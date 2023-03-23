#![deny(warnings)]
#![cfg_attr(feature = "benchmark", allow(warnings))]

use parking_lot::{Mutex, RwLock};
use rt_evm_model::{
    codec::ProtocolCodec,
    traits::{BlockStorage, TxStorage},
    types::{
        Account, BlockNumber, Hash, SignedTransaction as SignedTx, H160,
        MAX_BLOCK_GAS_LIMIT, MIN_TRANSACTION_GAS_LIMIT, NIL_HASH, U256,
        WORLD_STATE_META_KEY,
    },
};
use rt_evm_storage::{MptStore, Storage};
use ruc::*;
use serde::{Deserialize, Serialize};
use std::{
    cmp::Ordering,
    collections::{BTreeMap, HashMap},
    mem,
    sync::{
        atomic::{AtomicBool, AtomicU64, Ordering as AtoOrd},
        Arc,
    },
    thread,
};

// Decrease from u64::MAX
static TX_INDEXER: AtomicU64 = AtomicU64::new(u64::MAX);

pub type EvmTxChecker = fn(&SignedTx, bool) -> Result<()>;
pub type SysTxChecker = fn(&SysTx) -> Result<()>;

#[derive(Clone)]
pub struct Mempool {
    // If number of tx exceed the capacity, deny new transactions
    //
    // NOTE: lock order number is 1
    txs_evm: Arc<Mutex<BTreeMap<u64, SignedTx>>>,
    txs_sys: Arc<Mutex<BTreeMap<u64, SysTx>>>,

    // Record transactions that need to be broadcasted
    broadcast_queue_evm: Arc<Mutex<Vec<SignedTx>>>,
    broadcast_queue_sys: Arc<Mutex<Vec<SysTx>>>,

    // Pending transactions of each account
    //
    // NOTE: lock order number is 0
    address_pending_cnter: Arc<RwLock<HashMap<H160, HashMap<Hash, u64>>>>,

    // key: <timestamp of tx> % <lifetime limitation>
    // value: the index of tx in `txs`
    //
    // discard_guard = tx_lifetime_fields.split_off(ts!() % <lifetime limitation> - 2)
    //
    // min_tx_index_to_discard = discard_gurad.pop_last().1
    // txs_to_discard = txs.split_off(min_tx_index_to_discard)
    //
    // decrease pending cnter based on txs_to_discard
    //
    tx_lifetime_fields: Arc<Mutex<BTreeMap<u64, u64>>>,

    // If `true`, the background thread will exit itself.
    stop_cleaner: Arc<AtomicBool>,

    cfg: MempoolCfg,
}

impl Mempool {
    pub fn new(
        capacity: u64,
        tx_lifetime_in_secs: u64,

        tx_gas_cap: Option<u64>,
        trie_db: Arc<MptStore>,
        storage: Arc<Storage>,
        tx_checker_evm: Option<EvmTxChecker>,
        tx_checker_sys: Option<SysTxChecker>,
    ) -> Arc<Self> {
        let address_pending_cnter = Arc::new(RwLock::new(map! {}));

        let ret = Self {
            txs_evm: Arc::new(Mutex::new(BTreeMap::new())),
            txs_sys: Arc::new(Mutex::new(BTreeMap::new())),
            broadcast_queue_evm: Arc::new(Mutex::new(vec![])),
            broadcast_queue_sys: Arc::new(Mutex::new(vec![])),
            tx_lifetime_fields: Arc::new(Mutex::new(BTreeMap::new())),
            address_pending_cnter,
            stop_cleaner: Arc::new(AtomicBool::new(false)),
            cfg: MempoolCfg {
                capacity,
                tx_lifetime_in_secs,
                tx_gas_cap: tx_gas_cap.unwrap_or(MAX_BLOCK_GAS_LIMIT).into(),
                trie_db,
                storage,
                tx_checker_evm,
                tx_checker_sys,
            },
        };
        let ret = Arc::new(ret);

        let hdr_ret = Arc::clone(&ret);
        thread::spawn(move || {
            loop {
                sleep_ms!(tx_lifetime_in_secs * 1000);

                if hdr_ret.stop_cleaner.load(AtoOrd::Relaxed) {
                    return;
                }

                let mut ts_guard = ts!() % tx_lifetime_in_secs;
                alt!(3 > ts_guard, continue);
                ts_guard -= 2;

                let mut to_discard =
                    if let Some(mut tlf) = hdr_ret.tx_lifetime_fields.try_lock() {
                        let mut to_keep = tlf.split_off(&ts_guard);
                        mem::swap(&mut to_keep, &mut tlf);
                        to_keep // now is 'to_discard'
                    } else {
                        continue;
                    };

                let idx_gurad = if let Some((_, idx)) = to_discard.pop_last() {
                    idx
                } else {
                    continue;
                };

                // Deal with evm transactions,
                // we call `collect` and then `iter` again to avoid `dead lock`
                let to_del = hdr_ret
                    .txs_evm
                    .lock()
                    .split_off(&idx_gurad)
                    .into_values()
                    .collect::<Vec<_>>();
                let mut pending_cnter = hdr_ret.address_pending_cnter.write();
                to_del.iter().for_each(|tx| {
                    if let Some(i) = pending_cnter.get_mut(&tx.sender) {
                        i.remove(&tx.transaction.hash);
                    }
                });

                // Deal with sys transactions,
                let to_del = hdr_ret
                    .txs_sys
                    .lock()
                    .split_off(&idx_gurad)
                    .into_values()
                    .collect::<Vec<_>>();
                let mut pending_cnter = hdr_ret.address_pending_cnter.write();
                to_del.iter().for_each(|tx| {
                    if let Some(i) = pending_cnter.get_mut(&tx.sender) {
                        i.remove(&tx.hash);
                    }
                });
            }
        });

        ret
    }

    // Add a new evm transaction to mempool
    #[cfg_attr(feature = "benchmark", allow(dead_code))]
    pub fn tx_insert_evm(&self, tx: SignedTx, signature_checked: bool) -> Result<()> {
        if self.tx_pending_cnt(None) > self.cfg.capacity {
            return Err(eg!("Mempool is full"));
        }

        if self
            .address_pending_cnter
            .read()
            .get(&tx.sender)
            .and_then(|m| m.get(&tx.transaction.hash))
            .is_some()
        {
            return Err(eg!("Already cached in mempool"));
        }

        #[cfg(not(feature = "benchmark"))]
        if let Some(checker) = self.cfg.tx_checker_evm.as_ref() {
            checker(&tx, signature_checked).c(d!())?;
        } else {
            self.tx_check_evm(&tx, signature_checked).c(d!())?;
        }

        self.broadcast_queue_evm.lock().push(tx.clone());

        let idx = TX_INDEXER.fetch_sub(1, AtoOrd::Relaxed);

        self.address_pending_cnter
            .write()
            .entry(tx.sender)
            .or_insert(map! {})
            .insert(tx.transaction.hash, idx);

        self.tx_lifetime_fields
            .lock()
            .insert(ts!() % self.cfg.tx_lifetime_in_secs, idx);

        self.txs_evm.lock().insert(idx, tx);

        Ok(())
    }

    // Add a new sys transaction to mempool
    #[cfg_attr(feature = "benchmark", allow(dead_code))]
    pub fn tx_insert_sys(&self, tx: SysTx) -> Result<()> {
        if self.tx_pending_cnt(None) > self.cfg.capacity {
            return Err(eg!("Mempool is full"));
        }

        if self
            .address_pending_cnter
            .read()
            .get(&tx.sender)
            .and_then(|m| m.get(&tx.hash))
            .is_some()
        {
            return Err(eg!("Already cached in mempool"));
        }

        #[cfg(not(feature = "benchmark"))]
        if let Some(checker) = self.cfg.tx_checker_sys.as_ref() {
            checker(&tx).c(d!())?;
        }

        self.broadcast_queue_sys.lock().push(tx.clone());

        let idx = TX_INDEXER.fetch_sub(1, AtoOrd::Relaxed);

        self.address_pending_cnter
            .write()
            .entry(tx.sender)
            .or_insert(map! {})
            .insert(tx.hash, idx);

        self.tx_lifetime_fields
            .lock()
            .insert(ts!() % self.cfg.tx_lifetime_in_secs, idx);

        self.txs_sys.lock().insert(idx, tx);

        Ok(())
    }

    // Transactions that **maybe** have not been confirmed
    pub fn tx_pending_cnt(&self, addr: Option<H160>) -> u64 {
        if let Some(addr) = addr {
            self.address_pending_cnter
                .read()
                .get(&addr)
                .map(|i| i.len() as u64)
                .unwrap_or_default()
        } else {
            (self.txs_evm.lock().len() + self.txs_sys.lock().len()) as u64
        }
    }

    // Broadcast evm transactions to other nodes ?
    pub fn tx_take_broadcast_evm(&self) -> Vec<SignedTx> {
        mem::take(&mut *self.broadcast_queue_evm.lock())
    }

    // Broadcast sys transactions to other nodes ?
    pub fn tx_take_broadcast_sys(&self) -> Vec<SysTx> {
        mem::take(&mut *self.broadcast_queue_sys.lock())
    }

    // Package transactions for proposing a new block ?
    pub fn tx_take_propose_evm(&self, cnt: usize) -> Vec<SignedTx> {
        let mut ret = self
            .txs_evm
            .lock()
            .iter()
            .rev()
            .take(cnt)
            .map(|(_, tx)| tx.clone())
            .collect::<Vec<_>>();

        ret.sort_unstable_by(|a, b| {
            let price_cmp = b
                .transaction
                .unsigned
                .gas_price()
                .cmp(&a.transaction.unsigned.gas_price());
            if matches!(price_cmp, Ordering::Equal) {
                a.transaction
                    .unsigned
                    .nonce()
                    .cmp(b.transaction.unsigned.nonce())
            } else {
                price_cmp
            }
        });

        ret
    }

    // Package transactions for proposing a new block ?
    pub fn tx_take_propose_sys(&self, cnt: usize) -> Vec<SysTx> {
        self.txs_sys
            .lock()
            .iter()
            .rev()
            .take(cnt)
            .map(|(_, tx)| tx.clone())
            .collect()
    }

    // Remove transactions after they have been confirmed ?
    pub fn tx_cleanup(&self, to_del: &[(H160, Hash)]) {
        let mut pending_cnter = self.address_pending_cnter.write();
        let mut txs_evm = self.txs_evm.lock();
        let mut txs_sys = self.txs_sys.lock();
        to_del.iter().for_each(|(sender, txhash)| {
            if let Some(i) = pending_cnter.get_mut(sender) {
                if let Some(idx) = i.remove(txhash) {
                    txs_evm.remove(&idx);
                    txs_sys.remove(&idx);
                }
            }
        });
    }

    // Pre-check the tx before execute it.
    pub fn tx_check_evm(&self, tx: &SignedTx, signature_checked: bool) -> Result<()> {
        let utx = &tx.transaction;

        let gas_price = utx.unsigned.gas_price();

        if gas_price == U256::zero() {
            return Err(eg!("The 'gas price' is zero"));
        }

        if gas_price >= U256::from(u64::MAX) {
            return Err(eg!("The 'gas price' exceeds the limition(u64::MAX)"));
        }

        let gas_limit = *utx.unsigned.gas_limit();

        if gas_limit < MIN_TRANSACTION_GAS_LIMIT.into() {
            return Err(eg!(
                "The 'gas limit' less than {}",
                MIN_TRANSACTION_GAS_LIMIT
            ));
        }

        if gas_limit > self.cfg.tx_gas_cap {
            return Err(eg!(
                "The 'gas limit' exceeds the gas capacity({})",
                self.cfg.tx_gas_cap,
            ));
        }

        utx.check_hash().c(d!())?;

        if !signature_checked && tx != &SignedTx::try_from(utx.clone()).c(d!())? {
            return Err(eg!("Signature verify failed"));
        }

        let acc = self.get_account(tx.sender, None).c(d!())?;

        if &acc.nonce > utx.unsigned.nonce() {
            return Err(eg!("Invalid nonce"));
        }

        if acc.balance < gas_price.saturating_mul(MIN_TRANSACTION_GAS_LIMIT.into()) {
            return Err(eg!("Insufficient balance to cover possible gas"));
        }

        if self
            .cfg
            .storage
            .get_tx_by_hash(&utx.hash)
            .c(d!())?
            .is_some()
        {
            return Err(eg!("Historical transaction detected"));
        }

        Ok(())
    }

    fn get_account(
        &self,
        address: H160,
        number: Option<BlockNumber>,
    ) -> Result<Account> {
        let header = if let Some(n) = number {
            self.cfg.storage.get_block_header(n).c(d!())?.c(d!())?
        } else {
            self.cfg.storage.get_latest_block_header().c(d!())?
        };

        let state = self
            .cfg
            .trie_db
            .trie_restore(&WORLD_STATE_META_KEY, header.state_root)
            .c(d!())?;

        match state.get(address.as_bytes()).c(d!())? {
            Some(bytes) => Account::decode(bytes).c(d!()),
            None => Ok(Account {
                nonce: U256::zero(),
                balance: U256::zero(),
                storage_root: NIL_HASH,
                code_hash: NIL_HASH,
            }),
        }
    }
}

#[derive(Clone)]
struct MempoolCfg {
    // Static fields,
    // set once, and then immutable forever ?
    capacity: u64,
    tx_lifetime_in_secs: u64,

    // fields for tx pre-check
    tx_gas_cap: U256,
    trie_db: Arc<MptStore>,
    storage: Arc<Storage>,

    tx_checker_evm: Option<EvmTxChecker>,
    tx_checker_sys: Option<SysTxChecker>,
}

// TODO
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SysTx {
    sender: H160,

    // hash of `raw_tx`
    hash: Hash,

    raw_tx: Vec<u8>,
}
