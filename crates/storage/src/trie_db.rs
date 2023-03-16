use backend::TrieBackend;
use blake3_hasher::Blake3Hasher as H;
use rt_evm_model::types::MerkleRoot;
use ruc::*;
use serde::{Deserialize, Serialize};
use sp_trie::{
    cache::{LocalTrieCache, TrieCache},
    trie_types::{
        TrieDB, TrieDBMutBuilderV1 as TrieDBMutBuilder, TrieDBMutV1 as TrieDBMut,
    },
    LayoutV1, Trie, TrieDBBuilder, TrieHash, TrieMut,
};
use std::mem;
use vsdb::basic::mapx_ord_rawkey::MapxOrdRawKey;

#[derive(Default, Serialize, Deserialize)]
pub struct MptStore {
    // backend key ==> backend instance
    //
    // the backend key
    // - for the world state MPT, it is `[0]`
    // - for the storage MPT, it is the bytes of a H160 address
    meta: MapxOrdRawKey<TrieBackend>,
}

impl MptStore {
    pub fn new() -> Self {
        Self {
            meta: MapxOrdRawKey::new(),
        }
    }

    pub fn trie_create<'a>(
        &self,
        backend_key: &'a [u8],
        cache_size: usize,
    ) -> Result<MptOnce<'a>> {
        let backend = MptStore::new_backend(cache_size);
        self.put_backend(backend_key, &backend).c(d!())?;

        let backend = Box::into_raw(Box::new(backend));
        unsafe {
            Ok(MptOnce {
                mpt: MptMut::new(&mut *backend),
                backend: Box::from_raw(backend),
            })
        }
    }

    pub fn trie_restore<'a>(
        &self,
        backend_key: &'a [u8],
        root: MerkleRoot,
    ) -> Result<MptOnce<'a>> {
        let backend = self.get_backend(backend_key).c(d!("backend not found"))?;

        let backend = Box::into_raw(Box::new(backend));
        unsafe {
            Ok(MptOnce {
                mpt: MptMut::from_existing(&mut *backend, root),
                backend: Box::from_raw(backend),
            })
        }
    }

    fn get_backend(&self, backend_key: &[u8]) -> Option<TrieBackend> {
        self.meta.get(backend_key)
    }

    fn put_backend(&self, backend_key: &[u8], backend: &TrieBackend) -> Result<()> {
        if self.meta.contains_key(backend_key) {
            return Err(eg!("backend key already exists"));
        }
        unsafe { self.meta.shadow() }.insert(backend_key, backend);
        Ok(())
    }

    fn new_backend(cache_size: usize) -> TrieBackend {
        TrieBackend::new(cache_size)
    }
}

///
/// # NOTE
///
/// The referenced field **MUST** be placed after the field that references it,
/// this is to ensure that the `drop`s can be executed in the correct order,
/// so that UB will not occur
pub struct MptOnce<'a> {
    mpt: MptMut<'a>,

    // self-reference
    #[allow(dead_code)]
    backend: Box<TrieBackend>,
}

impl<'a> MptOnce<'a> {
    pub fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>> {
        self.mpt.get(key).c(d!())
    }

    pub fn contains(&self, key: &[u8]) -> Result<bool> {
        self.mpt.contains(key).c(d!())
    }

    pub fn insert(&mut self, key: &[u8], value: &[u8]) -> Result<()> {
        self.mpt.insert(key, value).c(d!()).map(|_| ())
    }

    pub fn remove(&mut self, key: &[u8]) -> Result<()> {
        self.mpt.remove(key).c(d!()).map(|_| ())
    }

    pub fn commit(&mut self) -> MerkleRoot {
        self.mpt.commit()
    }
}

///
/// # NOTE
///
/// The referenced field **MUST** be placed after the field that references it,
/// this is to ensure that the `drop`s can be executed in the correct order,
/// so that UB will not occur
pub struct MptMut<'a> {
    trie: TrieDBMut<'a, H>,

    // self-reference
    #[allow(dead_code)]
    cache: Box<TrieCache<'a, H>>,

    // self-reference
    #[allow(dead_code)]
    local_cache: Box<LocalTrieCache<H>>,

    // self-reference
    #[allow(dead_code)]
    root: Box<TrieHash<LayoutV1<H>>>,
}

impl Drop for MptMut<'_> {
    fn drop(&mut self) {
        let tmp = self as *mut Self;
        let mut tmp = unsafe { &mut *tmp }.local_cache.as_trie_db_mut_cache();
        mem::swap(&mut tmp, &mut *self.cache);
        tmp.merge_into(&self.local_cache, *self.root);
    }
}

impl<'a> MptMut<'a> {
    // keep private !!
    pub fn new(backend: &'a mut TrieBackend) -> Self {
        let local_cache = Box::into_raw(Box::new(backend.get_cache_hdr().local_cache()));
        let cache =
            Box::into_raw(Box::new(unsafe { &*local_cache }.as_trie_db_mut_cache()));

        let root_buf = Box::into_raw(Box::default());
        let trie = TrieDBMutBuilder::new(backend, unsafe { &mut *root_buf })
            .with_cache(unsafe { &mut *cache })
            .build();

        unsafe {
            Self {
                root: Box::from_raw(root_buf),
                local_cache: Box::from_raw(local_cache),
                cache: Box::from_raw(cache),
                trie,
            }
        }
    }

    pub fn from_existing(backend: &'a mut TrieBackend, root: MerkleRoot) -> Self {
        let root = Box::into_raw(Box::new(root.to_fixed_bytes()));
        let local_cache = Box::into_raw(Box::new(backend.get_cache_hdr().local_cache()));
        let cache =
            Box::into_raw(Box::new(unsafe { &*local_cache }.as_trie_db_mut_cache()));

        let trie = TrieDBMutBuilder::from_existing(backend, unsafe { &mut *root })
            .with_cache(unsafe { &mut *cache })
            .build();

        unsafe {
            Self {
                root: Box::from_raw(root),
                local_cache: Box::from_raw(local_cache),
                cache: Box::from_raw(cache),
                trie,
            }
        }
    }

    pub fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>> {
        self.trie.get(key).c(d!())
    }

    pub fn contains(&self, key: &[u8]) -> Result<bool> {
        self.trie.contains(key).c(d!())
    }

    pub fn insert(&mut self, key: &[u8], value: &[u8]) -> Result<()> {
        self.trie.insert(key, value).c(d!()).map(|_| ())
    }

    pub fn remove(&mut self, key: &[u8]) -> Result<()> {
        self.trie.remove(key).c(d!()).map(|_| ())
    }

    pub fn commit(&mut self) -> MerkleRoot {
        self.trie.root().into()
    }
}

///
/// # NOTE
///
/// The referenced field **MUST** be placed after the field that references it,
/// this is to ensure that the `drop`s can be executed in the correct order,
/// so that UB will not occur
pub struct MptRo<'a> {
    trie: TrieDB<'a, 'a, H>,

    // self-reference
    #[allow(dead_code)]
    cache: Box<TrieCache<'a, H>>,

    // self-reference
    #[allow(dead_code)]
    local_cache: Box<LocalTrieCache<H>>,

    // self-reference
    #[allow(dead_code)]
    root: Box<TrieHash<LayoutV1<H>>>,
}

impl<'a> MptRo<'a> {
    pub fn from_existing(backend: &'a TrieBackend, root: MerkleRoot) -> Self {
        let root = root.to_fixed_bytes();
        let local_cache = Box::into_raw(Box::new(backend.get_cache_hdr().local_cache()));
        let cache =
            Box::into_raw(Box::new(unsafe { &*local_cache }.as_trie_db_cache(root)));

        let root = Box::into_raw(Box::new(root));
        let trie = TrieDBBuilder::new(backend, unsafe { &*root })
            .with_cache(unsafe { &mut *cache })
            .build();

        unsafe {
            Self {
                root: Box::from_raw(root),
                local_cache: Box::from_raw(local_cache),
                cache: Box::from_raw(cache),
                trie,
            }
        }
    }

    pub fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>> {
        self.trie.get(key).c(d!())
    }

    pub fn contains(&self, key: &[u8]) -> Result<bool> {
        self.trie.contains(key).c(d!())
    }

    pub fn root(&mut self) -> MerkleRoot {
        self.trie.root().into()
    }
}

mod backend {
    use hash_db::{AsHashDB, HashDB, HashDBRef, Hasher as KeyHasher, Prefix};
    use ruc::*;
    use serde::{Deserialize, Serialize};
    use sp_trie::cache::{CacheSize, SharedTrieCache};
    use vsdb::{basic::mapx_ord_rawkey::MapxOrdRawKey as Map, RawBytes, ValueEnDe};

    const GB: usize = 1024 * 1024 * 1024;
    const DEFAULT_SIZE: CacheSize = CacheSize::new(GB);

    pub type TrieBackend = VsBackend<blake3_hasher::Blake3Hasher, Vec<u8>>;
    type SharedCache = SharedTrieCache<blake3_hasher::Blake3Hasher>;

    pub trait TrieVar: AsRef<[u8]> + for<'a> From<&'a [u8]> {}

    impl<T> TrieVar for T where T: AsRef<[u8]> + for<'a> From<&'a [u8]> {}

    // NOTE: make it `!Clone`
    pub struct VsBackend<H, T>
    where
        H: KeyHasher,
        T: TrieVar,
    {
        data: Map<Value<T>>,
        cache: SharedCache,
        cache_size: usize,

        hashed_null_key: H::Out,
        original_null_key: Vec<u8>,
        null_node_data: T,
    }

    impl<H, T> VsBackend<H, T>
    where
        H: KeyHasher,
        T: TrieVar,
    {
        /// Create a new `VsBackend` from the default null key/data
        pub fn new(cache_size: usize) -> Self {
            Self::from_null_node(&[0u8][..], (&[0u8][..]).into(), cache_size)
        }

        /// Create a new `VsBackend` from a given null key/data
        fn from_null_node(
            null_key: &[u8],
            null_node_data: T,
            cache_size: usize,
        ) -> Self {
            let cache = if 0 == cache_size {
                SharedCache::new(DEFAULT_SIZE)
            } else {
                SharedCache::new(CacheSize::new(cache_size))
            };

            VsBackend {
                data: Map::new(),
                cache,
                cache_size,

                hashed_null_key: H::hash(null_key),
                original_null_key: null_key.to_vec(),
                null_node_data,
            }
        }

        pub fn get_cache_hdr(&self) -> &SharedCache {
            &self.cache
        }
    }

    impl<H, T> HashDB<H, T> for VsBackend<H, T>
    where
        H: KeyHasher,
        T: TrieVar + Clone + Sync + Send + PartialEq + Default,
    {
        fn get(&self, key: &<H as KeyHasher>::Out, prefix: Prefix) -> Option<T> {
            if key == &self.hashed_null_key {
                return Some(self.null_node_data.clone());
            }
            let key = prefixed_key::<H>(key, prefix);
            match self.data.get(key) {
                Some(Value { v, rc }) if rc > 0 => Some(v),
                _ => None,
            }
        }

        fn contains(&self, key: &<H as KeyHasher>::Out, prefix: Prefix) -> bool {
            if key == &self.hashed_null_key {
                return true;
            }
            let key = prefixed_key::<H>(key, prefix);
            matches!(self.data.get(key), Some(Value { v: _, rc }) if rc > 0)
        }

        fn emplace(&mut self, key: <H as KeyHasher>::Out, prefix: Prefix, value: T) {
            if value == self.null_node_data {
                return;
            }

            let key = prefixed_key::<H>(&key, prefix);

            if let Some(mut old) = self.data.get_mut(&key) {
                if old.rc == 0 {
                    old.v = value;
                    old.rc = 1;
                } else {
                    old.rc += 1;
                }
                return;
            }

            self.data.insert(key, &Value { v: value, rc: 1 });
        }

        fn insert(&mut self, prefix: Prefix, value: &[u8]) -> <H as KeyHasher>::Out {
            let v = T::from(value);
            if v == self.null_node_data {
                return self.hashed_null_key;
            }

            let key = H::hash(value);
            HashDB::emplace(self, key, prefix, v);
            key
        }

        fn remove(&mut self, key: &<H as KeyHasher>::Out, prefix: Prefix) {
            if key == &self.hashed_null_key {
                return;
            }

            let key = prefixed_key::<H>(key, prefix);
            if let Some(mut v) = self.data.get_mut(&key) {
                if v.rc > 0 {
                    v.rc -= 1;
                }
            }
        }
    }

    impl<H, T> HashDBRef<H, T> for VsBackend<H, T>
    where
        H: KeyHasher,
        T: TrieVar + Clone + Sync + Send + Default + PartialEq,
    {
        fn get(&self, key: &<H as KeyHasher>::Out, prefix: Prefix) -> Option<T> {
            HashDB::get(self, key, prefix)
        }
        fn contains(&self, key: &<H as KeyHasher>::Out, prefix: Prefix) -> bool {
            HashDB::contains(self, key, prefix)
        }
    }

    impl<H, T> AsHashDB<H, T> for VsBackend<H, T>
    where
        H: KeyHasher,
        T: TrieVar + Clone + Sync + Send + Default + PartialEq,
    {
        fn as_hash_db(&self) -> &dyn HashDB<H, T> {
            self
        }
        fn as_hash_db_mut(&mut self) -> &mut dyn HashDB<H, T> {
            self
        }
    }

    // Derive a database key from hash value of the node (key) and the node prefix.
    fn prefixed_key<H: KeyHasher>(key: &H::Out, prefix: Prefix) -> Vec<u8> {
        let mut prefixed_key =
            Vec::with_capacity(key.as_ref().len() + prefix.0.len() + 1);
        prefixed_key.extend_from_slice(prefix.0);
        if let Some(last) = prefix.1 {
            prefixed_key.push(last);
        }
        prefixed_key.extend_from_slice(key.as_ref());
        prefixed_key
    }

    struct Value<T> {
        v: T,
        rc: i32,
    }

    const RC_BYTES_NUM: usize = i32::to_be_bytes(0).len();

    impl<T> ValueEnDe for Value<T>
    where
        T: TrieVar,
    {
        fn try_encode(&self) -> Result<RawBytes> {
            Ok(self.encode())
        }

        fn encode(&self) -> RawBytes {
            let vbytes = self.v.as_ref();
            let mut r = Vec::with_capacity(RC_BYTES_NUM + vbytes.len());
            r.extend_from_slice(&i32::to_be_bytes(self.rc));
            r.extend_from_slice(vbytes);
            r
        }

        fn decode(bytes: &[u8]) -> Result<Self> {
            if bytes.len() < RC_BYTES_NUM {
                return Err(eg!("invalid length"));
            }
            let rcbytes =
                <[u8; RC_BYTES_NUM]>::try_from(&bytes[..RC_BYTES_NUM]).unwrap();
            Ok(Self {
                v: T::from(&bytes[RC_BYTES_NUM..]),
                rc: i32::from_be_bytes(rcbytes),
            })
        }
    }

    #[derive(Serialize, Deserialize)]
    #[serde(bound = "")]
    struct VsBackendSerde<T>
    where
        T: TrieVar,
    {
        data: Map<Value<T>>,
        cache_size: usize,

        original_null_key: Vec<u8>,
        null_node_data: Vec<u8>,
    }

    impl<H, T> From<VsBackendSerde<T>> for VsBackend<H, T>
    where
        H: KeyHasher,
        T: TrieVar,
    {
        fn from(vbs: VsBackendSerde<T>) -> Self {
            Self {
                data: vbs.data,
                cache: SharedCache::new(CacheSize::new(vbs.cache_size)),
                cache_size: vbs.cache_size,

                hashed_null_key: H::hash(&vbs.original_null_key),
                original_null_key: vbs.original_null_key,
                null_node_data: T::from(&vbs.null_node_data),
            }
        }
    }

    impl<H, T> From<&VsBackend<H, T>> for VsBackendSerde<T>
    where
        H: KeyHasher,
        T: TrieVar,
    {
        fn from(vb: &VsBackend<H, T>) -> Self {
            Self {
                data: unsafe { vb.data.shadow() },
                cache_size: vb.cache_size,

                original_null_key: vb.original_null_key.clone(),
                null_node_data: vb.null_node_data.as_ref().to_vec(),
            }
        }
    }

    impl<H, T> ValueEnDe for VsBackend<H, T>
    where
        H: KeyHasher,
        T: TrieVar,
    {
        fn try_encode(&self) -> Result<RawBytes> {
            bcs::to_bytes(&VsBackendSerde::from(self)).c(d!())
        }

        fn encode(&self) -> RawBytes {
            pnk!(self.try_encode())
        }

        fn decode(bytes: &[u8]) -> Result<Self> {
            bcs::from_bytes::<VsBackendSerde<T>>(bytes)
                .c(d!())
                .map(Self::from)
        }
    }
}
