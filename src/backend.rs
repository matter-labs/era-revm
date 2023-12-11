use era_test_node::fork::{ForkDetails, ForkStorage};
use era_test_node::http_fork_source::HttpForkSource;
use era_test_node::system_contracts;
use ethabi::ethereum_types::H256;
use multivm::vm_refunds_enhancement::{AppDataFrameManagerWithHistory, HistoryDisabled};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use zksync_state::{InMemoryStorage, ReadStorage, StoragePtr, StorageView, WriteStorage};
use zksync_types::{StorageKey, StorageLogQuery, StorageValue};

#[derive(Debug, Clone)]
pub struct ForkedStorageOracle<S> {
    pub frames_stack: AppDataFrameManagerWithHistory<Box<StorageLogQuery>, HistoryDisabled>,
    pub storage: StoragePtr<S>,
}

#[derive(Debug)]
pub struct ForkedStorage {
    oracle: ForkedStorageOracle<StorageView<ForkStorage<HttpForkSource>>>,
    source: ForkDetails<HttpForkSource>,
}

#[derive(Debug)]
pub struct Backend {
    forks: HashMap<usize, ForkedStorage>,
    in_memory_storage: ForkedStorageOracle<StorageView<InMemoryStorage>>,
    active_fork: Option<usize>,
}

impl Backend {
    pub fn new() -> Self {
        Self {
            forks: HashMap::new(),
            in_memory_storage: ForkedStorageOracle {
                frames_stack: Default::default(),
                storage: Rc::new(RefCell::new(StorageView::new(InMemoryStorage::default()))),
            },
            active_fork: None,
        }
    }

    pub fn activate_fork(&mut self, fork_id: usize) -> Option<&ForkedStorage> {
        self.active_fork = Some(fork_id);
        self.forks.get(&fork_id)
    }

    pub fn create_fork(
        &mut self,
        source: ForkDetails<HttpForkSource>,
        opts: system_contracts::Options,
    ) -> usize {
        let storage = ForkedStorage {
            oracle: ForkedStorageOracle {
                frames_stack: Default::default(),
                storage: Rc::new(RefCell::new(StorageView::new(ForkStorage::new(
                    Some(source.clone()),
                    &opts,
                )))),
            },
            source,
        };

        let fork_id = self.forks.len();
        self.forks.insert(fork_id, storage);
        fork_id
    }

    pub fn deactivate_fork(&mut self) {
        self.active_fork = None;
    }
}

macro_rules! exec_function {
    ($self:ident.$function:ident($($params:tt)*)) => {
        match $self.active_fork {
            None => {
                $self.in_memory_storage.storage.borrow_mut().$function($($params)*)
            }
            Some(i) => {
                $self.forks.get(&i).unwrap().oracle.storage.borrow_mut().$function($($params)*)
            }
        }
    };
}

impl ReadStorage for Backend {
    fn read_value(&mut self, key: &StorageKey) -> StorageValue {
        exec_function!(self.read_value(key))
    }

    fn is_write_initial(&mut self, key: &StorageKey) -> bool {
        exec_function!(self.is_write_initial(key))
    }

    fn load_factory_dep(&mut self, hash: H256) -> Option<Vec<u8>> {
        exec_function!(self.load_factory_dep(hash))
    }

    fn get_enumeration_index(&mut self, key: &StorageKey) -> Option<u64> {
        exec_function!(self.get_enumeration_index(key))
    }
}

impl WriteStorage for Backend {
    fn set_value(&mut self, key: StorageKey, value: StorageValue) -> StorageValue {
        exec_function!(self.set_value(key, value))
    }

    fn modified_storage_keys(&self) -> &HashMap<StorageKey, StorageValue> {
        todo!()
    }

    fn missed_storage_invocations(&self) -> usize {
        0
    }
}
