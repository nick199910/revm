use revm_primitives::Bytes;

use crate::primitives::{hash_map::Entry, Bytecode, HashMap, U256};
use crate::InstructionResult::Continue;
use crate::{
    primitives::{Address, Env, Log, B256, KECCAK_EMPTY},
    Host, SStoreResult, SelfDestructResult,
};
use crate::{Gas, InstructionResult, InterpreterResult};
use std::sync::Arc;
use std::vec::Vec;

use super::LoadAccountResult;

/// A dummy [Host] implementation.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DummyHost {
    pub env: Env,
    pub storage: HashMap<U256, U256>,
    pub transient_storage: HashMap<U256, U256>,
    pub log: Vec<Log>,
}

impl DummyHost {
    /// Create a new dummy host with the given [`Env`].
    #[inline]
    pub fn new(env: Env) -> Self {
        Self {
            env,
            ..Default::default()
        }
    }

    /// Clears the storage and logs of the dummy host.
    #[inline]
    pub fn clear(&mut self) {
        self.storage.clear();
        self.log.clear();
    }
}

impl Host<u32> for DummyHost {
    #[inline]
    fn env(&self) -> &Env {
        &self.env
    }

    #[inline]
    fn env_mut(&mut self) -> &mut Env {
        &mut self.env
    }

    #[inline]
    fn load_account(&mut self, _address: Address) -> Option<LoadAccountResult> {
        Some(LoadAccountResult::default())
    }

    #[inline]
    fn block_hash(&mut self, _number: U256) -> Option<B256> {
        Some(B256::ZERO)
    }

    #[inline]
    fn balance(&mut self, _address: Address) -> Option<(U256, bool)> {
        Some((U256::ZERO, false))
    }

    #[inline]
    fn code(&mut self, _address: Address) -> Option<(Arc<Bytecode>, bool)> {
        Some((Arc::new(Bytecode::default()), false))
    }

    #[inline]
    fn code_hash(&mut self, __address: Address) -> Option<(B256, bool)> {
        Some((KECCAK_EMPTY, false))
    }

    #[inline]
    fn sload(&mut self, __address: Address, index: U256) -> Option<(U256, bool)> {
        match self.storage.entry(index) {
            Entry::Occupied(entry) => Some((*entry.get(), false)),
            Entry::Vacant(entry) => {
                entry.insert(U256::ZERO);
                Some((U256::ZERO, true))
            }
        }
    }

    #[inline]
    fn sstore(&mut self, _address: Address, index: U256, value: U256) -> Option<SStoreResult> {
        let (present, is_cold) = match self.storage.entry(index) {
            Entry::Occupied(mut entry) => (entry.insert(value), false),
            Entry::Vacant(entry) => {
                entry.insert(value);
                (U256::ZERO, true)
            }
        };

        Some(SStoreResult {
            original_value: U256::ZERO,
            present_value: present,
            new_value: value,
            is_cold,
        })
    }

    #[inline]
    fn tload(&mut self, _address: Address, index: U256) -> U256 {
        self.transient_storage
            .get(&index)
            .copied()
            .unwrap_or_default()
    }

    #[inline]
    fn tstore(&mut self, _address: Address, index: U256, value: U256) {
        self.transient_storage.insert(index, value);
    }

    #[inline]
    fn log(&mut self, log: Log) {
        self.log.push(log)
    }

    #[inline]
    fn selfdestruct(&mut self, _address: Address, _target: Address) -> Option<SelfDestructResult> {
        panic!("Selfdestruct is not supported for this host")
    }

    fn step(
        &mut self,
        _interpreter: &mut crate::Interpreter,
        _additional_data: &mut u32,
    ) -> InstructionResult {
        InstructionResult::Continue
    }

    fn create(
        &mut self,
        _inputs: &mut crate::CreateInputs,
        _additional_data: &mut u32,
    ) -> crate::CreateOutcome {
        crate::CreateOutcome {
            result: InterpreterResult {
                result: InstructionResult::Continue,
                output: Bytes::new(),
                gas: Gas::new(1000000),
            },
            address: Some(Address::default()),
        }
    }

    fn call(
        &mut self,
        _input: &mut crate::CallInputs,
        _interp: &mut crate::Interpreter,
        _output_info: (usize, usize),
        _additional_data: &mut u32,
    ) -> crate::CallOutcome {
        crate::CallOutcome {
            result: InterpreterResult {
                result: InstructionResult::Continue,
                output: Bytes::new(),
                gas: Gas::new(1000000),
            },
            memory_offset: (0..32),
        }
    }
}
