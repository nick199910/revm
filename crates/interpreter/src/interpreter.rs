pub mod analysis;
mod contract;
#[cfg(feature = "serde")]
pub mod serde;
mod shared_memory;
mod stack;
pub use contract::Contract;
pub use shared_memory::{next_multiple_of_32, SharedMemory, EMPTY_SHARED_MEMORY};
pub use stack::{Stack, STACK_LIMIT};
use std::sync::Arc;

use crate::{interpreter, EOFCreateOutcome};
use crate::{
    primitives::Bytes, push, push_b256, return_ok, return_revert, CallOutcome, CreateOutcome,
    FunctionStack, Gas, Host, InstructionResult, InterpreterAction,
};
use core::cmp::min;
use revm_primitives::{Bytecode, Eof, Spec, MAX_INSTRUCTION_SIZE, U256};
use std::borrow::ToOwned;

/// EVM bytecode interpreter.
#[derive(Debug, Clone)]
pub struct Interpreter {
    /// The current instruction pointer.
    pub instruction_pointer: *const u8,
    /// The gas state.
    pub gas: Gas,
    /// Contract information and invoking data
    pub contract: Contract,
    /// The execution control flag. If this is not set to `Continue`, the interpreter will stop
    /// execution.
    pub instruction_result: InstructionResult,
    /// Currently run Bytecode that instruction result will point to.
    /// Bytecode is owned by the contract.
    pub bytecode: Bytes,
    /// Whether we are Interpreting the Ethereum Object Format (EOF) bytecode.
    /// This is local field that is set from `contract.is_eof()`.
    pub is_eof: bool,
    /// Is init flag for eof create
    pub is_eof_init: bool,
    /// Shared memory.
    ///
    /// Note: This field is only set while running the interpreter loop.
    /// Otherwise it is taken and replaced with empty shared memory.
    pub shared_memory: SharedMemory,
    /// Stack.
    pub stack: Stack,
    /// EOF function stack.
    pub function_stack: FunctionStack,
    /// The return data buffer for internal calls.
    /// It has multi usage:
    ///
    /// * It contains the output bytes of call sub call.
    /// * When this interpreter finishes execution it contains the output bytes of this contract.
    pub return_data_buffer: Bytes,
    /// Whether the interpreter is in "staticcall" mode, meaning no state changes can happen.
    pub is_static: bool,
    /// Actions that the EVM should do.
    ///
    /// Set inside CALL or CREATE instructions and RETURN or REVERT instructions. Additionally those instructions will set
    /// InstructionResult to CallOrCreate/Return/Revert so we know the reason.
    pub next_action: InterpreterAction,
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new(Contract::default(), 0, false)
    }
}

/// The result of an interpreter operation.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(::serde::Serialize, ::serde::Deserialize))]
pub struct InterpreterResult {
    /// The result of the instruction execution.
    pub result: InstructionResult,
    /// The output of the instruction execution.
    pub output: Bytes,
    /// The gas usage information.
    pub gas: Gas,
}

impl Interpreter {
    /// Create new interpreter
    pub fn new(contract: Contract, gas_limit: u64, is_static: bool) -> Self {
        if !contract.bytecode.is_execution_ready() {
            panic!("Contract is not execution ready {:?}", contract.bytecode);
        }
        let is_eof = contract.bytecode.is_eof();
        let bytecode = contract.bytecode.bytecode_bytes();
        Self {
            instruction_pointer: bytecode.as_ptr(),
            bytecode,
            contract,
            gas: Gas::new(gas_limit),
            instruction_result: InstructionResult::Continue,
            function_stack: FunctionStack::default(),
            is_static,
            is_eof,
            is_eof_init: false,
            return_data_buffer: Bytes::new(),
            shared_memory: EMPTY_SHARED_MEMORY,
            stack: Stack::new(),
            next_action: InterpreterAction::None,
        }
    }

    /// Set set is_eof_init to true, this is used to enable `RETURNCONTRACT` opcode.
    #[inline]
    pub fn set_is_eof_init(&mut self) {
        self.is_eof_init = true;
    }

    #[inline]
    pub fn eof(&self) -> Option<&Eof> {
        self.contract.bytecode.eof()
    }

    /// Test related helper
    #[cfg(test)]
    pub fn new_bytecode(bytecode: Arc<Bytecode>) -> Self {
        Self::new(
            Contract::new(
                Bytes::new(),
                bytecode,
                None,
                crate::primitives::Address::default(),
                crate::primitives::Address::default(),
                U256::ZERO,
                crate::primitives::Address::default(),
            ),
            0,
            false,
        )
    }

    /// Load EOF code into interpreter. PC is assumed to be correctly set
    pub(crate) fn load_eof_code(&mut self, idx: usize, pc: usize) {
        // SAFETY: eof flag is true only if bytecode is Eof.
        let Bytecode::Eof(eof) = &*self.contract.bytecode else {
            panic!("Expected EOF bytecode")
        };
        let Some(code) = eof.body.code(idx) else {
            panic!("Code not found")
        };
        self.bytecode = code.clone();
        self.instruction_pointer = unsafe { self.bytecode.as_ptr().add(pc) };
    }

    /// Inserts the output of a `create` call into the interpreter.
    ///
    /// This function is used after a `create` call has been executed. It processes the outcome
    /// of that call and updates the state of the interpreter accordingly.
    ///
    /// # Arguments
    ///
    /// * `create_outcome` - A `CreateOutcome` struct containing the results of the `create` call.
    ///
    /// # Behavior
    ///
    /// The function updates the `return_data_buffer` with the data from `create_outcome`.
    /// Depending on the `InstructionResult` indicated by `create_outcome`, it performs one of the following:
    ///
    /// - `Ok`: Pushes the address from `create_outcome` to the stack, updates gas costs, and records any gas refunds.
    /// - `Revert`: Pushes `U256::ZERO` to the stack and updates gas costs.
    /// - `FatalExternalError`: Sets the `instruction_result` to `InstructionResult::FatalExternalError`.
    /// - `Default`: Pushes `U256::ZERO` to the stack.
    ///
    /// # Side Effects
    ///
    /// - Updates `return_data_buffer` with the data from `create_outcome`.
    /// - Modifies the stack by pushing values depending on the `InstructionResult`.
    /// - Updates gas costs and records refunds in the interpreter's `gas` field.
    /// - May alter `instruction_result` in case of external errors.
    pub fn insert_create_outcome(&mut self, create_outcome: CreateOutcome) {
        self.instruction_result = InstructionResult::Continue;

        let instruction_result = create_outcome.instruction_result();
        self.return_data_buffer = if instruction_result.is_revert() {
            // Save data to return data buffer if the create reverted
            create_outcome.output().to_owned()
        } else {
            // Otherwise clear it
            Bytes::new()
        };

        match instruction_result {
            return_ok!() => {
                let address = create_outcome.address;
                push_b256!(self, address.unwrap_or_default().into_word());
                self.gas.erase_cost(create_outcome.gas().remaining());
                self.gas.record_refund(create_outcome.gas().refunded());
            }
            return_revert!() => {
                push!(self, U256::ZERO);
                self.gas.erase_cost(create_outcome.gas().remaining());
            }
            InstructionResult::FatalExternalError => {
                panic!("Fatal external error in insert_create_outcome");
            }
            _ => {
                push!(self, U256::ZERO);
            }
        }
    }

    pub fn insert_eofcreate_outcome(&mut self, create_outcome: EOFCreateOutcome) {
        let instruction_result = create_outcome.instruction_result();

        self.return_data_buffer = if *instruction_result == InstructionResult::Revert {
            // Save data to return data buffer if the create reverted
            create_outcome.output().to_owned()
        } else {
            // Otherwise clear it. Note that RETURN opcode should abort.
            Bytes::new()
        };

        match instruction_result {
            InstructionResult::ReturnContract => {
                push_b256!(self, create_outcome.address.into_word());
                self.gas.erase_cost(create_outcome.gas().remaining());
                self.gas.record_refund(create_outcome.gas().refunded());
            }
            return_revert!() => {
                push!(self, U256::ZERO);
                self.gas.erase_cost(create_outcome.gas().remaining());
            }
            InstructionResult::FatalExternalError => {
                panic!("Fatal external error in insert_eofcreate_outcome");
            }
            _ => {
                push!(self, U256::ZERO);
            }
        }
    }

    /// Inserts the outcome of a call into the virtual machine's state.
    ///
    /// This function takes the result of a call, represented by `CallOutcome`,
    /// and updates the virtual machine's state accordingly. It involves updating
    /// the return data buffer, handling gas accounting, and setting the memory
    /// in shared storage based on the outcome of the call.
    ///
    /// # Arguments
    ///
    /// * `shared_memory` - A mutable reference to the shared memory used by the virtual machine.
    /// * `call_outcome` - The outcome of the call to be processed, containing details such as
    ///   instruction result, gas information, and output data.
    ///
    /// # Behavior
    ///
    /// The function first copies the output data from the call outcome to the virtual machine's
    /// return data buffer. It then checks the instruction result from the call outcome:
    ///
    /// - `return_ok!()`: Processes successful execution, refunds gas, and updates shared memory.
    /// - `return_revert!()`: Handles a revert by only updating the gas usage and shared memory.
    /// - `InstructionResult::FatalExternalError`: Sets the instruction result to a fatal external error.
    /// - Any other result: No specific action is taken.
    pub fn insert_call_outcome(
        &mut self,
        shared_memory: &mut SharedMemory,
        call_outcome: CallOutcome,
    ) {
        self.instruction_result = InstructionResult::Continue;
        self.return_data_buffer.clone_from(call_outcome.output());

        let out_offset = call_outcome.memory_start();
        let out_len = call_outcome.memory_length();

        let target_len = min(out_len, self.return_data_buffer.len());
        match call_outcome.instruction_result() {
            return_ok!() => {
                // return unspend gas.
                let remaining = call_outcome.gas().remaining();
                let refunded = call_outcome.gas().refunded();
                self.gas.erase_cost(remaining);
                self.gas.record_refund(refunded);
                shared_memory.set(out_offset, &self.return_data_buffer[..target_len]);
                push!(self, U256::from(1));
            }
            return_revert!() => {
                self.gas.erase_cost(call_outcome.gas().remaining());
                shared_memory.set(out_offset, &self.return_data_buffer[..target_len]);
                push!(self, U256::ZERO);
            }
            InstructionResult::FatalExternalError
            | InstructionResult::ControlLeak
            | InstructionResult::ArbitraryExternalCallAddressBounded(_, _, _)
            | InstructionResult::AddressUnboundedStaticCall => {
                panic!("Fatal external error in insert_call_outcome");
            }
            _ => {
                push!(self, U256::ZERO);
            }
        }
    }

    /// Returns the opcode at the current instruction pointer.
    #[inline]
    pub fn current_opcode(&self) -> u8 {
        unsafe { *self.instruction_pointer }
    }

    /// Returns a reference to the contract.
    #[inline]
    pub fn contract(&self) -> &Contract {
        &self.contract
    }

    /// Returns a reference to the interpreter's gas state.
    #[inline]
    pub fn gas(&self) -> &Gas {
        &self.gas
    }

    /// Returns a reference to the interpreter's stack.
    #[inline]
    pub fn stack(&self) -> &Stack {
        &self.stack
    }

    /// Returns the current program counter.
    #[inline]
    pub fn program_counter(&self) -> usize {
        // SAFETY: `instruction_pointer` should be at an offset from the start of the bytecode.
        // In practice this is always true unless a caller modifies the `instruction_pointer` field manually.
        unsafe { self.instruction_pointer.offset_from(self.bytecode.as_ptr()) as usize }
    }

    /// Executes the instruction at the current instruction pointer.
    ///
    /// Internally it will increment instruction pointer by one.
    #[inline]
    pub(crate) fn step<T, FN, H: Host<T> + ?Sized>(
        &mut self,
        instruction_table: &[FN; 256],
        host: &mut H,
        _additional: &mut T,
    ) where
        FN: Fn(&mut Interpreter, &mut H, &mut T),
    {
        // Get current opcode.
        let opcode = unsafe { *self.instruction_pointer };

        // SAFETY: In analysis we are doing padding of bytecode so that we are sure that last
        // byte instruction is STOP so we are safe to just increment program_counter bcs on last instruction
        // it will do noop and just stop execution of this contract
        self.instruction_pointer = unsafe { self.instruction_pointer.offset(1) };

        // execute instruction.
        (instruction_table[opcode as usize])(self, host, _additional)
    }

    /// Take memory and replace it with empty memory.
    pub fn take_memory(&mut self) -> SharedMemory {
        core::mem::replace(&mut self.shared_memory, EMPTY_SHARED_MEMORY)
    }

    /// Executes the interpreter until it returns or stops.
    pub fn run<T, FN, H: Host<T> + ?Sized>(
        &mut self,
        shared_memory: SharedMemory,
        host: &mut H,
        instruction_table: &[FN; 256],
        _additional: &mut T,
    ) -> InterpreterAction
    where
        FN: Fn(&mut Interpreter, &mut H, &mut T),
    {
        self.next_action = InterpreterAction::None;
        self.shared_memory = shared_memory;
        // main loop
        while self.instruction_result == InstructionResult::Continue {
            self.step(instruction_table, host, _additional);
        }

        // Return next action if it is some.
        if self.next_action.is_some() {
            return core::mem::take(&mut self.next_action);
        }
        // If not, return action without output as it is a halt.
        InterpreterAction::Return {
            result: InterpreterResult {
                result: self.instruction_result,
                // return empty bytecode
                output: Bytes::new(),
                gas: self.gas,
            },
        }
    }

    pub fn run_inspect<T, H: Host<T>, SPEC: Spec>(
        &mut self,
        host: &mut H,
        instruction_table: &[fn(&mut Interpreter, &mut H, &mut T); 256],
        additional_data: &mut T,
    ) -> InstructionResult {
        // let instruction_table: [fn(&mut Interpreter, &mut H); 256] =
        //     crate::opcode::make_instruction_table::<T, H, SPEC>();
        self.next_action = InterpreterAction::None;
        for _count in 0..MAX_INSTRUCTION_SIZE {
            if self.instruction_result == InstructionResult::Continue {
                host.step(self, additional_data);
                self.step(&instruction_table, host, additional_data);
                if self.next_action.is_return() {
                    self.return_data_buffer = self
                        .next_action
                        .clone()
                        .into_result_return()
                        .unwrap()
                        .output
                }
            } else {
                println!("{:?}", self.instruction_result);
                break;
            }
        }

        self.instruction_result
    }
}

impl InterpreterResult {
    /// Returns whether the instruction result is a success.
    #[inline]
    pub const fn is_ok(&self) -> bool {
        self.result.is_ok()
    }

    /// Returns whether the instruction result is a revert.
    #[inline]
    pub const fn is_revert(&self) -> bool {
        self.result.is_revert()
    }

    /// Returns whether the instruction result is an error.
    #[inline]
    pub const fn is_error(&self) -> bool {
        self.result.is_error()
    }
}

#[cfg(test)]
mod tests {
    use core::{any::Any, str::FromStr};

    use super::*;
    use crate::{opcode::InstructionTable, DummyHost};
    use revm_primitives::{hex, keccak256, Address, CancunSpec, LatestSpec, ShanghaiSpec, B256};

    #[test]
    fn object_safety() {
        let mut interp = Interpreter::new(Contract::default(), u64::MAX, false);

        let mut host = crate::DummyHost::default();
        let table: InstructionTable<DummyHost, u32> =
            crate::opcode::make_instruction_table::<u32, DummyHost, CancunSpec>();
        let ret = interp.run(EMPTY_SHARED_MEMORY, &mut host, &table, &mut u32::MAX);

        let host: &mut dyn Host<u32> = &mut host as &mut dyn Host<u32>;
        let table: InstructionTable<dyn Host<u32>, u32> =
            crate::opcode::make_instruction_table::<u32, dyn Host<u32>, CancunSpec>();
        let _ = interp.run(EMPTY_SHARED_MEMORY, host, &table, &mut u32::MAX);
    }

    #[test]
    fn test_run_inspect_create() {
        let code = "7067600035600757FE5B60005260086018F3600052601760156000f0600060006000600060008561FFFFf1600060006032600060008661FFFFf1";
        let code = Bytecode::new_raw(Bytes::from_str(code).unwrap());

        let code_hash = hex::encode(keccak256(code.bytecode_bytes()));
        let input = Bytes::from_str("b5a49624").unwrap();

        let target = Address::from_str("5B38Da6a701c568545dCfcB03FcB875f56beddC4").unwrap();
        let call = Contract::new(
            input.into(),
            Arc::new(code),
            Some(B256::from_str(&code_hash).unwrap()),
            target,
            Address::default(),
            U256::ZERO,
            target,
        );
        let mut interp = Interpreter::new(call, u64::MAX, false);

        let mut host = crate::DummyHost::default();
        let table: InstructionTable<DummyHost, u32> =
            crate::opcode::make_instruction_table::<u32, DummyHost, ShanghaiSpec>();

        let ret = interp.run_inspect::<u32, DummyHost, ShanghaiSpec>(&mut host, &table, &mut 3);
        println!("ret is {:?}", ret);
    }

    #[test]
    fn test_run_inspect() {
        // contract A {
        //     uint256 x = 256;
        //     function test() public view returns(uint){
        //         return x;
        //     }
        // }

        // contract B{
        //     function test() public returns(uint){
        //         A a = new A();
        //         (bool ret, bytes memory data) = address(a).staticcall(abi.encodeWithSignature("test()"));
        //         require(ret == true);
        //         return abi.decode(data, (uint256));
        //     }
        // }

        let code = "608060405234801561000f575f80fd5b5060043610610029575f3560e01c8063f8a8fd6d1461002d575b5f80fd5b61003561004b565b60405161004291906101b0565b60405180910390f35b5f806040516100599061018c565b604051809103905ff080158015610072573d5f803e3d5ffd5b5090505f808273ffffffffffffffffffffffffffffffffffffffff166040516024016040516020818303038152906040527ff8a8fd6d000000000000000000000000000000000000000000000000000000007bffffffffffffffffffffffffffffffffffffffffffffffffffffffff19166020820180517bffffffffffffffffffffffffffffffffffffffffffffffffffffffff838183161783525050505060405161011e919061021b565b5f60405180830381855afa9150503d805f8114610156576040519150601f19603f3d011682016040523d82523d5f602084013e61015b565b606091505b50915091506001151582151514610170575f80fd5b80806020019051810190610184919061025f565b935050505090565b60ce8061028b83390190565b5f819050919050565b6101aa81610198565b82525050565b5f6020820190506101c35f8301846101a1565b92915050565b5f81519050919050565b5f81905092915050565b8281835e5f83830152505050565b5f6101f5826101c9565b6101ff81856101d3565b935061020f8185602086016101dd565b80840191505092915050565b5f61022682846101eb565b915081905092915050565b5f80fd5b61023e81610198565b8114610248575f80fd5b50565b5f8151905061025981610235565b92915050565b5f6020828403121561027457610273610231565b5b5f6102818482850161024b565b9150509291505056fe60806040526101005f553480156013575f80fd5b5060af80601f5f395ff3fe6080604052348015600e575f80fd5b50600436106026575f3560e01c8063f8a8fd6d14602a575b5f80fd5b60306044565b604051603b91906062565b60405180910390f35b5f8054905090565b5f819050919050565b605c81604c565b82525050565b5f60208201905060735f8301846055565b9291505056fea2646970667358221220e2983c948a5d33611cc3a2d4ec5404e857c43f9ea5ec9cb4b3a710253bcdb53664736f6c63430008190033a2646970667358221220702b896f84f4ba4d28ab121e7c773dc70223a968bd5c1af0594da4827b57df0964736f6c63430008190033";
        let code = "604260005260206000F3";
        let code = Bytes::from_str(code).unwrap();
        let code = Bytecode::new_raw(code);

        let code_hash = hex::encode(keccak256(code.bytecode_bytes()));
        let input = Bytes::from_str("f8a8fd6d").unwrap();

        let target = Address::from_str("5B38Da6a701c568545dCfcB03FcB875f56beddC4").unwrap();
        let call = Contract::new(
            input.into(),
            Arc::new(code),
            Some(B256::from_str(&code_hash).unwrap()),
            target,
            Address::default(),
            U256::ZERO,
            target,
        );
        let mut interp = Interpreter::new(call, u64::MAX, true);

        let mut host = crate::DummyHost::default();
        let table: InstructionTable<DummyHost, u32> =
            crate::opcode::make_instruction_table::<u32, DummyHost, CancunSpec>();

        let ret = interp.run_inspect::<u32, DummyHost, ShanghaiSpec>(&mut host, &table, &mut 3);

        println!("return data is: {}", interp.return_data_buffer);
        // if interp.next_action.is_return() {
        //     println!(
        //         "return data is: {:?}",
        //         interp.next_action.into_result_return().unwrap().output
        //     );
        // }
    }
}
