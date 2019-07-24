mod externalities;
mod instructions;
mod raw;
mod return_data;
mod schedule;
mod stack;

use bit_set::BitSet;
use bytes::Bytes;
use ethereum_types::{Address, H256, U256};
use externalities::Ext;
use instructions::Instruction;
use num_bigint::BigUint;
use raw::*;
use return_data::*;
use stack::*;
use std::marker::PhantomData;
use std::sync::Arc;
use std::{cmp, mem};

/// Stepping result returned by interpreter.
pub enum InterpreterResult {
    /// The VM has already stopped.
    Stopped,
    /// The VM has just finished execution in the current step.
    Done,
    /// The VM can continue to run.
    Continue,
    Trap,
}

/// ActionParams without code, so that it can be feed into CodeReader.
#[derive(Debug)]
struct InterpreterParams {
    /// Address of currently executed code.
    pub code_address: Address,
    /// Hash of currently executed code.
    pub code_hash: Option<H256>,
    /// Receive address. Usually equal to code_address,
    /// except when called using CALLCODE.
    pub address: Address,
    /// Sender of current part of the transaction.
    pub sender: Address,
    /// Transaction initiator.
    pub origin: Address,
    /// Gas paid up front for transaction execution
    pub gas: U256,
    /// Gas price.
    pub gas_price: U256,
    /// Transaction value.
    //pub value: ActionValue,
    /// Input data.
    pub data: Option<Bytes>,
    // Type of call
    //pub call_type: CallType,
    // Param types encoding
    //pub params_type: ParamsType,
}

enum InstructionResult {
    Ok,
    //UnusedGas(Gas),
    JumpToPosition(U256),
    StopExecutionNeedsReturn {
        // Gas left.
        //gas: Gas,
        /// Return data offset.
        init_off: U256,
        /// Return data size.
        init_size: U256,
        /// Apply or revert state changes.
        apply: bool,
    },
    StopExecution,
    Trap, //(TrapKind),
}

struct CodeReader {
    position: usize, //ProgramCounter,
    code: Arc<Bytes>,
}

impl CodeReader {
    /// Create new code reader - starting at position 0.
    fn new(code: Arc<Bytes>) -> Self {
        CodeReader { code, position: 0 }
    }

    /// Get `no_of_bytes` from code and convert to U256. Move PC
    fn read(&mut self, no_of_bytes: usize) -> U256 {
        let pos = self.position;
        self.position += no_of_bytes;
        let max = cmp::min(pos + no_of_bytes, self.code.len());
        U256::from(&self.code[pos..max])
    }

    fn len(&self) -> usize {
        self.code.len()
    }
}

fn to_biguint(x: U256) -> BigUint {
    let mut bytes = [0u8; 32];
    x.to_little_endian(&mut bytes);
    BigUint::from_bytes_le(&bytes)
}

fn from_biguint(x: BigUint) -> U256 {
    let bytes = x.to_bytes_le();
    U256::from_little_endian(&bytes)
}

pub struct Interpreter {
    mem: Vec<u8>,
    //cache: Arc<SharedCache>,
    params: InterpreterParams,
    reader: CodeReader,
    return_data: ReturnData,
    //informant: informant::EvmInformant,
    do_trace: bool,
    done: bool,
    valid_jump_destinations: Option<Arc<BitSet>>,
    //gasometer: Option<Gasometer<Cost>>,
    stack: VecStack<U256>,
    resume_output_range: Option<(U256, U256)>,
    resume_result: Option<InstructionResult>,
    last_stack_ret_len: usize,
    //_type: PhantomData<Cost>,
}

impl Interpreter {
    fn exec(mut self: Box<Self>, ext: &mut Ext) {
        loop {
            let result = self.step(ext);
        }
    }
}

impl Interpreter {
    pub fn step(&mut self, ext: &mut Ext) -> InterpreterResult {
        if self.done {
            return InterpreterResult::Stopped;
        }
        self.step_inner(ext);
        InterpreterResult::Done
    }
    fn step_inner(&mut self, ext: &mut Ext) -> Result<Never, InterpreterResult> {
        let result = match self.resume_result.take() {
            Some(result) => result,
            None => {
                let opcode = self.reader.code[self.reader.position];
                let instruction = Instruction::from_u8(opcode);

                let instruction = match instruction {
                    Some(i) => i,
                    None => return Err(InterpreterResult::Done),
                };

                let info = instruction.info();
                self.last_stack_ret_len = info.ret;
                //self.verify_instruction(ext, instruction, info)?;

                // Execute instruction
                let requirements_gas = 0;
                let current_gas = 0; //self.gasometer.as_mut().expect(GASOMETER_PROOF).current_gas;
                let result =
                    self.exec_instruction(current_gas, ext, instruction, requirements_gas)?;

                InstructionResult::Ok
            }
        };
        Err(InterpreterResult::Continue)
    }
    fn exec_instruction(
        &mut self,
        gas: usize,
        ext: &mut Ext,
        instruction: Instruction,
        provided: usize,
    ) -> Result<InstructionResult, ()> {
        match instruction {
            instructions::JUMP => {
                let jump = self.stack.pop_back();
                return Ok(InstructionResult::JumpToPosition(jump));
            }
            instructions::JUMPI => {
                let jump = self.stack.pop_back();
                let condition = self.stack.pop_back();
                if !condition.is_zero() {
                    return Ok(InstructionResult::JumpToPosition(jump));
                }
            }
            instructions::CREATE | instructions::CREATE2 => {
                let endowment = self.stack.pop_back();
                let init_off = self.stack.pop_back();
                let init_size = self.stack.pop_back();
                let address_scheme = match instruction {
                    instructions::CREATE => CreateContractAddress::FromSenderAndNonce,
                    instructions::CREATE2 => CreateContractAddress::FromSenderSaltAndCodeHash(
                        self.stack.pop_back().into(),
                    ),
                    _ => unreachable!("instruction can only be CREATE/CREATE2 checked above; qed"),
                };

                //let create_gas = provided.expect("`provided` comes through Self::exec from `Gasometer::get_gas_cost_mem`; `gas_gas_mem_cost` guarantees `Some` when instruction is `CALL`/`CALLCODE`/`DELEGATECALL`/`CREATE`; this is `CREATE`; qed");

                if ext.is_static() {
                    return Err(());
                }

                // clear return data buffer before creating new call frame.
                self.return_data = ReturnData::empty();

                let can_create = ext.balance(&self.params.address)? >= endowment
                    && ext.depth() < ext.schedule().max_depth;
                if !can_create {
                    self.stack.push(U256::zero());
                    return Ok(InstructionResult::UnusedGas(create_gas));
                }

                let contract_code = self.mem.read_slice(init_off, init_size);

                let create_result = ext.create(
                    &create_gas.as_u256(),
                    &endowment,
                    contract_code,
                    address_scheme,
                    true,
                );
                return match create_result {
                    Ok(ContractCreateResult::Created(address, gas_left)) => {
                        self.stack.push(address_to_u256(address));
                        Ok(InstructionResult::UnusedGas(
                            Cost::from_u256(gas_left).expect("Gas left cannot be greater."),
                        ))
                    }
                    Ok(ContractCreateResult::Reverted(gas_left, return_data)) => {
                        self.stack.push(U256::zero());
                        self.return_data = return_data;
                        Ok(InstructionResult::UnusedGas(
                            Cost::from_u256(gas_left).expect("Gas left cannot be greater."),
                        ))
                    }
                    Ok(ContractCreateResult::Failed) => {
                        self.stack.push(U256::zero());
                        Ok(InstructionResult::Ok)
                    }
                    Err(trap) => Ok(InstructionResult::Trap(trap)),
                };
            }

            _ => {}
        }
        Err(())
    }
}

enum Never {}

enum PubErr {
    None,
}
impl From<PubErr> for InterpreterResult {
    fn from(err: PubErr) -> Self {
        InterpreterResult::Done
    }
}
