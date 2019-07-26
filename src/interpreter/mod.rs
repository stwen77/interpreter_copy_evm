mod call_type;
mod externalities;
mod instructions;
mod memory;
mod raw;
mod return_data;
mod schedule;
mod stack;

use bit_set::BitSet;
use bytes::Bytes;
use call_type::CallType;
use ethereum_types::{Address, H256, U256};
use externalities::*;
use instructions::Instruction;
use memory::Memory;
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
    UnusedGas(u32),
    JumpToPosition(U256),
    StopExecutionNeedsReturn {
        // Gas left.
        gas: u32,
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
                let result = self
                    .exec_instruction(current_gas, ext, instruction, requirements_gas)
                    .unwrap();

                InstructionResult::Ok
            }
        };
        Err(InterpreterResult::Continue)
    }
    fn exec_instruction(
        &mut self,
        gas: u32,
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
                    return Ok(InstructionResult::UnusedGas(0));
                }

                let contract_code = self.mem.read_slice(init_off, init_size);

                let create_result = ext.create(
                    &U256::from(0), //&create_gas.as_u256(),
                    &endowment,
                    contract_code,
                    address_scheme,
                    true,
                );
                return match create_result {
                    Ok(ContractCreateResult::Created(address, gas_left)) => {
                        self.stack.push(address_to_u256(address));
                        Ok(InstructionResult::UnusedGas(0))
                    }
                    Ok(ContractCreateResult::Reverted(gas_left, return_data)) => {
                        self.stack.push(U256::zero());
                        self.return_data = return_data;
                        Ok(InstructionResult::UnusedGas(0))
                    }
                    Ok(ContractCreateResult::Failed) => {
                        self.stack.push(U256::zero());
                        Ok(InstructionResult::Ok)
                    }
                    Err(trap) => Ok(InstructionResult::Trap),
                };
            }
            instructions::CALL
            | instructions::CALLCODE
            | instructions::DELEGATECALL
            | instructions::STATICCALL => {
                assert!(
                    ext.schedule().call_value_transfer_gas > ext.schedule().call_stipend,
                    "overflow possible"
                );

                self.stack.pop_back();
                let call_gas = 0;
                let code_address = self.stack.pop_back();
                let code_address = u256_to_address(&code_address);

                let value = if instruction == instructions::DELEGATECALL {
                    None
                } else if instruction == instructions::STATICCALL {
                    Some(U256::zero())
                } else {
                    Some(self.stack.pop_back())
                };

                let in_off = self.stack.pop_back();
                let in_size = self.stack.pop_back();
                let out_off = self.stack.pop_back();
                let out_size = self.stack.pop_back();

                // Add stipend (only CALL|CALLCODE when value > 0)
                let call_gas = 0;

                // Get sender & receive addresses, check if we have balance
                let (sender_address, receive_address, has_balance, call_type) = match instruction {
                    instructions::CALL => {
                        if ext.is_static() && value.map_or(false, |v| !v.is_zero()) {
                            return Err(());
                        }
                        let has_balance = ext.balance(&self.params.address)?
                            >= value.expect("value set for all but delegate call; qed");
                        (
                            &self.params.address,
                            &code_address,
                            has_balance,
                            CallType::Call,
                        )
                    }
                    instructions::CALLCODE => {
                        let has_balance = ext.balance(&self.params.address)?
                            >= value.expect("value set for all but delegate call; qed");
                        (
                            &self.params.address,
                            &self.params.address,
                            has_balance,
                            CallType::CallCode,
                        )
                    }
                    instructions::DELEGATECALL => (
                        &self.params.sender,
                        &self.params.address,
                        true,
                        CallType::DelegateCall,
                    ),
                    instructions::STATICCALL => (
                        &self.params.address,
                        &code_address,
                        true,
                        CallType::StaticCall,
                    ),
                    _ => panic!(format!(
                        "Unexpected instruction {:?} in CALL branch.",
                        instruction
                    )),
                };

                // clear return data buffer before creating new call frame.
                self.return_data = ReturnData::empty();

                let can_call = has_balance && ext.depth() < ext.schedule().max_depth;
                if !can_call {
                    self.stack.push(U256::zero());
                    return Ok(InstructionResult::UnusedGas(call_gas));
                }

                let call_result = {
                    let input = self.mem.read_slice(in_off, in_size);
                    ext.call(
                        &U256::from(call_gas),
                        sender_address,
                        receive_address,
                        value,
                        input,
                        &code_address,
                        call_type,
                        true,
                    )
                };

                self.resume_output_range = Some((out_off, out_size));

                return match call_result {
                    Ok(MessageCallResult::Success(gas_left, data)) => {
                        let output = self.mem.writeable_slice(out_off, out_size);
                        let len = cmp::min(output.len(), data.len());
                        (&mut output[..len]).copy_from_slice(&data[..len]);

                        self.stack.push(U256::one());
                        self.return_data = data;
                        Ok(InstructionResult::UnusedGas(0))
                    }
                    Ok(MessageCallResult::Reverted(gas_left, data)) => {
                        let output = self.mem.writeable_slice(out_off, out_size);
                        let len = cmp::min(output.len(), data.len());
                        (&mut output[..len]).copy_from_slice(&data[..len]);

                        self.stack.push(U256::zero());
                        self.return_data = data;
                        Ok(InstructionResult::UnusedGas(0))
                    }
                    Ok(MessageCallResult::Failed) => {
                        self.stack.push(U256::zero());
                        Ok(InstructionResult::Ok)
                    }
                    Err(trap) => Ok(InstructionResult::Trap),
                };
            }
            instructions::RETURN => {
                let init_off = self.stack.pop_back();
                let init_size = self.stack.pop_back();

                return Ok(InstructionResult::StopExecutionNeedsReturn {
                    gas: gas,
                    init_off: init_off,
                    init_size: init_size,
                    apply: true,
                });
            }
            instructions::REVERT => {
                let init_off = self.stack.pop_back();
                let init_size = self.stack.pop_back();

                return Ok(InstructionResult::StopExecutionNeedsReturn {
                    gas: gas,
                    init_off: init_off,
                    init_size: init_size,
                    apply: false,
                });
            }
            instructions::STOP => {
                return Ok(InstructionResult::StopExecution);
            }
            instructions::SUICIDE => {
                let address = self.stack.pop_back();
                //ext.suicide(&u256_to_address(&address))?;
                return Ok(InstructionResult::StopExecution);
            }
            instructions::LOG0
            | instructions::LOG1
            | instructions::LOG2
            | instructions::LOG3
            | instructions::LOG4 => {
                let no_of_topics = instruction
                    .log_topics()
                    .expect("log_topics always return some for LOG* instructions; qed");

                let offset = self.stack.pop_back();
                let size = self.stack.pop_back();
                let topics:Vec<H256> = self
                    .stack
                    .pop_n(no_of_topics)
                    .iter()
                    .map(H256::from)
                    .collect();
                //ext.log(topics, self.mem.read_slice(offset, size))?;
            }
            _ => {}
        }
        Err(())
    }
}

fn address_to_u256(value: Address) -> U256 {
    U256::from(&*H256::from(value))
}

fn u256_to_address(value: &U256) -> Address {
    Address::from(H256::from(value))
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
