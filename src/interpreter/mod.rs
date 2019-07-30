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

const ONE: U256 = U256([1, 0, 0, 0]);
const TWO: U256 = U256([2, 0, 0, 0]);
const TWO_POW_5: U256 = U256([0x20, 0, 0, 0]);
const TWO_POW_8: U256 = U256([0x100, 0, 0, 0]);
const TWO_POW_16: U256 = U256([0x10000, 0, 0, 0]);
const TWO_POW_24: U256 = U256([0x1000000, 0, 0, 0]);
const TWO_POW_64: U256 = U256([0, 0x1, 0, 0]); // 0x1 00000000 00000000
const TWO_POW_96: U256 = U256([0, 0x100000000, 0, 0]); //0x1 00000000 00000000 00000000
const TWO_POW_224: U256 = U256([0, 0, 0, 0x100000000]); //0x1 00000000 00000000 00000000 00000000 00000000 00000000 00000000
const TWO_POW_248: U256 = U256([0, 0, 0, 0x100000000000000]); //0x1 00000000 00000000 00000000 00000000 00000000 00000000 00000000 000000

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
    pub call_type: CallType,
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

fn get_and_reset_sign(value: U256) -> (U256, bool) {
    let U256(arr) = value;
    let sign = arr[3].leading_zeros() == 0;
    (set_sign(value, sign), sign)
}

fn set_sign(value: U256, sign: bool) -> U256 {
    if sign {
        (!U256::zero() ^ value).overflowing_add(U256::one()).0
    } else {
        value
    }
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
                let topics: Vec<H256> = self
                    .stack
                    .pop_n(no_of_topics)
                    .iter()
                    .map(H256::from)
                    .collect();
                //ext.log(topics, self.mem.read_slice(offset, size))?;
            }
            instructions::PUSH1
            | instructions::PUSH2
            | instructions::PUSH3
            | instructions::PUSH4
            | instructions::PUSH5
            | instructions::PUSH6
            | instructions::PUSH7
            | instructions::PUSH8
            | instructions::PUSH9
            | instructions::PUSH10
            | instructions::PUSH11
            | instructions::PUSH12
            | instructions::PUSH13
            | instructions::PUSH14
            | instructions::PUSH15
            | instructions::PUSH16
            | instructions::PUSH17
            | instructions::PUSH18
            | instructions::PUSH19
            | instructions::PUSH20
            | instructions::PUSH21
            | instructions::PUSH22
            | instructions::PUSH23
            | instructions::PUSH24
            | instructions::PUSH25
            | instructions::PUSH26
            | instructions::PUSH27
            | instructions::PUSH28
            | instructions::PUSH29
            | instructions::PUSH30
            | instructions::PUSH31
            | instructions::PUSH32 => {
                let bytes = instruction
                    .push_bytes()
                    .expect("push_bytes always return some for PUSH* instructions");
                let val = self.reader.read(bytes);
                self.stack.push(val);
            }
            instructions::MLOAD => {
                let word = self.mem.read(self.stack.pop_back());
                self.stack.push(U256::from(word));
            }
            instructions::MSTORE => {
                let offset = self.stack.pop_back();
                let word = self.stack.pop_back();
                Memory::write(&mut self.mem, offset, word);
            }
            instructions::MSTORE8 => {
                let offset = self.stack.pop_back();
                let byte = self.stack.pop_back();
                self.mem.write_byte(offset, byte);
            }
            instructions::MSIZE => {
                self.stack.push(U256::from(self.mem.size()));
            }
            instructions::SHA3 => {
                let offset = self.stack.pop_back();
                let size = self.stack.pop_back();
                //to do let k = keccak(self.mem.read_slice(offset, size));
                //to do self.stack.push(U256::from(&*k));
            }
            instructions::SLOAD => {
                let key = H256::from(&self.stack.pop_back());
                //let word = U256::from(&*ext.storage_at(&key)?);
                //self.stack.push(word);
            }
            instructions::SSTORE => {
                //to do
            }
            instructions::PC => {
                self.stack.push(U256::from(self.reader.position - 1));
            }
            instructions::GAS => {
                self.stack.push(U256::from(gas));
            }
            instructions::ADDRESS => {
                self.stack
                    .push(address_to_u256(self.params.address.clone()));
            }
            instructions::ORIGIN => {
                self.stack.push(address_to_u256(self.params.origin.clone()));
            }
            instructions::BALANCE => {
                let address = u256_to_address(&self.stack.pop_back());
                let balance = ext.balance(&address)?;
                self.stack.push(balance);
            }
            instructions::CALLER => {
                self.stack.push(address_to_u256(self.params.sender.clone()));
            }
            instructions::CALLVALUE => {
                //to do
            }
            instructions::CALLDATALOAD => {
                let big_id = self.stack.pop_back();
                let id = big_id.low_u64() as usize;
                let max = id.wrapping_add(32);
                if let Some(data) = self.params.data.as_ref() {
                    let bound = cmp::min(data.len(), max);
                    if id < bound && big_id < U256::from(data.len()) {
                        let mut v = [0u8; 32];
                        v[0..bound - id].clone_from_slice(&data[id..bound]);
                        self.stack.push(U256::from(&v[..]))
                    } else {
                        self.stack.push(U256::zero())
                    }
                } else {
                    self.stack.push(U256::zero())
                }
            }
            instructions::CALLDATASIZE => {
                self.stack
                    .push(U256::from(self.params.data.as_ref().map_or(0, |l| l.len())));
            }
            instructions::CODESIZE => {
                self.stack.push(U256::from(self.reader.len()));
            }
            instructions::RETURNDATASIZE => self.stack.push(U256::from(self.return_data.len())),
            instructions::EXTCODESIZE => {
                let address = u256_to_address(&self.stack.pop_back());
                //let len = ext.extcodesize(&address)?.unwrap_or(0);
                //self.stack.push(U256::from(len));
            }
            instructions::CALLDATACOPY => {
                //Self::copy_data_to_memory(&mut self.mem, &mut self.stack, &self.params.data.as_ref().map_or_else(|| &[] as &[u8], |d| &*d as &[u8]));
            }
            instructions::RETURNDATACOPY => {
                {
                    let source_offset = self.stack.peek(1);
                    let size = self.stack.peek(2);
                    let return_data_len = U256::from(self.return_data.len());
                    //if source_offset.saturating_add(*size) > return_data_len
                    {
                        //return Err(vm::Error::OutOfBounds);
                    }
                }
                //Self::copy_data_to_memory(&mut self.mem, &mut self.stack, &*self.return_data);
            }
            instructions::CODECOPY => {
                //Self::copy_data_to_memory(&mut self.mem, &mut self.stack, &self.reader.code);
            }
            instructions::EXTCODECOPY => {
                let address = u256_to_address(&self.stack.pop_back());
                //let code = ext.extcode(&address)?;
                //Self::copy_data_to_memory(&mut self.mem,&mut self.stack,code.as_ref().map(|c| &(*c)[..]).unwrap_or(&[])	);
            }
            instructions::GASPRICE => {
                self.stack.push(self.params.gas_price.clone());
            }
            instructions::BLOCKHASH => {
                let block_number = self.stack.pop_back();
                //let block_hash = ext.blockhash(&block_number);
                //self.stack.push(U256::from(&*block_hash));
            }
            instructions::COINBASE => {
                //self.stack.push(address_to_u256(ext.env_info().author.clone()));
            }
            instructions::TIMESTAMP => {
                //self.stack.push(U256::from(ext.env_info().timestamp));
            }
            instructions::NUMBER => {
                //self.stack.push(U256::from(ext.env_info().number));
            }
            instructions::DIFFICULTY => {
                //self.stack.push(ext.env_info().difficulty.clone());
            }
            instructions::GASLIMIT => {
                //self.stack.push(ext.env_info().gas_limit.clone());
            }
            instructions::DUP1
            | instructions::DUP2
            | instructions::DUP3
            | instructions::DUP4
            | instructions::DUP5
            | instructions::DUP6
            | instructions::DUP7
            | instructions::DUP8
            | instructions::DUP9
            | instructions::DUP10
            | instructions::DUP11
            | instructions::DUP12
            | instructions::DUP13
            | instructions::DUP14
            | instructions::DUP15
            | instructions::DUP16 => {
                let position = instruction
                    .dup_position()
                    .expect("dup_position always return some for DUP* instructions");
                let val = self.stack.peek(position).clone();
                self.stack.push(val);
            }
            instructions::SWAP1
            | instructions::SWAP2
            | instructions::SWAP3
            | instructions::SWAP4
            | instructions::SWAP5
            | instructions::SWAP6
            | instructions::SWAP7
            | instructions::SWAP8
            | instructions::SWAP9
            | instructions::SWAP10
            | instructions::SWAP11
            | instructions::SWAP12
            | instructions::SWAP13
            | instructions::SWAP14
            | instructions::SWAP15
            | instructions::SWAP16 => {
                let position = instruction
                    .swap_position()
                    .expect("swap_position always return some for SWAP* instructions");
                self.stack.swap_with_top(position)
            }
            instructions::POP => {
                self.stack.pop_back();
            }
            instructions::ADD => {
                let a = self.stack.pop_back();
                let b = self.stack.pop_back();
                self.stack.push(a.overflowing_add(b).0);
            }
            instructions::MUL => {
                let a = self.stack.pop_back();
                let b = self.stack.pop_back();
                self.stack.push(a.overflowing_mul(b).0);
            }
            instructions::SUB => {
                let a = self.stack.pop_back();
                let b = self.stack.pop_back();
                self.stack.push(a.overflowing_sub(b).0);
            }
            instructions::DIV => {
                let a = self.stack.pop_back();
                let b = self.stack.pop_back();
                self.stack.push(if !b.is_zero() {
                    match b {
                        ONE => a,
                        TWO => a >> 1,
                        TWO_POW_5 => a >> 5,
                        TWO_POW_8 => a >> 8,
                        TWO_POW_16 => a >> 16,
                        TWO_POW_24 => a >> 24,
                        TWO_POW_64 => a >> 64,
                        TWO_POW_96 => a >> 96,
                        TWO_POW_224 => a >> 224,
                        TWO_POW_248 => a >> 248,
                        _ => a / b,
                    }
                } else {
                    U256::zero()
                });
            }
            instructions::MOD => {
                let a = self.stack.pop_back();
                let b = self.stack.pop_back();
                self.stack
                    .push(if !b.is_zero() { a % b } else { U256::zero() });
            }
            instructions::SDIV => {
                let (a, sign_a) = get_and_reset_sign(self.stack.pop_back());
                let (b, sign_b) = get_and_reset_sign(self.stack.pop_back());

                // -2^255
                let min = (U256::one() << 255) - U256::one();
                self.stack.push(if b.is_zero() {
                    U256::zero()
                } else if a == min && b == !U256::zero() {
                    min
                } else {
                    let c = a / b;
                    set_sign(c, sign_a ^ sign_b)
                });
            }
            instructions::SMOD => {
                let ua = self.stack.pop_back();
                let ub = self.stack.pop_back();
                let (a, sign_a) = get_and_reset_sign(ua);
                let b = get_and_reset_sign(ub).0;

                self.stack.push(if !b.is_zero() {
                    let c = a % b;
                    set_sign(c, sign_a)
                } else {
                    U256::zero()
                });
            }
            instructions::EXP => {
                let base = self.stack.pop_back();
                let expon = self.stack.pop_back();
                let res = base.overflowing_pow(expon).0;
                self.stack.push(res);
            }
            instructions::NOT => {
                let a = self.stack.pop_back();
                self.stack.push(!a);
            }
            instructions::LT => {
                let a = self.stack.pop_back();
                let b = self.stack.pop_back();
                self.stack.push(Self::bool_to_u256(a < b));
            }
            instructions::SLT => {
                let (a, neg_a) = get_and_reset_sign(self.stack.pop_back());
                let (b, neg_b) = get_and_reset_sign(self.stack.pop_back());

                let is_positive_lt = a < b && !(neg_a | neg_b);
                let is_negative_lt = a > b && (neg_a & neg_b);
                let has_different_signs = neg_a && !neg_b;

                self.stack.push(Self::bool_to_u256(
                    is_positive_lt | is_negative_lt | has_different_signs,
                ));
            }
            instructions::GT => {
                let a = self.stack.pop_back();
                let b = self.stack.pop_back();
                self.stack.push(Self::bool_to_u256(a > b));
            }
            instructions::SGT => {
                let (a, neg_a) = get_and_reset_sign(self.stack.pop_back());
                let (b, neg_b) = get_and_reset_sign(self.stack.pop_back());

                let is_positive_gt = a > b && !(neg_a | neg_b);
                let is_negative_gt = a < b && (neg_a & neg_b);
                let has_different_signs = !neg_a && neg_b;

                self.stack.push(Self::bool_to_u256(
                    is_positive_gt | is_negative_gt | has_different_signs,
                ));
            }
            instructions::EQ => {
                let a = self.stack.pop_back();
                let b = self.stack.pop_back();
                self.stack.push(Self::bool_to_u256(a == b));
            }
            instructions::ISZERO => {
                let a = self.stack.pop_back();
                self.stack.push(Self::bool_to_u256(a.is_zero()));
            }
            instructions::AND => {
                let a = self.stack.pop_back();
                let b = self.stack.pop_back();
                self.stack.push(a & b);
            }
            instructions::OR => {
                let a = self.stack.pop_back();
                let b = self.stack.pop_back();
                self.stack.push(a | b);
            }
            instructions::XOR => {
                let a = self.stack.pop_back();
                let b = self.stack.pop_back();
                self.stack.push(a ^ b);
            }
            instructions::BYTE => {
                let word = self.stack.pop_back();
                let val = self.stack.pop_back();
                let byte = match word < U256::from(32) {
                    true => (val >> (8 * (31 - word.low_u64() as usize))) & U256::from(0xff),
                    false => U256::zero(),
                };
                self.stack.push(byte);
            }
            instructions::ADDMOD => {
                let a = self.stack.pop_back();
                let b = self.stack.pop_back();
                let c = self.stack.pop_back();

                self.stack.push(if !c.is_zero() {
                    let a_num = to_biguint(a);
                    let b_num = to_biguint(b);
                    let c_num = to_biguint(c);
                    let res = a_num + b_num;
                    let x = res % c_num;
                    from_biguint(x)
                } else {
                    U256::zero()
                });
            }
            instructions::MULMOD => {
                let a = self.stack.pop_back();
                let b = self.stack.pop_back();
                let c = self.stack.pop_back();

                self.stack.push(if !c.is_zero() {
                    let a_num = to_biguint(a);
                    let b_num = to_biguint(b);
                    let c_num = to_biguint(c);
                    let res = a_num * b_num;
                    let x = res % c_num;
                    from_biguint(x)
                } else {
                    U256::zero()
                });
            }
            instructions::SIGNEXTEND => {
                let bit = self.stack.pop_back();
                if bit < U256::from(32) {
                    let number = self.stack.pop_back();
                    let bit_position = (bit.low_u64() * 8 + 7) as usize;

                    let bit = number.bit(bit_position);
                    let mask = (U256::one() << bit_position) - U256::one();
                    self.stack
                        .push(if bit { number | !mask } else { number & mask });
                }
            }
            instructions::SHL => {
                const CONST_256: U256 = U256([256, 0, 0, 0]);

                let shift = self.stack.pop_back();
                let value = self.stack.pop_back();

                let result = if shift >= CONST_256 {
                    U256::zero()
                } else {
                    value << (shift.as_u32() as usize)
                };
                self.stack.push(result);
            }
            instructions::SHR => {
                const CONST_256: U256 = U256([256, 0, 0, 0]);

                let shift = self.stack.pop_back();
                let value = self.stack.pop_back();

                let result = if shift >= CONST_256 {
                    U256::zero()
                } else {
                    value >> (shift.as_u32() as usize)
                };
                self.stack.push(result);
            }
            instructions::SAR => {
                // We cannot use get_and_reset_sign/set_sign here, because the rounding looks different.

                const CONST_256: U256 = U256([256, 0, 0, 0]);
                const CONST_HIBIT: U256 = U256([0, 0, 0, 0x8000000000000000]);

                let shift = self.stack.pop_back();
                let value = self.stack.pop_back();
                let sign = value & CONST_HIBIT != U256::zero();

                let result = if shift >= CONST_256 {
                    if sign {
                        U256::max_value()
                    } else {
                        U256::zero()
                    }
                } else {
                    let shift = shift.as_u32() as usize;
                    let mut shifted = value >> shift;
                    if sign {
                        shifted = shifted | (U256::max_value() << (256 - shift));
                    }
                    shifted
                };
                self.stack.push(result);
            }

            _ => {}
        }
        Err(())
    }

    fn bool_to_u256(val: bool) -> U256 {
        if val {
            U256::one()
        } else {
            U256::zero()
        }
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
