use std::marker::PhantomData;
use std::sync::Arc;
use std::{cmp, mem};
use bit_set::BitSet;
use bytes::Bytes;
use ethereum_types::{Address, H256, U256};
use num_bigint::BigUint;


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
	Trap,//(TrapKind),
}

struct CodeReader {
	position: usize, //ProgramCounter,
	code: Arc<Bytes>,
}

impl CodeReader {
	/// Create new code reader - starting at position 0.
	fn new(code: Arc<Bytes>) -> Self {
		CodeReader {
			code,
			position: 0,
		}
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
    //reader: CodeReader,
    //return_data: ReturnData,
    //informant: informant::EvmInformant,
    do_trace: bool,
    done: bool,
    valid_jump_destinations: Option<Arc<BitSet>>,
    //gasometer: Option<Gasometer<Cost>>,
    //stack: VecStack<U256>,
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
        let result = match self.resume_result.take(){
            Some(result) => result,
            None => {


                InstructionResult::Ok
            },
        };
        Err(InterpreterResult::Continue)
    }
}

pub trait Ext {}
enum Never {}
