use num_bigint::BigUint;
use ethereum_types::{U256, H256, Address};

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

fn to_biguint(x: U256) -> BigUint {
	let mut bytes = [0u8; 32];
	x.to_little_endian(&mut bytes);
	BigUint::from_bytes_le(&bytes)
}

fn from_biguint(x: BigUint) -> U256 {
	let bytes = x.to_bytes_le();
	U256::from_little_endian(&bytes)
}

pub struct Interpreter{
    done: bool,
}

impl Interpreter{
    fn exec(mut self: Box<Self>,ext: &mut Ext){
        loop{
            let result = self.step(ext);
        }
    }
}

impl Interpreter{
    pub fn step(&mut self, ext: &mut Ext)->InterpreterResult{
        if self.done{
            return InterpreterResult::Stopped;
        }
        //self.step_inner(ext);
        InterpreterResult::Done
    }
    fn step_inner(&mut self, ext: &mut Ext) -> Result<Never, InterpreterResult> {


        Err(InterpreterResult::Continue)
    }
}

pub trait Ext {}
enum Never {}