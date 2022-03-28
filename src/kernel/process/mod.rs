use crate::kernel::{
    memory::{Error as MemoryError, ProcessMemory},
    Pointer, SyscallRequest,
};
use thiserror::Error;

use super::ProcessId;

mod unicorn_x86;
mod x86;

pub use unicorn_x86::UnicornX86Process;
pub use x86::X86Process;

#[derive(Error, Debug)]
pub enum Error {
    #[error("Memory Error: {0}")]
    Memory(#[from] MemoryError),

    #[error("Platform specific error: {0}")]
    Custom(&'static str),
}

pub type Result<T> = std::result::Result<T, Error>;

pub enum StepResult {
    Continue,
    InvalidInstruction,
    Syscall(SyscallRequest),
}

pub trait Process {
    ///
    /// Initalize the process.
    ///
    /// entry_point - where execution should start.
    /// stack_pointer - where the top of the stack lives.
    /// at_exit_pointer - a function pointer to be registered with atexit(BA_OS).
    /// memory - the memory space visable to the process.
    ///
    /// Returns an instance of the process.
    ///
    fn initalize(
        &mut self,
        process_id: ProcessId,
        entry_point: Pointer,
        stack_pointer: Pointer,
        at_exit_pointer: Pointer,
        memory: ProcessMemory,
    ) -> Result<()>;

    ///
    /// Step the process through a limited number of instructions or attention is needed from the kernel.
    /// Returns StepResult and the number of unprocessed instructions.
    /// Unprocessed instructions will always be zero unless the step exited early for attention from the kernel, or it has overstepped the instruction count.
    /// If the step exited early, the returned step count will be posative, with how many additional instructions are yet to be executed.
    /// If the step overstepped the instruction count, the returned step count will be negative, indicating how many steps in debt it is.
    ///
    /// instruction_count -  the ideal number of instructions to be executed.
    ///
    fn step(
        &mut self,
        instruction_count: u64,
        syscall_result: Option<Pointer>,
    ) -> Result<(StepResult, i64)>; // TODO eventually this needs to always be successful.

    fn memory(&mut self) -> &ProcessMemory;
}
