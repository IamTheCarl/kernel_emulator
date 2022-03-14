use elf_rs::{Elf, ElfFile, ProgramHeaderFlags};
use std::{collections::BTreeMap, sync::Arc};
use syscalls::Sysno;
use thiserror::Error;

mod bytes;
use bytes::Bytes;

mod memory;
use memory::*;

mod cpu;
use cpu::*;

#[derive(Error, Debug)]
pub enum Error {
    #[error("Invalid syscall: {0}")]
    InvalidSyscall(u64),

    #[error("Io Error: {0}")]
    Io(#[from] std::io::Error),

    #[error("Memory Error: {0}")]
    MemoryError(#[from] memory::Error),

    #[error("The end of the exectuable block has been reached.")]
    EndOfExecutableBlock,
}

type Result<T> = std::result::Result<T, Error>;

pub struct Executable {
    // Where execution should start.
    entry_point: Pointer,

    sections: Vec<MemoryBlock>,
}

type Pointer = u64;

pub struct Kernel {
    memory: BTreeMap<Pointer, MemoryBlock>,
}

impl Kernel {
    pub fn new() -> Result<Self> {
        Ok(Self {
            memory: BTreeMap::new(),
        })
    }

    pub fn load_elf(elf_bytes: &[u8]) -> Result<Arc<Executable>> {
        let elf = Elf::from_bytes(elf_bytes).unwrap();

        let mut sections = Vec::new();
        let entry_point = elf.entry_point();

        for header in elf.program_header_iter() {
            let flags = header.flags();

            let base_data = Arc::new(header.content().to_vec());

            sections.push(MemoryBlock::new(
                header.paddr(),
                Bytes::reference(base_data),
                flags & ProgramHeaderFlags::READ == ProgramHeaderFlags::READ,
                flags & ProgramHeaderFlags::WRITE == ProgramHeaderFlags::WRITE,
                flags & ProgramHeaderFlags::EXECUTE == ProgramHeaderFlags::EXECUTE,
            ));
        }

        Ok(Arc::new(Executable {
            entry_point,
            sections,
        }))
    }

    // TODO this function is HUGE! Move it to its own struct in another module.
    pub fn execute(&mut self, executable: &Executable) -> Result<u64> {
        // Start by loading the executable into memory.
        for section in executable.sections.iter() {
            self.new_block(section.clone())?;
        }

        let mut registers: RegisterFile = [0u64; 16];

        let instruction_pointer = executable.entry_point;

        let active_instruction_block = self
            .get_memory_block(instruction_pointer)
            .ok_or(memory::Error::UnmappedAddress)?;

        if active_instruction_block.is_executable() {
            let mut next_indstruction = active_instruction_block
                .instruction_iterator(instruction_pointer)
                .ok_or(memory::Error::WrongMemoryType {
                    address: instruction_pointer,
                    execute_wanted: true,
                    read_wanted: false,
                    write_wanted: false,
                })?;

            loop {
                let active_instruction = next_indstruction
                    .next()
                    .ok_or(Error::EndOfExecutableBlock)?;

                if let Some(syscall_result) =
                    run_instruction(&mut registers, active_instruction, |registers| {
                        self.syscall(registers)
                    })
                {
                    // We had a syscall and need to process the result.
                    if let Some(exit_code) = syscall_result? {
                        // Process terminated.
                        break Ok(exit_code);
                    }
                }
            }
        } else {
            Err(Error::MemoryError(memory::Error::WrongMemoryType {
                address: active_instruction_block.base_address(),
                read_wanted: false,
                write_wanted: false,
                execute_wanted: true,
            }))
        }
    }

    fn syscall(&self, registers: &mut RegisterFile) -> Result<Option<u64>> {
        let call_code = registers[Register::Rax as usize];

        if let Some(call_code) = Sysno::new(call_code as usize) {
            match call_code {
                Sysno::exit => {
                    let exit_code = registers[Register::Rdi as usize];

                    Ok(Some(exit_code))
                }
                Sysno::write => {
                    let file_handle = registers[Register::Rdi as usize];
                    let message_pointer = registers[Register::Rsi as usize];
                    let message_length = registers[Register::Rdx as usize];

                    let mut file: Box<dyn std::io::Write> = match file_handle {
                        1 => Box::new(std::io::stdout()),
                        2 => Box::new(std::io::stderr()),
                        _ => panic!("Non standard file handals are not yet supported."),
                    };

                    let memory_block = self
                        .get_memory_block(message_pointer)
                        .ok_or(memory::Error::UnmappedAddress)?;

                    if memory_block.is_read() {
                        let message = memory_block
                            .get_range(message_pointer..message_pointer + message_length)
                            .ok_or(memory::Error::SectionAliacing)?;

                        let bytes_written = file.write(message)?;
                        registers[Register::Rax as usize] = bytes_written as u64;

                        Ok(None)
                    } else {
                        Err(Error::MemoryError(memory::Error::WrongMemoryType {
                            address: message_pointer,
                            read_wanted: true,
                            write_wanted: false,
                            execute_wanted: false,
                        }))
                    }
                }
                _ => panic!("Syscall `{}` is not yet supported.", call_code),
            }
        } else {
            Err(Error::InvalidSyscall(call_code))
        }
    }
}

impl SystemMemory for Kernel {
    fn memory_mut(&mut self) -> &mut BTreeMap<Pointer, MemoryBlock> {
        &mut self.memory
    }

    fn memory(&self) -> &BTreeMap<Pointer, MemoryBlock> {
        &self.memory
    }
}

#[test]
fn overlapping_memory() {
    fn assert_overlap_failed(result: memory::Result<()>) -> std::result::Result<(), &'static str> {
        match result {
            Err(error) => match error {
                memory::Error::MemoryOverlapps => {
                    // We have successfully failed.
                    Ok(())
                }
                _ => Err("Overlapping produced wrong error type."),
            },
            Ok(_) => Err("Overlapping did not fail."),
        }
    }

    let mut kernel = Kernel::new().unwrap();
    kernel
        .new_block(MemoryBlock::new(
            0,
            Bytes::from_static(&[0u8; 512]),
            false,
            false,
            false,
        ))
        .unwrap();

    kernel
        .new_block(MemoryBlock::new(
            512,
            Bytes::from_static(&[0u8; 512]),
            false,
            false,
            false,
        ))
        .unwrap();

    let result = kernel.new_block(MemoryBlock::new(
        512,
        Bytes::from_static(&[0u8; 512]),
        false,
        false,
        false,
    ));
    assert_overlap_failed(result).unwrap();

    let result = kernel.new_block(MemoryBlock::new(
        256,
        Bytes::from_static(&[0u8; 512]),
        false,
        false,
        false,
    ));
    assert_overlap_failed(result).unwrap();

    let result = kernel.new_block(MemoryBlock::new(
        1,
        Bytes::from_static(&[0u8; 1]),
        false,
        false,
        false,
    ));
    assert_overlap_failed(result).unwrap();
}

#[test]
fn load_instructions() {
    let mut kernel = Kernel::new().unwrap();
    kernel
        .new_block(MemoryBlock::new(
            0,
            Bytes::from_static(&[0x8b, 0x01, 0x00, 0x00, 0x00]),
            false,
            false,
            true,
        ))
        .unwrap();
}
