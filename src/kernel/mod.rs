use elf_rs::{Elf, ElfFile, SectionHeaderFlags};
use std::sync::Arc;
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
    Memory(#[from] memory::Error),

    #[error("CPU Error: {0}")]
    Cpu(#[from] cpu::Error),

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
    memory: SystemMemory,
}

impl Kernel {
    pub fn new() -> Result<Self> {
        Ok(Self {
            memory: SystemMemory::new(),
        })
    }

    pub fn load_elf(elf_bytes: &[u8]) -> Result<Arc<Executable>> {
        let elf = Elf::from_bytes(elf_bytes).unwrap();

        let mut sections = Vec::new();
        let entry_point = elf.entry_point();

        for header in elf.section_header_iter() {
            let flags = header.flags();

            let base_data = Arc::new(header.content().to_vec());

            let readable = flags & SectionHeaderFlags::SHF_ALLOC == SectionHeaderFlags::SHF_ALLOC;
            let writable = flags & SectionHeaderFlags::SHF_WRITE == SectionHeaderFlags::SHF_WRITE;
            let executable =
                flags & SectionHeaderFlags::SHF_EXECINSTR == SectionHeaderFlags::SHF_EXECINSTR;

            if (readable || writable || executable) && base_data.len() > 0 {
                // println!(
                //     "Load section:\t{:08x}-{:08x}\tR:{}\tW:{}\tX:{}",
                //     header.addr(),
                //     header.addr() + base_data.len() as Pointer - 1,
                //     readable,
                //     writable,
                //     executable
                // );

                sections.push(MemoryBlock::new(
                    header.addr(),
                    Bytes::reference(base_data),
                    readable,
                    writable,
                    executable,
                ));
            }
        }

        Ok(Arc::new(Executable {
            entry_point,
            sections,
        }))
    }

    pub fn execute(&mut self, executable: &Executable) -> Result<u64> {
        // Start by loading the executable into memory.
        for section in executable.sections.iter() {
            self.memory.new_block(section.clone())?;
        }

        let mut registers: RegisterFile = [0u64; 16];

        let instruction_pointer = executable.entry_point;

        let active_instruction_block = self.memory.get_memory_block(&instruction_pointer)?;

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

                if let Some(syscall_result) = run_instruction(
                    &self.memory,
                    &mut registers,
                    active_instruction,
                    |registers| self.syscall(registers),
                )? {
                    // We had a syscall and need to process the result.
                    if let Some(exit_code) = syscall_result? {
                        // Process terminated.
                        break Ok(exit_code);
                    }
                }
            }
        } else {
            Err(Error::Memory(memory::Error::WrongMemoryType {
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

                    let memory_block = self.memory.get_memory_block(&message_pointer)?;

                    if memory_block.is_read() {
                        let message = memory_block
                            .get_range(message_pointer..message_pointer + message_length)?;

                        let bytes_written = file.write(message)?;
                        registers[Register::Rax as usize] = bytes_written as u64;

                        Ok(None)
                    } else {
                        Err(Error::Memory(memory::Error::WrongMemoryType {
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
