use elf_rs::{Elf, ElfFile, SectionHeaderFlags, SectionType};
use std::{ffi::CString, sync::Arc};
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

    #[error("CString has invalid format: {0}")]
    StringFormat(#[from] std::ffi::NulError),
}

type Result<T> = std::result::Result<T, Error>;

pub struct Executable {
    // Where execution should start.
    entry_point: Pointer,

    sections: Vec<MemoryBlock>,
    blank_sections: Vec<BlankMemoryBlock>,
}

pub type Pointer = u64;
pub const POINTER_WIDTH: Pointer = std::mem::size_of::<Pointer>() as Pointer;
pub const STACK_SIZE: Pointer = 4 * 1024; // 4 Kb
pub const STACK_START: Pointer = 0x7FFFFFFFFFFFFFFF;

pub enum ProgramResult {
    Exit(u64),
    Halt,
}

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
        let mut blank_sections = Vec::new();
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
                //     "Load section:\t{:08x}-{:08x}\tR:{}\tW:{}\tX:{}\tName: {}",
                //     header.addr(),
                //     header.addr() + base_data.len() as Pointer - 1,
                //     readable,
                //     writable,
                //     executable,
                //     String::from_utf8_lossy(header.section_name())
                // );

                if header.sh_type() != SectionType::SHT_NOBITS {
                    sections.push(MemoryBlock::new(
                        header.addr(),
                        Bytes::reference(base_data),
                        readable,
                        writable,
                        executable,
                    ));
                } else {
                    blank_sections.push(BlankMemoryBlock::new(
                        header.addr() as Pointer,
                        base_data.len() as Pointer,
                        readable,
                        writable,
                        executable,
                    ))
                }
            }
        }

        Ok(Arc::new(Executable {
            entry_point,
            sections,
            blank_sections,
        }))
    }

    fn build_stack(arguments: impl Into<Vec<String>>) -> Result<(Pointer, MemoryBlock)> {
        let arguments = arguments.into();
        let memory_start = STACK_START - STACK_SIZE;

        let mut data = vec![0u8; STACK_SIZE as usize];
        let mut stack_pointer = STACK_SIZE;

        let mut push = |to_push: &[u8]| {
            let end = stack_pointer;
            stack_pointer -= to_push.len() as Pointer;
            data[stack_pointer as usize..end as usize].copy_from_slice(to_push);

            end
        };

        let argument_count = arguments.len() as Pointer;

        // Push argument strings.
        let mut argument_pointers = Vec::new();
        argument_pointers.reserve(arguments.len());

        for argument in arguments {
            let argument = CString::new(argument)?;
            let pointer = push(argument.as_bytes_with_nul());
            argument_pointers.push(memory_start + pointer);
        }

        // Push null aux vector.
        push(&[0u8; POINTER_WIDTH as usize * 2]); // Must end with two null words.

        // Push environment pointers. (unimplemented)
        push(&[0u8; POINTER_WIDTH as usize]); // Must end with null word.

        // Push argv.
        // We're actually just reserving space here.
        push(&[0u8; POINTER_WIDTH as usize]); // Must end with null word.
        argument_pointers.reverse();
        for pointer in argument_pointers {
            // Push arguments on there too.
            push(&pointer.to_le_bytes());
        }

        // Push argc.
        push(&argument_count.to_le_bytes());

        // println!("{:02x?}", data);

        Ok((
            memory_start + stack_pointer as Pointer,
            MemoryBlock::new(memory_start, Bytes::Original(data), true, true, false),
        ))
    }

    pub fn execute(
        &mut self,
        executable: &Executable,
        arguments: impl Into<Vec<String>>,
    ) -> Result<ProgramResult> {
        let arguments = arguments.into();

        // The register file. We need to set this up.
        let mut registers = RegisterFile::new();

        // Start by loading the executable into memory.
        for section in executable.sections.iter() {
            self.memory.new_block(section.clone())?;
        }
        for section in executable.blank_sections.iter() {
            self.memory.new_blank_block(section.clone())?;
        }

        let (stack_pointer, stack) = Self::build_stack(arguments)?;

        println!("STACK POINTER: {:08x}", stack_pointer);
        println!("STACK RANGE: {:08x?}", stack.range());

        self.memory.new_block(stack)?;
        registers.general_purpose_registers[GeneralPurposeRegister::Rsp as usize] = stack_pointer;

        // This function pointer is to be reigstered with atexit(BA_OS) by the program.
        // TODO make this actually point to something.
        registers.general_purpose_registers[GeneralPurposeRegister::Rdx as usize] = 0xdeafbeef;

        let entry_point = executable.entry_point;
        registers.rip = entry_point;

        let mut active_instruction_block = self.memory.get_memory_block(&entry_point)?;

        let mut next_indstruction = active_instruction_block.instruction_iterator(entry_point)?;

        loop {
            let active_instruction = next_indstruction
                .next(&active_instruction_block)
                .ok_or(Error::EndOfExecutableBlock)?; // TODO see if there's an immediatly adjacent block where rip is pointing.

            match run_instruction(&self.memory, &mut registers, active_instruction)? {
                InstructionResult::Continue => { /* Just go on your merry way! */ }
                InstructionResult::Halt => break Ok(ProgramResult::Halt),
                InstructionResult::Syscall => {
                    if let Some(exit_code) = self.syscall(&mut registers)? {
                        break Ok(ProgramResult::Exit(exit_code));
                    }
                }
                InstructionResult::Jump(new_address) => {
                    active_instruction_block = self.memory.get_memory_block(&new_address)?;
                    next_indstruction =
                        active_instruction_block.instruction_iterator(new_address)?;

                    registers.rip = new_address;
                }
            }
        }
    }

    fn syscall(&self, registers: &mut RegisterFile) -> Result<Option<u64>> {
        let call_code = registers.general_purpose_registers[GeneralPurposeRegister::Rax as usize];

        if let Some(call_code) = Sysno::new(call_code as usize) {
            match call_code {
                Sysno::exit => {
                    let exit_code =
                        registers.general_purpose_registers[GeneralPurposeRegister::Rdi as usize];

                    Ok(Some(exit_code))
                }
                Sysno::write => {
                    let file_handle =
                        registers.general_purpose_registers[GeneralPurposeRegister::Rdi as usize];
                    let message_pointer =
                        registers.general_purpose_registers[GeneralPurposeRegister::Rsi as usize];
                    let message_length =
                        registers.general_purpose_registers[GeneralPurposeRegister::Rdx as usize];

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
                        registers.general_purpose_registers[GeneralPurposeRegister::Rax as usize] =
                            bytes_written as u64;

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
