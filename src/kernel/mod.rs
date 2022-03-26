use elf_rs::{Elf, ElfFile, SectionHeaderFlags, SectionType};
use std::{collections::HashMap, ffi::CString, sync::Arc};
use syscalls::Sysno;
use thiserror::Error;

mod bytes;
use bytes::Bytes;

mod memory;
use memory::*;

pub mod process;
use process::{Process, StepResult};

#[derive(Error, Debug)]
pub enum Error {
    #[error("Invalid syscall: {0}")]
    InvalidSyscall(u64),

    #[error("Io Error: {0}")]
    Io(#[from] std::io::Error),

    #[error("Memory Error: {0}")]
    Memory(#[from] memory::Error),

    #[error("CPU Error: {0}")]
    Cpu(#[from] process::Error),

    #[error("The end of the exectuable block has been reached.")]
    EndOfExecutableBlock,

    #[error("CString has invalid format: {0}")]
    StringFormat(#[from] std::ffi::NulError),
}

type Result<T> = std::result::Result<T, Error>;

pub struct SyscallRequest {
    process_id: ProcessId,
    call_code: Pointer,
    arguments: [Pointer; 6],
}

pub enum SyscallResult {
    None,
    Some(Pointer),
    Exit,
}

pub struct Executable {
    // Where execution should start.
    entry_point: Pointer,

    sections: Vec<MemoryBlock>,
    blank_sections: Vec<BlankMemoryBlock>,
}

pub type Pointer = u64;
pub type ProcessId = u64;

#[derive(Clone)]
pub enum Value {
    Byte(u8),
    Word(u16),
    Double(u32),
    Quad(u64),
}

impl Value {
    pub fn from_bytes(bytes: &[u8]) -> Self {
        match bytes.len() {
            1 => Self::Byte({
                let mut integer_bytes = [0u8; 1];
                integer_bytes.copy_from_slice(bytes);

                u8::from_le_bytes(integer_bytes)
            }),
            2 => Self::Word({
                let mut integer_bytes = [0u8; 2];
                integer_bytes.copy_from_slice(bytes);

                u16::from_le_bytes(integer_bytes)
            }),
            4 => Self::Double({
                let mut integer_bytes = [0u8; 4];
                integer_bytes.copy_from_slice(bytes);

                u32::from_le_bytes(integer_bytes)
            }),
            8 => Self::Quad({
                let mut integer_bytes = [0u8; 8];
                integer_bytes.copy_from_slice(bytes);

                u64::from_le_bytes(integer_bytes)
            }),
            _ => panic!("Unsupported value width: {}", bytes.len()),
        }
    }

    pub fn as_pointer(&self) -> Pointer {
        match self {
            Self::Byte(v) => *v as Pointer,
            Self::Word(v) => *v as Pointer,
            Self::Double(v) => *v as Pointer,
            Self::Quad(v) => *v as Pointer,
        }
    }

    pub fn as_quad(&self) -> u64 {
        match self {
            Self::Byte(v) => *v as u64,
            Self::Word(v) => *v as u64,
            Self::Double(v) => *v as u64,
            Self::Quad(v) => *v as u64,
        }
    }

    pub fn as_double(&self) -> u32 {
        match self {
            Self::Byte(v) => *v as u32,
            Self::Word(v) => *v as u32,
            Self::Double(v) => *v as u32,
            Self::Quad(v) => *v as u32,
        }
    }

    pub fn as_word(&self) -> u16 {
        match self {
            Self::Byte(v) => *v as u16,
            Self::Word(v) => *v as u16,
            Self::Double(v) => *v as u16,
            Self::Quad(v) => *v as u16,
        }
    }

    pub fn as_byte(&self) -> u8 {
        match self {
            Self::Byte(v) => *v as u8,
            Self::Word(v) => *v as u8,
            Self::Double(v) => *v as u8,
            Self::Quad(v) => *v as u8,
        }
    }

    pub fn as_signed_quad(&self) -> i64 {
        match self {
            Self::Byte(v) => *v as i8 as i64,
            Self::Word(v) => *v as i16 as i64,
            Self::Double(v) => *v as i32 as i64,
            Self::Quad(v) => *v as i64,
        }
    }

    pub fn as_signed_double(&self) -> i32 {
        match self {
            Self::Byte(v) => *v as i8 as i32,
            Self::Word(v) => *v as i16 as i32,
            Self::Double(v) => *v as i32,
            Self::Quad(v) => *v as i32,
        }
    }

    pub fn as_signed_word(&self) -> i16 {
        match self {
            Self::Byte(v) => *v as i8 as i16,
            Self::Word(v) => *v as i16,
            Self::Double(v) => *v as i16,
            Self::Quad(v) => *v as i16,
        }
    }

    pub fn as_signed_byte(&self) -> i8 {
        match self {
            Self::Byte(v) => *v as i8,
            Self::Word(v) => *v as i8,
            Self::Double(v) => *v as i8,
            Self::Quad(v) => *v as i8,
        }
    }

    pub fn to_bytes(&self) -> [u8; 8] {
        let mut bytes = [0u8; 8];

        match self {
            Self::Byte(v) => bytes[..1].copy_from_slice(&v.to_le_bytes()),
            Self::Word(v) => bytes[..2].copy_from_slice(&v.to_le_bytes()),
            Self::Double(v) => bytes[..4].copy_from_slice(&v.to_le_bytes()),
            Self::Quad(v) => bytes.copy_from_slice(&v.to_le_bytes()),
        }

        bytes
    }

    pub fn len(&self) -> usize {
        match self {
            Self::Byte(_) => 1,
            Self::Word(_) => 2,
            Self::Double(_) => 4,
            Self::Quad(_) => 8,
        }
    }

    pub fn dynamic_cast(&self, new_size: ValueSize) -> Self {
        match new_size {
            ValueSize::Byte => Value::Byte(self.as_byte()),
            ValueSize::Word => Value::Word(self.as_word()),
            ValueSize::Double => Value::Double(self.as_double()),
            ValueSize::Quad => Value::Quad(self.as_quad()),
        }
    }

    pub fn dynamic_signed_cast(&self, new_size: ValueSize) -> Self {
        match new_size {
            ValueSize::Byte => Value::Byte(self.as_signed_byte() as u8),
            ValueSize::Word => Value::Word(self.as_signed_word() as u16),
            ValueSize::Double => Value::Double(self.as_signed_double() as u32),
            ValueSize::Quad => Value::Quad(self.as_signed_quad() as u64),
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Byte(v) => write!(f, "{:02x}", v),
            Value::Word(v) => write!(f, "{:04x}", v),
            Value::Double(v) => write!(f, "{:08x}", v),
            Value::Quad(v) => write!(f, "{:016x}", v),
        }
    }
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Byte(v) => write!(f, "{:02x}", v),
            Value::Word(v) => write!(f, "{:04x}", v),
            Value::Double(v) => write!(f, "{:08x}", v),
            Value::Quad(v) => write!(f, "{:016x}", v),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ValueSize {
    Byte,
    Word,
    Double,
    Quad,
}

impl ValueSize {
    pub fn new(size: u8) -> Self {
        match size {
            1 => ValueSize::Byte,
            2 => ValueSize::Word,
            4 => ValueSize::Double,
            8 => ValueSize::Quad,
            _ => panic!("Invalid operand size."),
        }
    }

    pub fn len(&self) -> usize {
        match self {
            ValueSize::Byte => 1,
            ValueSize::Word => 2,
            ValueSize::Double => 4,
            ValueSize::Quad => 8,
        }
    }
}

trait GetValueSize {
    fn value_size(&self) -> ValueSize {
        self.try_value_size().expect("Value does not have width.")
    }
    fn try_value_size(&self) -> Option<ValueSize>;
}

impl GetValueSize for yaxpeax_x86::long_mode::RegSpec {
    fn try_value_size(&self) -> Option<ValueSize> {
        use yaxpeax_x86::long_mode::register_class;

        Some(match self.class() {
            register_class::Q => ValueSize::Quad,
            register_class::D => ValueSize::Double,
            register_class::W => ValueSize::Word,
            register_class::B => ValueSize::Byte,
            register_class::RB => unimplemented!(),
            register_class::CR => unimplemented!(),
            register_class::DR => unimplemented!(),
            register_class::S => unimplemented!(),
            register_class::X => unimplemented!(),
            register_class::Y => unimplemented!(),
            register_class::Z => unimplemented!(),
            register_class::ST => unimplemented!(),
            register_class::MM => unimplemented!(),
            register_class::K => unimplemented!(),
            register_class::RIP => ValueSize::Quad,
            register_class::EIP => ValueSize::Double,
            register_class::RFLAGS => unimplemented!(),
            register_class::EFLAGS => unimplemented!(),
        })
    }
}

impl GetValueSize for yaxpeax_x86::long_mode::Operand {
    fn try_value_size(&self) -> Option<ValueSize> {
        if let Some(width) = self.width() {
            match width {
                1 => Some(ValueSize::Byte),
                2 => Some(ValueSize::Word),
                4 => Some(ValueSize::Double),
                8 => Some(ValueSize::Quad),
                _ => None,
            }
        } else {
            None
        }
    }
}

impl GetValueSize for yaxpeax_x86::long_mode::Instruction {
    fn try_value_size(&self) -> Option<ValueSize> {
        if let Some(width) = self
            .mem_size()
            .and_then(|memory_size| memory_size.bytes_size())
        {
            match width {
                1 => Some(ValueSize::Byte),
                2 => Some(ValueSize::Word),
                4 => Some(ValueSize::Double),
                8 => Some(ValueSize::Quad),
                _ => None,
            }
        } else {
            None
        }
    }
}

impl From<u64> for Value {
    fn from(val: u64) -> Self {
        Value::Quad(val)
    }
}

impl From<i64> for Value {
    fn from(val: i64) -> Self {
        Value::Quad(val as u64)
    }
}

impl From<u32> for Value {
    fn from(val: u32) -> Self {
        Value::Double(val)
    }
}

impl From<i32> for Value {
    fn from(val: i32) -> Self {
        Value::Double(val as u32)
    }
}

impl From<u16> for Value {
    fn from(val: u16) -> Self {
        Value::Word(val)
    }
}

impl From<i16> for Value {
    fn from(val: i16) -> Self {
        Value::Word(val as u16)
    }
}

impl From<u8> for Value {
    fn from(val: u8) -> Self {
        Value::Byte(val)
    }
}

impl From<i8> for Value {
    fn from(val: i8) -> Self {
        Value::Byte(val as u8)
    }
}

pub trait IntoValue {
    fn into_value(self, size: ValueSize) -> Value;
}

impl IntoValue for u64 {
    fn into_value(self, size: ValueSize) -> Value {
        match size {
            ValueSize::Byte => Value::Byte(self as u8),
            ValueSize::Word => Value::Word(self as u16),
            ValueSize::Double => Value::Double(self as u32),
            ValueSize::Quad => Value::Quad(self as u64),
        }
    }
}

impl IntoValue for i64 {
    fn into_value(self, size: ValueSize) -> Value {
        match size {
            ValueSize::Byte => Value::Byte(self as u8),
            ValueSize::Word => Value::Word(self as u16),
            ValueSize::Double => Value::Double(self as u32),
            ValueSize::Quad => Value::Quad(self as u64),
        }
    }
}

impl IntoValue for u32 {
    fn into_value(self, size: ValueSize) -> Value {
        match size {
            ValueSize::Byte => Value::Byte(self as u8),
            ValueSize::Word => Value::Word(self as u16),
            ValueSize::Double => Value::Double(self as u32),
            ValueSize::Quad => Value::Quad(self as u64),
        }
    }
}

impl IntoValue for i32 {
    fn into_value(self, size: ValueSize) -> Value {
        match size {
            ValueSize::Byte => Value::Byte(self as u8),
            ValueSize::Word => Value::Word(self as u16),
            ValueSize::Double => Value::Double(self as u32),
            ValueSize::Quad => Value::Quad(self as i64 as u64),
        }
    }
}

impl IntoValue for u16 {
    fn into_value(self, size: ValueSize) -> Value {
        match size {
            ValueSize::Byte => Value::Byte(self as u8),
            ValueSize::Word => Value::Word(self as u16),
            ValueSize::Double => Value::Double(self as u32),
            ValueSize::Quad => Value::Quad(self as u64),
        }
    }
}

impl IntoValue for i16 {
    fn into_value(self, size: ValueSize) -> Value {
        match size {
            ValueSize::Byte => Value::Byte(self as u8),
            ValueSize::Word => Value::Word(self as u16),
            ValueSize::Double => Value::Double(self as i32 as u32),
            ValueSize::Quad => Value::Quad(self as i64 as u64),
        }
    }
}

impl IntoValue for u8 {
    fn into_value(self, size: ValueSize) -> Value {
        match size {
            ValueSize::Byte => Value::Byte(self as u8),
            ValueSize::Word => Value::Word(self as u16),
            ValueSize::Double => Value::Double(self as u32),
            ValueSize::Quad => Value::Quad(self as u64),
        }
    }
}

impl IntoValue for i8 {
    fn into_value(self, size: ValueSize) -> Value {
        match size {
            ValueSize::Byte => Value::Byte(self as u8),
            ValueSize::Word => Value::Word(self as i16 as u16),
            ValueSize::Double => Value::Double(self as i32 as u32),
            ValueSize::Quad => Value::Quad(self as i64 as u64),
        }
    }
}

pub const POINTER_WIDTH: Pointer = std::mem::size_of::<Pointer>() as Pointer;
pub const STACK_SIZE: Pointer = 4 * 1024; // 4 Kb
pub const STACK_START: Pointer = 0x7FFFFFFFFFFFFFFF;

pub struct Kernel {
    processes: HashMap<ProcessId, Box<dyn Process>>,
    next_pid: u64,
    time_aliace: i64,
}

impl Kernel {
    pub fn new() -> Result<Self> {
        Ok(Self {
            processes: HashMap::new(),
            next_pid: 0,
            time_aliace: 0,
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
                println!(
                    "Load section:\t{:08x}-{:08x}\tR:{}\tW:{}\tX:{}\tName: {}",
                    header.addr(),
                    header.addr() + base_data.len() as Pointer - 1,
                    readable,
                    writable,
                    executable,
                    String::from_utf8_lossy(header.section_name())
                );

                if header.sh_type() != SectionType::SHT_NOBITS {
                    sections.push(MemoryBlock::new(
                        String::from_utf8_lossy(header.section_name()),
                        header.addr(),
                        Bytes::reference(base_data),
                        readable,
                        writable,
                        executable,
                    ));
                } else {
                    blank_sections.push(BlankMemoryBlock::new(
                        String::from_utf8_lossy(header.section_name()),
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

    fn build_stack(arguments: Vec<String>) -> Result<(Pointer, MemoryBlock)> {
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
        argument_pointers.reverse();

        // Push null aux vector.
        push(&[0u8; POINTER_WIDTH as usize * 2]); // Must end with two null words.

        // Push environment pointers. (unimplemented)
        push(&[0u8; POINTER_WIDTH as usize]); // Must end with null word.

        // Push argv.
        // We're actually just reserving space here.
        push(&[0u8; POINTER_WIDTH as usize]); // Must end with null word.
        for pointer in argument_pointers {
            // Push arguments on there too.
            push(&pointer.to_le_bytes());
        }

        // Push argc.
        push(&argument_count.to_le_bytes());

        // println!("STACK {:02x?}", data);

        Ok((
            memory_start + stack_pointer as Pointer,
            MemoryBlock::new(
                "stack",
                memory_start,
                Bytes::Original(data),
                true,
                true,
                false,
            ),
        ))
    }

    pub fn new_process(
        &mut self,
        mut process: Box<dyn Process>,
        executable: &Executable,
        arguments: Vec<String>,
    ) -> Result<ProcessId> {
        let mut memory = ProcessMemory::new();

        // Start by loading the executable into memory.
        for section in executable.sections.iter() {
            memory.new_block(section.clone())?;
        }
        for section in executable.blank_sections.iter() {
            memory.new_blank_block(section.clone())?;
        }

        let (stack_pointer, stack) = Self::build_stack(arguments)?;

        memory.new_block(stack)?;

        let process_id = self.next_pid;
        self.next_pid += 1;

        process.initalize(
            process_id,
            executable.entry_point,
            stack_pointer,
            0xdeafbeef,
            memory,
        )?;

        // Store it for execution later.
        self.processes.insert(process_id, process);
        Ok(process_id)
    }

    pub fn step(&mut self, instruction_quota: u64) -> Vec<(ProcessId, Pointer)> {
        // Account for debt or overflow from the previous run cycle.
        let total_instruction_limit = instruction_quota as i64 + self.time_aliace;
        if total_instruction_limit > 0 {
            // Because we're just starting out, I'm going to just hand each process the same amount of time.
            let num_process = self.processes.len() as i64;

            let (time_per_process, aliace) = (
                total_instruction_limit / num_process,
                total_instruction_limit % num_process,
            );
            // Put that aliace toward our next stepping cycle.
            self.time_aliace = aliace;

            let mut termianted_processes = Vec::new();

            for (process_id, process) in self.processes.iter_mut() {
                let mut syscall_result = None;

                let mut time_to_run = time_per_process;

                println!("Switch to process: {}", process_id);

                loop {
                    match process.step(time_to_run as u64, syscall_result) {
                        Ok((result, time_underrun)) => {
                            time_to_run = time_underrun;

                            match result {
                                StepResult::Continue => {
                                    if time_to_run <= 0 {
                                        // We'll exit if we're out of time.
                                        // Make sure to add that unused time (or overused time) to our time aliace.
                                        self.time_aliace += time_to_run;
                                        break;
                                    }
                                }
                                StepResult::InvalidInstruction => {}
                                StepResult::Syscall(syscall_request) => {
                                    match Self::syscall(
                                        syscall_request,
                                        process.memory(),
                                        &mut termianted_processes,
                                    ) {
                                        Ok(result_code) => match result_code {
                                            SyscallResult::None => syscall_result = None, // No result, but we are to continue processing.
                                            SyscallResult::Some(result) => {
                                                syscall_result = Some(result)
                                            }
                                            SyscallResult::Exit => break, // We have been requested to stop execution of this process.
                                        },
                                        Err(syscall_error) => {
                                            println!("Error in syscall: {:?}", syscall_error);
                                            termianted_processes.push((*process_id, 0xFF));

                                            break;
                                        }
                                    }
                                }
                            }
                        }
                        Err(error) => {
                            println!("Error processing instruction: {:?}", error);
                            termianted_processes.push((*process_id, 0xFF));

                            break;
                        }
                    }
                }
            }

            // Clean up the dead processes.
            for (process_id, _exit_code) in termianted_processes.iter() {
                self.processes.remove(process_id);
            }

            termianted_processes
        } else {
            // Oh wow, we were so in debt that we couldn't even run this cycle.
            // Just use this time to pay off our debt.
            self.time_aliace += instruction_quota as i64;

            // Nothing died, so just return an empty vector.
            Vec::new()
        }
    }

    fn syscall(
        request: SyscallRequest,
        memory: &ProcessMemory,
        terminated_process_list: &mut Vec<(ProcessId, Pointer)>,
    ) -> Result<SyscallResult> {
        let call_code = request.call_code;

        if let Some(call_code) = Sysno::new(call_code as usize) {
            match call_code {
                Sysno::exit => {
                    let exit_code = request.arguments[0];

                    terminated_process_list.push((request.process_id, exit_code));

                    Ok(SyscallResult::Exit)
                }
                Sysno::write => {
                    let file_handle = request.arguments[0];
                    let message_pointer = request.arguments[1];
                    let message_length = request.arguments[2];

                    let mut file: Box<dyn std::io::Write> = match file_handle {
                        1 => Box::new(std::io::stdout()),
                        2 => Box::new(std::io::stderr()),
                        _ => panic!("Non standard file handals are not yet supported."),
                    };

                    let memory_block = memory.get_memory_block(&message_pointer)?;

                    if memory_block.is_read() {
                        let message = memory_block
                            .get_range(message_pointer..message_pointer + message_length)?;

                        // FIXME: An IO error should set errno.
                        let bytes_written = file.write(message)? as Pointer;

                        Ok(SyscallResult::Some(bytes_written))
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
