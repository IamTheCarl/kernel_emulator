use crate::kernel::{bytes::Bytes, Pointer};
use segmap::SegmentMap;
use std::{
    cell::{Ref, RefCell, RefMut},
    collections::HashMap,
    ops::{Deref, DerefMut, Range},
};
use thiserror::Error;
use yaxpeax_arch::{Decoder, Reader, U8Reader};
use yaxpeax_x86::long_mode::{InstDecoder, Instruction};

#[derive(Error, Debug)]
pub enum Error {
    #[error("Loaded overlapping memory.")]
    MemoryOverlapps { sections: Vec<Range<Pointer>> },

    #[error("Wrong memory type: {address:08x} Wanted read:{read_wanted} Wanted write:{write_wanted} Wanted execute:{execute_wanted}")]
    WrongMemoryType {
        address: Pointer,
        read_wanted: bool,
        write_wanted: bool,
        execute_wanted: bool,
    },

    #[error("Attempt to access unmapped memory.")]
    UnmappedAddress,

    #[error("Access memory is split between blocks.")]
    SectionAliacing,

    #[error("Jump to address that aliaces an instruction.")]
    InvalidInstructionAddress,
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct SystemMemory {
    segments: SegmentMap<Pointer, RefCell<MemoryBlock>>,
}

impl SystemMemory {
    pub fn new() -> Self {
        Self {
            segments: SegmentMap::new(),
        }
    }

    pub fn get_memory_block(&self, address: &Pointer) -> Result<Ref<MemoryBlock>> {
        self.segments
            .get(address)
            .map_or(Err(Error::UnmappedAddress), |cell| Ok(cell.borrow()))
    }

    pub fn get_memory_block_mut(&self, address: &Pointer) -> Result<RefMut<MemoryBlock>> {
        self.segments
            .get(address)
            .map_or(Err(Error::UnmappedAddress), |cell| Ok(cell.borrow_mut()))
    }

    pub fn new_block(&mut self, memory_block: MemoryBlock) -> Result<()> {
        // We're not overlapping anything, so this is fantastic.
        match self
            .segments
            .insert_if_empty(memory_block.range(), RefCell::new(memory_block))
        {
            None => Ok(()),
            Some(memory_block) => {
                let sections: Vec<Range<Pointer>> = self
                    .segments
                    .iter_in(memory_block.borrow().range())
                    .map(|(_segment, overlapping)| overlapping.borrow().range())
                    .collect();

                let range = memory_block.borrow().range();

                println!("OVERLAPPING RANGE {:08x}-{:08x}:", range.start, range.end);
                for range in sections.iter() {
                    println!("\t{:08x}-{:08x}", range.start, range.end);
                }

                Err(Error::MemoryOverlapps { sections })
            }
        }
    }

    pub fn end_address(&self) -> Pointer {
        self.segments.bounds().map_or(0, |bounds| {
            bounds.end_value().copied().copied().unwrap_or(0)
        })
    }
}

#[derive(Clone, Debug)]
pub struct MemoryBlock {
    read: bool,
    write: bool,
    execute: bool,
    base_address: Pointer,
    data: Bytes,
    instructions: Vec<Instruction>,
    instruction_addresses: HashMap<Pointer, usize>,
}

impl MemoryBlock {
    pub fn new(base_address: Pointer, data: Bytes, read: bool, write: bool, execute: bool) -> Self {
        let (instruction_addresses, instructions) = if execute {
            decode_instructions(base_address, &data)
        } else {
            (HashMap::new(), Vec::new())
        };

        Self {
            read,
            write,
            execute,
            base_address,
            data,
            instructions,
            instruction_addresses,
        }
    }
}

impl MemoryBlock {
    pub fn is_executable(&self) -> bool {
        self.execute
    }

    pub fn is_read(&self) -> bool {
        self.read
    }

    pub fn is_write(&self) -> bool {
        self.write
    }

    pub fn range(&self) -> std::ops::Range<Pointer> {
        self.base_address..(self.base_address + self.data.len() as Pointer - 1)
    }

    pub fn instruction_iterator(&self, address: Pointer) -> Result<InstructionIterator> {
        if self.is_executable() {
            let instruction_index = self.instruction_addresses.get(&address).cloned();

            if let Some(instruction_index) = instruction_index {
                Ok(InstructionIterator { instruction_index })
            } else {
                Err(Error::InvalidInstructionAddress)
            }
        } else {
            Err(Error::WrongMemoryType {
                address,
                read_wanted: false,
                write_wanted: false,
                execute_wanted: true,
            })
        }
    }

    pub fn get_range(&self, range: Range<Pointer>) -> Result<&[u8]> {
        let start = range.start - self.base_address;
        let end = range.end - self.base_address;

        self.data
            .get(start as usize..end as usize)
            .map_or(Err(Error::SectionAliacing), Ok)
    }

    pub fn get_range_mut(&mut self, range: Range<Pointer>) -> Result<&mut [u8]> {
        let start = range.start - self.base_address;
        let end = range.end - self.base_address;

        // FIXME we need to rebuild the executable code after the slice is released.

        self.data
            .get_mut(start as usize..end as usize)
            .map_or(Err(Error::SectionAliacing), Ok)
    }
}

impl Deref for MemoryBlock {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.data.deref()
    }
}

impl DerefMut for MemoryBlock {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.data.deref_mut()
    }
}

impl std::cmp::PartialEq for MemoryBlock {
    fn eq(&self, _other: &Self) -> bool {
        // They are NEVER equal.
        false
    }
}

impl std::cmp::Eq for MemoryBlock {}

fn decode_instructions(
    base_address: Pointer,
    bytes: &Bytes,
) -> (HashMap<Pointer, usize>, Vec<Instruction>) {
    let decoder = InstDecoder::minimal();

    let mut block = U8Reader::new(bytes);

    let mut instructions = Vec::new();
    let mut instruction_addresses = HashMap::new();

    let mut current_offset = base_address
        + <U8Reader<'_> as Reader<u16, yaxpeax_arch::U32le>>::total_offset(&mut block) as u64;

    while let Ok(instruction) = decoder.decode(&mut block) {
        instruction_addresses.insert(current_offset, instructions.len());
        instructions.push(instruction);

        current_offset = base_address
            + <U8Reader<'_> as Reader<u16, yaxpeax_arch::U32le>>::total_offset(&mut block) as u64;
    }

    (instruction_addresses, instructions)
}

pub struct InstructionIterator {
    instruction_index: usize,
}

impl InstructionIterator {
    pub fn next<'a>(&mut self, block: &'a MemoryBlock) -> Option<&'a Instruction> {
        let old_index = self.instruction_index;
        self.instruction_index += 1;

        block.instructions.get(old_index)
    }
}

#[test]
fn overlapping_memory() {
    fn assert_overlap_failed(result: Result<()>) -> std::result::Result<(), &'static str> {
        match result {
            Err(error) => match error {
                Error::MemoryOverlapps { .. } => {
                    // We have successfully failed.
                    Ok(())
                }
                _ => Err("Overlapping produced wrong error type."),
            },
            Ok(_) => Err("Overlapping did not fail."),
        }
    }

    let mut kernel = SystemMemory::new();
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
    let mut kernel = SystemMemory::new();
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
