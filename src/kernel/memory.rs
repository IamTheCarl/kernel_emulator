use crate::kernel::{bytes::Bytes, Pointer};
use segmap::SegmentMap;
use std::{
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

    #[error("Unmapped address.")]
    UnmappedAddress,

    #[error("Access memory is split between blocks.")]
    SectionAliacing,
}

pub type Result<T> = std::result::Result<T, Error>;

pub trait SystemMemory {
    fn memory_mut(&mut self) -> &mut SegmentMap<Pointer, MemoryBlock>;

    fn memory(&self) -> &SegmentMap<Pointer, MemoryBlock>;

    fn new_block(&mut self, memory_block: impl Into<MemoryBlock>) -> Result<()> {
        let memory_block = memory_block.into();

        // We're not overlapping anything, so this is fantastic.
        match self
            .memory_mut()
            .insert_if_empty(memory_block.range(), memory_block)
        {
            None => Ok(()),
            Some(memory_block) => {
                let sections: Vec<Range<Pointer>> = self
                    .memory()
                    .iter_in(memory_block.range())
                    .map(|(_segment, overlapping)| overlapping.range())
                    .collect();

                let range = memory_block.range();

                println!("OVERLAPPING RANGE {:08x}-{:08x}:", range.start, range.end);
                for range in sections.iter() {
                    println!("\t{:08x}-{:08x}", range.start, range.end);
                }

                // Err(Error::MemoryOverlapps { sections })
                Ok(())
            }
        }
    }

    fn get_memory_block(&self, address: &Pointer) -> Option<&MemoryBlock> {
        self.memory().get(address)
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

    fn range(&self) -> std::ops::Range<Pointer> {
        self.base_address..(self.base_address + self.data.len() as Pointer - 1)
    }

    pub fn base_address(&self) -> Pointer {
        self.base_address
    }

    pub fn instruction_iterator(
        &self,
        address: Pointer,
    ) -> Option<impl Iterator<Item = &Instruction>> {
        self.instruction_addresses
            .get(&address)
            .map(|first_instruction_index| self.instructions[*first_instruction_index..].iter())
    }

    pub fn get_range(&self, range: Range<Pointer>) -> Option<&[u8]> {
        let start = range.start - self.base_address;
        let end = range.end - self.base_address;

        self.data.get(start as usize..end as usize)
    }

    // TODO when you add a way to mutably access memory, we need to re-build the executable section, if applicable.
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