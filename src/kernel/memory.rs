use crate::kernel::{bytes::Bytes, Pointer, Value, ValueSize};
use segmap::SegmentMap;
use std::{
    cell::{Ref, RefCell, RefMut},
    ops::{Deref, DerefMut, Range},
};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error("Loaded overlapping memory.")]
    MemoryOverlapps {
        sections: Vec<(String, Range<Pointer>)>,
    },

    #[error("Wrong memory type: {address:08x} Wanted read:{read_wanted} Wanted write:{write_wanted} Wanted execute:{execute_wanted}")]
    WrongMemoryType {
        address: Pointer,
        read_wanted: bool,
        write_wanted: bool,
        execute_wanted: bool,
    },

    #[error("Attempt to access unmapped memory: 0x{0:016x}.")]
    UnmappedAddress(Pointer),

    #[error("Memory access operation is split between blocks.")]
    SectionAliacing,
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct ProcessMemory {
    segments: SegmentMap<Pointer, RefCell<MemoryBlock>>,
}

impl ProcessMemory {
    pub fn new() -> Self {
        Self {
            segments: SegmentMap::new(),
        }
    }

    pub fn get_memory_block(&self, address: &Pointer) -> Result<Ref<MemoryBlock>> {
        self.segments
            .get(address)
            .map_or(Err(Error::UnmappedAddress(*address)), |cell| {
                Ok(cell.borrow())
            })
    }

    pub fn get_memory_block_mut(&self, address: &Pointer) -> Result<RefMut<MemoryBlock>> {
        self.segments
            .get(address)
            .map_or(Err(Error::UnmappedAddress(*address)), |cell| {
                Ok(cell.borrow_mut())
            })
    }

    pub fn read_random(&self, address: Pointer, size: ValueSize) -> Result<Value> {
        let range = address..address + size.len() as Pointer;

        let block = self.get_memory_block(&range.start)?;

        if block.is_read() {
            let data = block.get_range(range)?;
            // println!("READ RANDOM {:016x}: {:02x?}", address, data);
            Ok(Value::from_bytes(data))
        } else {
            Err(Error::WrongMemoryType {
                address: range.start,
                read_wanted: true,
                write_wanted: false,
                execute_wanted: false,
            })
        }
    }

    pub fn write_random(&self, address: Pointer, value: Value) -> Result<()> {
        let mut block = self.get_memory_block_mut(&address)?;

        let data = value.to_bytes();
        let length = value.len();

        if block.is_write() {
            let range = address..address + length as Pointer;
            let block_data = block.get_range_mut(range)?;

            block_data.copy_from_slice(&data[..length]);

            // println!("WRITE RANDOM {:016x}: {:02x?}", address, block_data);

            Ok(())
        } else {
            Err(Error::WrongMemoryType {
                address,
                read_wanted: false,
                write_wanted: true,
                execute_wanted: false,
            })
        }
    }

    pub fn new_block(&mut self, memory_block: MemoryBlock) -> Result<()> {
        match self
            .segments
            .insert_if_empty(memory_block.range(), RefCell::new(memory_block))
        {
            None => Ok(()), // We're not overlapping anything, so this is fantastic.
            Some(memory_block) => {
                // We overlap. Produce some debug information and give an error.
                let sections: Vec<(String, Range<Pointer>)> = self
                    .segments
                    .iter_in(memory_block.borrow().range())
                    .map(|(_segment, overlapping)| {
                        let block = overlapping.borrow();
                        (block.name.clone(), block.range())
                    })
                    .collect();

                let range = memory_block.borrow().range();

                println!(
                    "OVERLAPPING RANGE {} {:08x}-{:08x}:",
                    memory_block.borrow().name,
                    range.start,
                    range.end
                );
                for (name, range) in sections.iter() {
                    println!("\t{}: {:08x}-{:08x}", name, range.start, range.end);
                }

                Err(Error::MemoryOverlapps { sections })
            }
        }
    }

    pub fn new_blank_block(&mut self, block: BlankMemoryBlock) -> Result<()> {
        let range = block.range;

        // Can't modify the memory while iterating it, so we need to collect these into an owned vec.
        let gaps: Vec<Range<Pointer>> = self
            .segments
            .iter_gaps()
            .map(|gap| Range {
                start: **gap.start_value().expect("Infinite memory secton."),
                end: **gap.end_value().expect("Infinite memory secton."),
            })
            .filter(|gap| gap.end >= range.start && gap.start <= range.end)
            .map(|gap| Range {
                start: std::cmp::max(gap.start, range.start),
                end: std::cmp::min(gap.end, range.end),
            })
            .collect();

        println!("ADD BLANK SECTION {}: {:016x?}", block.name, gaps);

        // We need to keep track of where the end is.
        let mut max = range.start;
        let mut index = 0;
        for gap in gaps {
            max = std::cmp::max(max, gap.end);

            let length = gap.end - gap.start;

            if length > 0 {
                let data = Bytes::Original(vec![0u8; length as usize]);
                let block = MemoryBlock::new(
                    format!("{}-{}", block.name, index),
                    gap.start,
                    data,
                    block.read,
                    block.write,
                    block.execute,
                );
                index += 1;

                println!(
                    "BLANK BLOCK {}: {:08x}-{:08x}",
                    block.name, gap.start, gap.end
                );

                self.new_block(block)?;
            }
        }

        let end_block_length = range.end + 1 - max;

        if end_block_length > 0 {
            let data = Bytes::Original(vec![0u8; end_block_length as usize]);
            let block = MemoryBlock::new(
                format!("{}-{}", block.name, index),
                max,
                data,
                block.read,
                block.write,
                block.execute,
            );

            println!("BLANK BLOCK {}: {:08x}-{:08x}", block.name, max, range.end);

            // We ignore errors here because there's actually a good chance this section is overlapping, and
            // if that's the case, I'm totally fine with just failing this.
            self.new_block(block).ok();
        }

        // Verify that every point exists.
        for i in range {
            debug_assert!(
                self.segments.get(&i).is_some(),
                "Missing address: {:016x}",
                i
            );
        }

        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct MemoryBlock {
    name: String,
    read: bool,
    write: bool,
    execute: bool,
    base_address: Pointer,
    data: Bytes,
}

impl MemoryBlock {
    pub fn new(
        name: impl Into<String>,
        base_address: Pointer,
        data: Bytes,
        read: bool,
        write: bool,
        execute: bool,
    ) -> Self {
        let name = name.into();

        Self {
            name,
            read,
            write,
            execute,
            base_address,
            data,
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

#[derive(Clone)]
pub struct BlankMemoryBlock {
    name: String,
    range: Range<Pointer>,
    read: bool,
    write: bool,
    execute: bool,
}

impl BlankMemoryBlock {
    pub fn new(
        name: impl Into<String>,
        base_address: Pointer,
        length: Pointer,
        read: bool,
        write: bool,
        execute: bool,
    ) -> Self {
        let name = name.into();

        Self {
            name,
            range: Range {
                start: base_address,
                end: base_address + length,
            },
            read,
            write,
            execute,
        }
    }
}

#[test]
fn overlapping_memory() {
    #[cfg(not(tarpaulin_include))]
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

    let mut kernel = ProcessMemory::new();
    kernel
        .new_block(MemoryBlock::new(
            "",
            0,
            Bytes::from_static(&[0u8; 512]),
            false,
            false,
            false,
        ))
        .unwrap();

    kernel
        .new_block(MemoryBlock::new(
            "",
            512,
            Bytes::from_static(&[0u8; 512]),
            false,
            false,
            false,
        ))
        .unwrap();

    let result = kernel.new_block(MemoryBlock::new(
        "",
        512,
        Bytes::from_static(&[0u8; 512]),
        false,
        false,
        false,
    ));
    assert_overlap_failed(result).unwrap();

    let result = kernel.new_block(MemoryBlock::new(
        "",
        256,
        Bytes::from_static(&[0u8; 512]),
        false,
        false,
        false,
    ));
    assert_overlap_failed(result).unwrap();

    let result = kernel.new_block(MemoryBlock::new(
        "",
        1,
        Bytes::from_static(&[0u8; 1]),
        false,
        false,
        false,
    ));
    assert_overlap_failed(result).unwrap();
}
