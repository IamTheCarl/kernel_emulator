// Copyright 2022 James Carl
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::{Error, Process, Result, StepResult};
use crate::kernel::{
    memory::{Error as MemoryError, ProcessMemory},
    GetValueSize, IntoValue, Pointer, ProcessId, SyscallRequest, Value, ValueSize,
};
use std::collections::HashMap;
use yaxpeax_arch::{Decoder, LengthedInstruction, Reader, U8Reader};
use yaxpeax_x86::amd64::{register_class, InstDecoder, Instruction, Opcode, Operand, RegSpec};

// #[cfg(test)]
// mod test;

struct RegisterFile {
    general_purpose_registers: [Pointer; 16],
    rip: Pointer,
    sf: bool,
    zf: bool,
    pf: bool,
    of: bool,
    cf: bool,
    af: bool,
}

impl RegisterFile {
    fn new() -> Self {
        Self {
            general_purpose_registers: [0; 16],
            rip: 0,
            sf: false,
            zf: false,
            pf: false,
            of: false,
            cf: false,
            af: false,
        }
    }

    fn get(&self, register: RegSpec) -> Value {
        match register.class() {
            register_class::Q => {
                Value::Quad(self.general_purpose_registers[register.num() as usize])
            }
            register_class::D => {
                Value::Double(self.general_purpose_registers[register.num() as usize] as u32)
            }
            register_class::W => {
                Value::Word(self.general_purpose_registers[register.num() as usize] as u16)
            }
            register_class::B => {
                Value::Byte(self.general_purpose_registers[register.num() as usize] as u8)
            }
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
            register_class::RIP => Value::Quad(self.rip),
            register_class::EIP => Value::Double(self.rip as u32),
            register_class::RFLAGS => unimplemented!(),
            register_class::EFLAGS => unimplemented!(),
        }
    }

    fn set(&mut self, register: RegSpec, value: Value) {
        match register.class() {
            register_class::Q => {
                self.general_purpose_registers[register.num() as usize] = value.as_pointer()
            }
            register_class::D => {
                self.general_purpose_registers[register.num() as usize] = value.as_pointer()
            }
            register_class::W => {
                self.general_purpose_registers[register.num() as usize] = value.as_pointer()
            }
            register_class::B => {
                self.general_purpose_registers[register.num() as usize] = value.as_pointer()
            }
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
            register_class::RIP => self.rip = value.as_pointer(),
            register_class::EIP => self.rip = value.as_pointer(),
            register_class::RFLAGS => unimplemented!(),
            register_class::EFLAGS => unimplemented!(),
        }
    }
}

impl std::fmt::Debug for RegisterFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RegisterFile")
            .field(
                "rax",
                &self.general_purpose_registers[GeneralPurposeRegister::Rax as usize],
            )
            .field(
                "rcx",
                &self.general_purpose_registers[GeneralPurposeRegister::Rcx as usize],
            )
            .field(
                "rdx",
                &self.general_purpose_registers[GeneralPurposeRegister::Rdx as usize],
            )
            .field(
                "rbx",
                &self.general_purpose_registers[GeneralPurposeRegister::Rbx as usize],
            )
            .field(
                "rsp",
                &self.general_purpose_registers[GeneralPurposeRegister::Rsp as usize],
            )
            .field(
                "rbp",
                &self.general_purpose_registers[GeneralPurposeRegister::Rbp as usize],
            )
            .field(
                "rsi",
                &self.general_purpose_registers[GeneralPurposeRegister::Rsi as usize],
            )
            .field(
                "rdi",
                &self.general_purpose_registers[GeneralPurposeRegister::Rdi as usize],
            )
            .field(
                "r8",
                &self.general_purpose_registers[GeneralPurposeRegister::R8 as usize],
            )
            .field(
                "r9",
                &self.general_purpose_registers[GeneralPurposeRegister::R9 as usize],
            )
            .field(
                "r10",
                &self.general_purpose_registers[GeneralPurposeRegister::R10 as usize],
            )
            .field(
                "r11",
                &self.general_purpose_registers[GeneralPurposeRegister::R11 as usize],
            )
            .field(
                "r12",
                &self.general_purpose_registers[GeneralPurposeRegister::R12 as usize],
            )
            .field(
                "r13",
                &self.general_purpose_registers[GeneralPurposeRegister::R13 as usize],
            )
            .field(
                "r14",
                &self.general_purpose_registers[GeneralPurposeRegister::R14 as usize],
            )
            .field(
                "r15",
                &self.general_purpose_registers[GeneralPurposeRegister::R15 as usize],
            )
            .field("rip", &self.rip)
            .field("sf", &self.sf)
            .field("zf", &self.zf)
            .field("pf", &self.pf)
            .field("of", &self.of)
            .field("cf", &self.cf)
            .field("af", &self.af)
            .finish()
    }
}

#[allow(unused)]
#[repr(usize)]
enum GeneralPurposeRegister {
    Rax = 0,
    Rcx = 1,
    Rdx = 2,
    Rbx = 3,
    Rsp = 4,
    Rbp = 5,
    Rsi = 6,
    Rdi = 7,
    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
    R12 = 12,
    R13 = 13,
    R14 = 14,
    R15 = 15,
}

struct InstructionIterator {
    instruction_index: usize,
    instructions: Vec<Instruction>,
    instruction_addresses: HashMap<Pointer, usize>,
}

impl InstructionIterator {
    fn new() -> Self {
        // Start in an unset state.
        Self {
            instruction_index: 0,
            instructions: Vec::new(),
            instruction_addresses: HashMap::new(),
        }
    }

    fn jump(&mut self, memory: &ProcessMemory, address: Pointer) -> Result<()> {
        if let Some(index) = self.instruction_addresses.get(&address) {
            // We're in the same block, so we'll just change our index.
            self.instruction_index = *index;
            Ok(())
        } else {
            // Looks like we're in a different block. We'll have to find it.

            let block = memory.get_memory_block(&address)?;

            if block.is_executable() {
                let decoder = InstDecoder::minimal();

                let mut block_reader = U8Reader::new(&block);

                let instructions = &mut self.instructions;
                let instruction_addresses = &mut self.instruction_addresses;

                // TODO maybe not toss the old ones out? Jumping back to them will be less expensive if we keep them.
                instructions.clear();
                instruction_addresses.clear();

                let mut current_offset = block.range().start
                    + <U8Reader<'_> as Reader<u16, yaxpeax_arch::U32le>>::total_offset(
                        &mut block_reader,
                    ) as u64;

                while let Ok(instruction) = decoder.decode(&mut block_reader) {
                    instruction_addresses.insert(current_offset, instructions.len());
                    instructions.push(instruction);

                    current_offset += instruction.len();
                }

                // And we need to point into this location as well.
                self.instruction_index = self
                    .instruction_addresses
                    .get(&address)
                    .copied()
                    .ok_or(Error::Memory(MemoryError::SectionAliacing))?;

                Ok(())
            } else {
                // Not executable code.
                Err(Error::Memory(MemoryError::WrongMemoryType {
                    address,
                    read_wanted: false,
                    write_wanted: false,
                    execute_wanted: true,
                }))
            }
        }
    }

    fn next(&mut self) -> Result<&Instruction> {
        let old_index = self.instruction_index;
        self.instruction_index += 1;

        if let Some(instruction) = self.instructions.get(old_index) {
            Ok(instruction)
        } else {
            todo!("Automatic jump to next block.")
        }
    }
}

pub struct X86Process {
    process_id: ProcessId,
    register_file: RegisterFile,
    memory: ProcessMemory,
    instruction_iterator: InstructionIterator,
}

impl Process for X86Process {
    fn initalize(
        &mut self,
        process_id: ProcessId,
        entry_point: Pointer,
        stack_pointer: Pointer,
        at_exit_pointer: Pointer,
        memory: ProcessMemory,
    ) -> super::Result<()> {
        self.process_id = process_id;
        self.memory = memory;

        Self::jump(
            &self.memory,
            &mut self.register_file,
            &mut self.instruction_iterator,
            entry_point,
        )?;

        self.register_file.general_purpose_registers[GeneralPurposeRegister::Rdx as usize] =
            at_exit_pointer;
        self.register_file.general_purpose_registers[GeneralPurposeRegister::Rsp as usize] =
            stack_pointer;

        Ok(())
    }

    fn step(
        &mut self,
        instruction_count: u64,
        syscall_result: Option<Pointer>,
    ) -> super::Result<(StepResult, i64)> {
        // TODO try to avoid counting individual instructions.
        let mut instruction_count = instruction_count as i64;

        if let Some(syscall_result) = syscall_result {
            self.register_file.general_purpose_registers[GeneralPurposeRegister::Rax as usize] =
                syscall_result;
        }
        while instruction_count > 0 {
            let result = self.run_instruction()?;

            match result {
                StepResult::Continue => instruction_count -= 1,
                StepResult::Syscall(_) => return Ok((result, instruction_count)),
                StepResult::InvalidInstruction => return Ok((result, instruction_count)),
            }
        }

        // Perfectly balanced~
        Ok((StepResult::Continue, 0))
    }

    fn memory(&mut self) -> &ProcessMemory {
        &self.memory
    }
}

impl X86Process {
    pub fn new() -> Box<Self> {
        Box::new(Self {
            process_id: 0,
            register_file: RegisterFile::new(),
            memory: ProcessMemory::new(),
            instruction_iterator: InstructionIterator::new(),
        })
    }

    fn read_operand(
        memory: &ProcessMemory,
        registers: &RegisterFile,
        operand: &Operand,
        other_operand: Option<&Operand>,
        instruction: &Instruction,
    ) -> Result<Value> {
        let value_size = match *operand {
            Operand::ImmediateI8(_)
            | Operand::ImmediateU8(_)
            | Operand::ImmediateI16(_)
            | Operand::ImmediateU16(_)
            | Operand::ImmediateI32(_)
            | Operand::ImmediateU32(_)
            | Operand::ImmediateI64(_)
            | Operand::ImmediateU64(_) => other_operand.map_or_else(
                || {
                    operand
                        .try_value_size()
                        .unwrap_or_else(|| instruction.value_size())
                },
                |other_operand| {
                    other_operand
                        .try_value_size()
                        .unwrap_or_else(|| instruction.value_size())
                },
            ),
            _ => operand
                .try_value_size()
                .unwrap_or_else(|| instruction.value_size()),
        };

        Ok(match *operand {
            Operand::ImmediateI8(v) => Value::Byte(v as u8).dynamic_signed_cast(value_size),
            Operand::ImmediateU8(v) => Value::Byte(v).dynamic_cast(value_size),
            Operand::ImmediateI16(v) => Value::Word(v as u16).dynamic_signed_cast(value_size),
            Operand::ImmediateU16(v) => Value::Word(v).dynamic_cast(value_size),
            Operand::ImmediateI32(v) => Value::Double(v as u32).dynamic_signed_cast(value_size),
            Operand::ImmediateU32(v) => Value::Double(v).dynamic_cast(value_size),
            Operand::ImmediateI64(v) => Value::Quad(v as u64).dynamic_signed_cast(value_size),
            Operand::ImmediateU64(v) => Value::Quad(v).dynamic_cast(value_size),
            Operand::Register(spec) => registers.get(spec),
            // Operand::RegisterMaskMerge(_, _, _) => todo!(),
            // Operand::RegisterMaskMergeSae(_, _, _, _) => todo!(),
            // Operand::RegisterMaskMergeSaeNoround(_, _, _) => todo!(),
            // Operand::DisplacementU32(_) => todo!(),
            // Operand::DisplacementU64(_) => todo!(),
            // Operand::RegDeref(_) => todo!(),
            Operand::RegDisp(spec, displacement) => {
                let address = registers
                    .get(spec)
                    .as_pointer()
                    .wrapping_add(displacement as i64 as Pointer);

                // println!("ADDRESS: {:016x}", address);

                memory.read_random(address, value_size)?
            }
            // Operand::RegScale(_, _) => todo!(),
            // Operand::RegIndexBase(_, _) => todo!(),
            // Operand::RegIndexBaseDisp(_, _, _) => todo!(),
            // Operand::RegScaleDisp(_, _, _) => todo!(),
            Operand::RegIndexBaseScale(base, offset, offset_scale) => {
                let base_address = registers.get(base).as_pointer();
                let offset = registers.get(offset).as_pointer();
                let address =
                    base_address.wrapping_add(offset.wrapping_mul(offset_scale as Pointer));

                memory.read_random(address, value_size)?
            }
            Operand::RegIndexBaseScaleDisp(base, offset, offset_scale, displacement) => {
                let base_address = registers.get(base).as_pointer();
                let offset = registers
                    .get(offset)
                    .as_pointer()
                    .wrapping_mul(offset_scale as Pointer);
                let address = base_address
                    .wrapping_add(offset)
                    .wrapping_add(displacement as i64 as Pointer);

                println!("BASE ADDRESS: {:016x}", base_address);
                println!("OFFSET:       {:016x}", offset);
                println!("DISPLACEMENT: {:016x}", displacement);
                println!("ADDRESS:      {:016x}", address);

                memory.read_random(address, value_size)?
            }
            // Operand::RegDerefMasked(_, _) => todo!(),
            // Operand::RegDispMasked(_, _, _) => todo!(),
            // Operand::RegScaleMasked(_, _, _) => todo!(),
            // Operand::RegIndexBaseMasked(_, _, _) => todo!(),
            // Operand::RegIndexBaseDispMasked(_, _, _, _) => todo!(),
            // Operand::RegScaleDispMasked(_, _, _, _) => todo!(),
            // Operand::RegIndexBaseScaleMasked(_, _, _, _) => todo!(),
            // Operand::RegIndexBaseScaleDispMasked(_, _, _, _, _) => todo!(),
            Operand::Nothing => panic!("operand out of bounds."),
            _ => {
                dbg!(operand);
                unreachable!()
            }
        })
    }

    fn write_target(
        memory: &ProcessMemory,
        registers: &mut RegisterFile,
        operand: Operand,
        value: Value,
    ) -> Result<()> {
        match operand {
            Operand::Register(spec) => registers.set(spec, value),
            // Operand::ImmediateI8(_) => todo!(),
            // Operand::ImmediateU8(_) => todo!(),
            // Operand::ImmediateI16(_) => todo!(),
            // Operand::ImmediateU16(_) => todo!(),
            // Operand::ImmediateI32(_) => todo!(),
            // Operand::ImmediateU32(_) => todo!(),
            // Operand::ImmediateI64(_) => todo!(),
            // Operand::ImmediateU64(_) => todo!(),
            // Operand::RegisterMaskMerge(_, _, _) => todo!(),
            // Operand::RegisterMaskMergeSae(_, _, _, _) => todo!(),
            // Operand::RegisterMaskMergeSaeNoround(_, _, _) => todo!(),
            // Operand::DisplacementU32(_) => todo!(),
            // Operand::DisplacementU64(_) => todo!(),
            // Operand::RegDeref(_) => todo!(),
            Operand::RegDisp(spec, displacement) => {
                let address = registers
                    .get(spec)
                    .as_pointer()
                    .wrapping_add(displacement as Pointer);

                memory.write_random(address, value)?;
            }
            // Operand::RegScale(_, _) => todo!(),
            // Operand::RegIndexBase(_, _) => todo!(),
            // Operand::RegIndexBaseDisp(_, _, _) => todo!(),
            // Operand::RegScaleDisp(_, _, _) => todo!(),
            // Operand::RegIndexBaseScale(_, _, _) => todo!(),
            // Operand::RegIndexBaseScaleDisp(_, _, _, _) => todo!(),
            // Operand::RegDerefMasked(_, _) => todo!(),
            // Operand::RegDispMasked(_, _, _) => todo!(),
            // Operand::RegScaleMasked(_, _, _) => todo!(),
            // Operand::RegIndexBaseMasked(_, _, _) => todo!(),
            // Operand::RegIndexBaseDispMasked(_, _, _, _) => todo!(),
            // Operand::RegScaleDispMasked(_, _, _, _) => todo!(),
            // Operand::RegIndexBaseScaleMasked(_, _, _, _) => todo!(),
            // Operand::RegIndexBaseScaleDispMasked(_, _, _, _, _) => todo!(),
            Operand::Nothing => panic!("operand out of bounds."),
            _ => {
                dbg!(operand);
                unreachable!()
            }
        }

        Ok(())
    }

    #[inline]
    fn push_onto_stack(
        memory: &ProcessMemory,
        registers: &mut RegisterFile,
        value: Value,
    ) -> Result<()> {
        let stack_pointer = registers.general_purpose_registers
            [GeneralPurposeRegister::Rsp as usize]
            - value.len() as Pointer;
        registers.general_purpose_registers[GeneralPurposeRegister::Rsp as usize] = stack_pointer;

        // println!("PUSH {:08x}: {}", stack_pointer, value);

        memory.write_random(stack_pointer, value)?;

        Ok(())
    }

    #[inline]
    fn pop_from_stack(
        memory: &ProcessMemory,
        registers: &mut RegisterFile,
        value_size: ValueSize,
    ) -> Result<Value> {
        let stack_pointer =
            registers.general_purpose_registers[GeneralPurposeRegister::Rsp as usize];

        let value = memory.read_random(stack_pointer, value_size)?;

        registers.general_purpose_registers[GeneralPurposeRegister::Rsp as usize] +=
            value.len() as Pointer;

        // println!("POP {:08x}: {}", stack_pointer, value);

        Ok(value)
    }

    #[inline]
    fn jump(
        memory: &ProcessMemory,
        registers: &mut RegisterFile,
        instruction_iterator: &mut InstructionIterator,
        address: Pointer,
    ) -> Result<()> {
        registers.rip = address;
        instruction_iterator.jump(memory, address)?;

        Ok(())
    }

    #[inline]
    fn run_instruction(&mut self) -> Result<StepResult> {
        let instruction = self.instruction_iterator.next()?;

        let instruction_length = instruction.len().to_const();

        // println!("REGISTERS: {:016x?}", registers);

        // let mut instruction_bytes = [0u8; 15];

        // memory.read_random(
        //     registers.rip,
        //     &mut instruction_bytes[..instruction_length as usize],
        // )?;
        // println!(
        //     "{:08x} {:<30}{}",
        //     registers.rip,
        //     format!("{:02x?}", &instruction_bytes[..instruction_length as usize]),
        //     instruction
        // );

        println!("{:08x} {}", self.register_file.rip, instruction);

        // Update instruction pointer.
        self.register_file.rip += instruction_length;

        match instruction.opcode() {
            Opcode::Invalid => return Ok(StepResult::InvalidInstruction),
            Opcode::ADD => {
                let source = instruction.operand(1);
                let target = instruction.operand(0);

                let a = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &target,
                    Some(&source),
                    instruction,
                )?
                .as_signed_quad();
                let b = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &source,
                    Some(&target),
                    instruction,
                )?
                .as_signed_quad();
                let result = a.wrapping_add(b).into_value(target.value_size());

                Self::write_target(
                    &self.memory,
                    &mut self.register_file,
                    instruction.operand(0),
                    result,
                )?;
            }
            Opcode::OR => {
                let source = instruction.operand(1);
                let target = instruction.operand(0);

                let a = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &target,
                    Some(&source),
                    instruction,
                )?
                .as_quad();
                let b = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &source,
                    Some(&target),
                    instruction,
                )?
                .as_quad();
                let result = (a | b).into_value(target.value_size());

                Self::write_target(
                    &self.memory,
                    &mut self.register_file,
                    instruction.operand(0),
                    result,
                )?;
            }
            // Opcode::ADC => todo!(),
            // Opcode::SBB => todo!(),
            Opcode::AND => {
                let source = instruction.operand(1);
                let target = instruction.operand(0);

                let a = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &target,
                    Some(&source),
                    instruction,
                )?
                .as_quad();
                let b = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &source,
                    Some(&target),
                    instruction,
                )?
                .as_quad();

                let result = (a & b).into_value(target.value_size());

                Self::write_target(
                    &self.memory,
                    &mut self.register_file,
                    instruction.operand(0),
                    result,
                )?;
            }
            Opcode::XOR => {
                let source = instruction.operand(1);
                let target = instruction.operand(0);

                let a = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &target,
                    Some(&source),
                    instruction,
                )?
                .as_quad();
                let b = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &source,
                    Some(&target),
                    instruction,
                )?
                .as_quad();
                let result = (a ^ b).into_value(target.value_size());

                Self::write_target(
                    &self.memory,
                    &mut self.register_file,
                    instruction.operand(0),
                    result,
                )?;
            }
            Opcode::SUB => {
                let source = instruction.operand(1);
                let target = instruction.operand(0);

                let a = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &target,
                    Some(&source),
                    instruction,
                )?
                .as_signed_quad();
                let b = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &source,
                    Some(&target),
                    instruction,
                )?
                .as_signed_quad();
                let result = a.wrapping_sub(b).into_value(target.value_size());

                Self::write_target(
                    &self.memory,
                    &mut self.register_file,
                    instruction.operand(0),
                    result,
                )?;
            }
            Opcode::CMP => {
                let operand_a = instruction.operand(1);
                let operand_b = instruction.operand(0);

                let a = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &operand_a,
                    Some(&operand_b),
                    instruction,
                )?
                .as_signed_quad();
                let b = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &operand_b,
                    Some(&operand_a),
                    instruction,
                )?
                .as_signed_quad();
                let result = a.wrapping_sub(b);

                self.register_file.zf = result == 0;
                self.register_file.sf = (result as i64) < 0;
                self.register_file.pf = result.count_ones() & 1 == 1;
            }
            // Opcode::XADD => todo!(),
            // Opcode::BT => todo!(),
            // Opcode::BTS => todo!(),
            // Opcode::BTC => todo!(),
            // Opcode::BTR => todo!(),
            // Opcode::BSF => todo!(),
            // Opcode::BSR => todo!(),
            // Opcode::TZCNT => todo!(),
            // Opcode::MOVSS => todo!(),
            // Opcode::ADDSS => todo!(),
            // Opcode::SUBSS => todo!(),
            // Opcode::MULSS => todo!(),
            // Opcode::DIVSS => todo!(),
            // Opcode::MINSS => todo!(),
            // Opcode::MAXSS => todo!(),
            // Opcode::SQRTSS => todo!(),
            // Opcode::MOVSD => todo!(),
            // Opcode::SQRTSD => todo!(),
            // Opcode::ADDSD => todo!(),
            // Opcode::SUBSD => todo!(),
            // Opcode::MULSD => todo!(),
            // Opcode::DIVSD => todo!(),
            // Opcode::MINSD => todo!(),
            // Opcode::MAXSD => todo!(),
            // Opcode::MOVSLDUP => todo!(),
            // Opcode::MOVSHDUP => todo!(),
            // Opcode::MOVDDUP => todo!(),
            // Opcode::HADDPS => todo!(),
            // Opcode::HSUBPS => todo!(),
            // Opcode::ADDSUBPD => todo!(),
            // Opcode::ADDSUBPS => todo!(),
            // Opcode::CVTSI2SS => todo!(),
            // Opcode::CVTSI2SD => todo!(),
            // Opcode::CVTTSD2SI => todo!(),
            // Opcode::CVTTPS2DQ => todo!(),
            // Opcode::CVTPD2DQ => todo!(),
            // Opcode::CVTPD2PS => todo!(),
            // Opcode::CVTPS2DQ => todo!(),
            // Opcode::CVTSD2SI => todo!(),
            // Opcode::CVTSD2SS => todo!(),
            // Opcode::CVTTSS2SI => todo!(),
            // Opcode::CVTSS2SI => todo!(),
            // Opcode::CVTSS2SD => todo!(),
            // Opcode::CVTDQ2PD => todo!(),
            // Opcode::LDDQU => todo!(),
            // Opcode::MOVZX => todo!(),
            // Opcode::MOVSX => todo!(),
            Opcode::MOVSXD => {
                let target = instruction.operand(0);
                let source = instruction.operand(1);

                let to_move = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &source,
                    Some(&target),
                    instruction,
                )?;
                let to_move = to_move.dynamic_signed_cast(target.value_size());

                Self::write_target(&self.memory, &mut self.register_file, target, to_move)?;
            }
            // Opcode::SAR => todo!(),
            // Opcode::SAL => todo!(),
            // Opcode::SHR => todo!(),
            // Opcode::SHRD => todo!(),
            // Opcode::SHL => todo!(),
            // Opcode::RCR => todo!(),
            // Opcode::RCL => todo!(),
            // Opcode::ROR => todo!(),
            // Opcode::ROL => todo!(),
            // Opcode::INC => todo!(),
            // Opcode::DEC => todo!(),
            Opcode::HLT => return Ok(StepResult::InvalidInstruction), // Halt is not allowed in the userland.
            Opcode::CALL => {
                // Get the return pointer and push that onto the stack.
                // We need that to return later.
                let return_pointer = self.register_file.rip;
                Self::push_onto_stack(
                    &self.memory,
                    &mut self.register_file,
                    Value::Quad(return_pointer),
                )?;

                // Get the new address we're jumping to.
                let new_address = return_pointer.wrapping_add(
                    Self::read_operand(
                        &self.memory,
                        &self.register_file,
                        &instruction.operand(0),
                        None,
                        instruction,
                    )?
                    .as_signed_quad() as u64,
                );

                Self::jump(
                    &self.memory,
                    &mut self.register_file,
                    &mut self.instruction_iterator,
                    new_address,
                )?;
            }
            // Opcode::CALLF => todo!(),
            // Opcode::JMP => todo!(),
            // Opcode::JMPF => todo!(),
            Opcode::PUSH => {
                // We need to figure out the width of our instruction.
                let operand = instruction.operand(0);
                let value = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &operand,
                    None,
                    instruction,
                )?;

                Self::push_onto_stack(&self.memory, &mut self.register_file, value)?;
            }
            Opcode::POP => {
                let target = instruction.operand(0);
                let value = Self::pop_from_stack(
                    &self.memory,
                    &mut self.register_file,
                    target.value_size(),
                )?;
                Self::write_target(&self.memory, &mut self.register_file, target, value)?;
            }
            Opcode::LEA => {
                let target = instruction.operand(0);
                let source = instruction.operand(1);

                let value = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &source,
                    Some(&target),
                    instruction,
                )?;

                Self::write_target(&self.memory, &mut self.register_file, target, value)?;
            }
            Opcode::NOP => {
                // Easy.
            }
            // Opcode::PREFETCHNTA => todo!(),
            // Opcode::PREFETCH0 => todo!(),
            // Opcode::PREFETCH1 => todo!(),
            // Opcode::PREFETCH2 => todo!(),
            // Opcode::XCHG => todo!(),
            // Opcode::POPF => todo!(),
            // Opcode::INT => todo!(),
            // Opcode::INTO => todo!(),
            // Opcode::IRET => todo!(),
            // Opcode::IRETD => todo!(),
            // Opcode::IRETQ => todo!(),
            // Opcode::RETF => todo!(),
            // Opcode::ENTER => todo!(),
            // Opcode::LEAVE => todo!(),
            Opcode::MOV => {
                let source = instruction.operand(1);
                let target = instruction.operand(0);

                let to_move = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &source,
                    Some(&target),
                    instruction,
                )?;

                Self::write_target(&self.memory, &mut self.register_file, target, to_move)?;
            }
            Opcode::RETURN => {
                let return_pointer =
                    Self::pop_from_stack(&self.memory, &mut self.register_file, ValueSize::Quad)?;

                Self::jump(
                    &self.memory,
                    &mut self.register_file,
                    &mut self.instruction_iterator,
                    return_pointer.as_pointer(),
                )?;
            }
            // Opcode::PUSHF => todo!(),
            // Opcode::WAIT => todo!(),
            // Opcode::CBW => todo!(),
            // Opcode::CWDE => todo!(),
            // Opcode::CDQE => todo!(),
            // Opcode::CWD => todo!(),
            // Opcode::CDQ => todo!(),
            // Opcode::CQO => todo!(),
            // Opcode::LODS => todo!(),
            // Opcode::STOS => todo!(),
            // Opcode::LAHF => todo!(),
            // Opcode::SAHF => todo!(),
            // Opcode::CMPS => todo!(),
            // Opcode::SCAS => todo!(),
            // Opcode::MOVS => todo!(),
            Opcode::TEST => {
                let operand_a = instruction.operand(1);
                let operand_b = instruction.operand(0);

                let a = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &operand_a,
                    Some(&operand_a),
                    instruction,
                )?
                .as_quad();
                let b = Self::read_operand(
                    &self.memory,
                    &self.register_file,
                    &operand_b,
                    Some(&operand_b),
                    instruction,
                )?
                .as_quad();
                let result = a & b;

                self.register_file.zf = result == 0;
                self.register_file.sf = (result as i64) < 0;
                self.register_file.pf = result.count_ones() & 1 == 1;
            }
            // Opcode::INS => todo!(),
            // Opcode::IN => todo!(),
            // Opcode::OUTS => todo!(),
            // Opcode::OUT => todo!(),
            // Opcode::IMUL => todo!(),
            // Opcode::JO => todo!(),
            // Opcode::JNO => todo!(),
            // Opcode::JB => todo!(),
            // Opcode::JNB => todo!(),
            Opcode::JZ => {
                if self.register_file.zf {
                    // Zero flag is set. We jump!
                    let address = self.register_file.rip.wrapping_add(
                        Self::read_operand(
                            &self.memory,
                            &self.register_file,
                            &instruction.operand(0),
                            None,
                            instruction,
                        )?
                        .as_signed_quad() as u64,
                    );

                    Self::jump(
                        &self.memory,
                        &mut self.register_file,
                        &mut self.instruction_iterator,
                        address,
                    )?;
                }
            }
            // Opcode::JNZ => todo!(),
            // Opcode::JA => todo!(),
            // Opcode::JNA => todo!(),
            // Opcode::JS => todo!(),
            // Opcode::JNS => todo!(),
            // Opcode::JP => todo!(),
            // Opcode::JNP => todo!(),
            // Opcode::JL => todo!(),
            // Opcode::JGE => todo!(),
            // Opcode::JLE => todo!(),
            // Opcode::JG => todo!(),
            // Opcode::CMOVA => todo!(),
            // Opcode::CMOVB => todo!(),
            // Opcode::CMOVG => todo!(),
            // Opcode::CMOVGE => todo!(),
            // Opcode::CMOVL => todo!(),
            // Opcode::CMOVLE => todo!(),
            // Opcode::CMOVNA => todo!(),
            // Opcode::CMOVNB => todo!(),
            // Opcode::CMOVNO => todo!(),
            // Opcode::CMOVNP => todo!(),
            // Opcode::CMOVNS => todo!(),
            // Opcode::CMOVNZ => todo!(),
            // Opcode::CMOVO => todo!(),
            // Opcode::CMOVP => todo!(),
            // Opcode::CMOVS => todo!(),
            // Opcode::CMOVZ => todo!(),
            // Opcode::DIV => todo!(),
            // Opcode::IDIV => todo!(),
            // Opcode::MUL => todo!(),
            // Opcode::NEG => todo!(),
            // Opcode::NOT => todo!(),
            // Opcode::CMPXCHG => todo!(),
            // Opcode::SETO => todo!(),
            // Opcode::SETNO => todo!(),
            // Opcode::SETB => todo!(),
            // Opcode::SETAE => todo!(),
            // Opcode::SETZ => todo!(),
            // Opcode::SETNZ => todo!(),
            // Opcode::SETBE => todo!(),
            // Opcode::SETA => todo!(),
            // Opcode::SETS => todo!(),
            // Opcode::SETNS => todo!(),
            // Opcode::SETP => todo!(),
            // Opcode::SETNP => todo!(),
            // Opcode::SETL => todo!(),
            // Opcode::SETGE => todo!(),
            // Opcode::SETLE => todo!(),
            // Opcode::SETG => todo!(),
            // Opcode::CPUID => todo!(),
            // Opcode::UD0 => todo!(),
            // Opcode::UD1 => todo!(),
            // Opcode::UD2 => todo!(),
            // Opcode::WBINVD => todo!(),
            // Opcode::INVD => todo!(),
            // Opcode::SYSRET => todo!(),
            // Opcode::CLTS => todo!(),
            Opcode::SYSCALL => {
                // Argument order: rdi, rsi, rdx, r10, r8, r9
                let syscall = SyscallRequest {
                    process_id: self.process_id,
                    call_code: self.register_file.general_purpose_registers
                        [GeneralPurposeRegister::Rax as usize],
                    arguments: [
                        self.register_file.general_purpose_registers
                            [GeneralPurposeRegister::Rdi as usize],
                        self.register_file.general_purpose_registers
                            [GeneralPurposeRegister::Rsi as usize],
                        self.register_file.general_purpose_registers
                            [GeneralPurposeRegister::Rdx as usize],
                        self.register_file.general_purpose_registers
                            [GeneralPurposeRegister::R10 as usize],
                        self.register_file.general_purpose_registers
                            [GeneralPurposeRegister::R8 as usize],
                        self.register_file.general_purpose_registers
                            [GeneralPurposeRegister::R9 as usize],
                    ],
                };

                return Ok(StepResult::Syscall(syscall));
            }
            // Opcode::LSL => todo!(),
            // Opcode::LAR => todo!(),
            // Opcode::SGDT => todo!(),
            // Opcode::SIDT => todo!(),
            // Opcode::LGDT => todo!(),
            // Opcode::LIDT => todo!(),
            // Opcode::SMSW => todo!(),
            // Opcode::LMSW => todo!(),
            // Opcode::SWAPGS => todo!(),
            // Opcode::RDTSCP => todo!(),
            // Opcode::INVLPG => todo!(),
            // Opcode::FXSAVE => todo!(),
            // Opcode::FXRSTOR => todo!(),
            // Opcode::LDMXCSR => todo!(),
            // Opcode::STMXCSR => todo!(),
            // Opcode::XSAVE => todo!(),
            // Opcode::XRSTOR => todo!(),
            // Opcode::XSAVEOPT => todo!(),
            // Opcode::LFENCE => todo!(),
            // Opcode::MFENCE => todo!(),
            // Opcode::SFENCE => todo!(),
            // Opcode::CLFLUSH => todo!(),
            // Opcode::CLFLUSHOPT => todo!(),
            // Opcode::CLWB => todo!(),
            // Opcode::WRMSR => todo!(),
            // Opcode::RDTSC => todo!(),
            // Opcode::RDMSR => todo!(),
            // Opcode::RDPMC => todo!(),
            // Opcode::SLDT => todo!(),
            // Opcode::STR => todo!(),
            // Opcode::LLDT => todo!(),
            // Opcode::LTR => todo!(),
            // Opcode::VERR => todo!(),
            // Opcode::VERW => todo!(),
            // Opcode::CMC => todo!(),
            // Opcode::CLC => todo!(),
            // Opcode::STC => todo!(),
            // Opcode::CLI => todo!(),
            // Opcode::STI => todo!(),
            // Opcode::CLD => todo!(),
            // Opcode::STD => todo!(),
            // Opcode::JMPE => todo!(),
            // Opcode::POPCNT => todo!(),
            // Opcode::MOVDQU => todo!(),
            // Opcode::MOVDQA => todo!(),
            // Opcode::MOVQ => todo!(),
            // Opcode::CMPSS => todo!(),
            // Opcode::CMPSD => todo!(),
            // Opcode::UNPCKLPS => todo!(),
            // Opcode::UNPCKLPD => todo!(),
            // Opcode::UNPCKHPS => todo!(),
            // Opcode::UNPCKHPD => todo!(),
            // Opcode::PSHUFHW => todo!(),
            // Opcode::PSHUFLW => todo!(),
            // Opcode::MOVUPS => todo!(),
            // Opcode::MOVQ2DQ => todo!(),
            // Opcode::MOVDQ2Q => todo!(),
            // Opcode::RSQRTSS => todo!(),
            // Opcode::RCPSS => todo!(),
            // Opcode::ANDN => todo!(),
            // Opcode::BEXTR => todo!(),
            // Opcode::BLSI => todo!(),
            // Opcode::BLSMSK => todo!(),
            // Opcode::BLSR => todo!(),
            // Opcode::VMCLEAR => todo!(),
            // Opcode::VMXON => todo!(),
            // Opcode::VMCALL => todo!(),
            // Opcode::VMLAUNCH => todo!(),
            // Opcode::VMRESUME => todo!(),
            // Opcode::VMXOFF => todo!(),
            // Opcode::PCONFIG => todo!(),
            // Opcode::MONITOR => todo!(),
            // Opcode::MWAIT => todo!(),
            // Opcode::MONITORX => todo!(),
            // Opcode::MWAITX => todo!(),
            // Opcode::CLAC => todo!(),
            // Opcode::STAC => todo!(),
            // Opcode::ENCLS => todo!(),
            // Opcode::ENCLV => todo!(),
            // Opcode::XGETBV => todo!(),
            // Opcode::XSETBV => todo!(),
            // Opcode::VMFUNC => todo!(),
            // Opcode::XABORT => todo!(),
            // Opcode::XBEGIN => todo!(),
            // Opcode::XEND => todo!(),
            // Opcode::XTEST => todo!(),
            // Opcode::ENCLU => todo!(),
            // Opcode::RDPKRU => todo!(),
            // Opcode::WRPKRU => todo!(),
            // Opcode::RDPRU => todo!(),
            // Opcode::CLZERO => todo!(),
            // Opcode::RDSEED => todo!(),
            // Opcode::RDRAND => todo!(),
            // Opcode::ADDPS => todo!(),
            // Opcode::ADDPD => todo!(),
            // Opcode::ANDNPS => todo!(),
            // Opcode::ANDNPD => todo!(),
            // Opcode::ANDPS => todo!(),
            // Opcode::ANDPD => todo!(),
            // Opcode::BSWAP => todo!(),
            // Opcode::CMPPD => todo!(),
            // Opcode::CMPPS => todo!(),
            // Opcode::COMISD => todo!(),
            // Opcode::COMISS => todo!(),
            // Opcode::CVTDQ2PS => todo!(),
            // Opcode::CVTPI2PS => todo!(),
            // Opcode::CVTPI2PD => todo!(),
            // Opcode::CVTPS2PD => todo!(),
            // Opcode::CVTPS2PI => todo!(),
            // Opcode::CVTPD2PI => todo!(),
            // Opcode::CVTTPS2PI => todo!(),
            // Opcode::CVTTPD2PI => todo!(),
            // Opcode::CVTTPD2DQ => todo!(),
            // Opcode::DIVPS => todo!(),
            // Opcode::DIVPD => todo!(),
            // Opcode::EMMS => todo!(),
            // Opcode::GETSEC => todo!(),
            // Opcode::LFS => todo!(),
            // Opcode::LGS => todo!(),
            // Opcode::LSS => todo!(),
            // Opcode::MASKMOVQ => todo!(),
            // Opcode::MASKMOVDQU => todo!(),
            // Opcode::MAXPS => todo!(),
            // Opcode::MAXPD => todo!(),
            // Opcode::MINPS => todo!(),
            // Opcode::MINPD => todo!(),
            // Opcode::MOVAPS => todo!(),
            // Opcode::MOVAPD => todo!(),
            // Opcode::MOVD => todo!(),
            // Opcode::MOVLPS => todo!(),
            // Opcode::MOVLPD => todo!(),
            // Opcode::MOVHPS => todo!(),
            // Opcode::MOVHPD => todo!(),
            // Opcode::MOVLHPS => todo!(),
            // Opcode::MOVHLPS => todo!(),
            // Opcode::MOVUPD => todo!(),
            // Opcode::MOVMSKPS => todo!(),
            // Opcode::MOVMSKPD => todo!(),
            // Opcode::MOVNTI => todo!(),
            // Opcode::MOVNTPS => todo!(),
            // Opcode::MOVNTPD => todo!(),
            // Opcode::EXTRQ => todo!(),
            // Opcode::INSERTQ => todo!(),
            // Opcode::MOVNTSS => todo!(),
            // Opcode::MOVNTSD => todo!(),
            // Opcode::MOVNTQ => todo!(),
            // Opcode::MOVNTDQ => todo!(),
            // Opcode::MULPS => todo!(),
            // Opcode::MULPD => todo!(),
            // Opcode::ORPS => todo!(),
            // Opcode::ORPD => todo!(),
            // Opcode::PACKSSDW => todo!(),
            // Opcode::PACKSSWB => todo!(),
            // Opcode::PACKUSWB => todo!(),
            // Opcode::PADDB => todo!(),
            // Opcode::PADDD => todo!(),
            // Opcode::PADDQ => todo!(),
            // Opcode::PADDSB => todo!(),
            // Opcode::PADDSW => todo!(),
            // Opcode::PADDUSB => todo!(),
            // Opcode::PADDUSW => todo!(),
            // Opcode::PADDW => todo!(),
            // Opcode::PAND => todo!(),
            // Opcode::PANDN => todo!(),
            // Opcode::PAVGB => todo!(),
            // Opcode::PAVGW => todo!(),
            // Opcode::PCMPEQB => todo!(),
            // Opcode::PCMPEQD => todo!(),
            // Opcode::PCMPEQW => todo!(),
            // Opcode::PCMPGTB => todo!(),
            // Opcode::PCMPGTD => todo!(),
            // Opcode::PCMPGTW => todo!(),
            // Opcode::PINSRW => todo!(),
            // Opcode::PMADDWD => todo!(),
            // Opcode::PMAXSW => todo!(),
            // Opcode::PMAXUB => todo!(),
            // Opcode::PMINSW => todo!(),
            // Opcode::PMINUB => todo!(),
            // Opcode::PMOVMSKB => todo!(),
            // Opcode::PMULHUW => todo!(),
            // Opcode::PMULHW => todo!(),
            // Opcode::PMULLW => todo!(),
            // Opcode::PMULUDQ => todo!(),
            // Opcode::POR => todo!(),
            // Opcode::PSADBW => todo!(),
            // Opcode::PSHUFW => todo!(),
            // Opcode::PSHUFD => todo!(),
            // Opcode::PSLLD => todo!(),
            // Opcode::PSLLDQ => todo!(),
            // Opcode::PSLLQ => todo!(),
            // Opcode::PSLLW => todo!(),
            // Opcode::PSRAD => todo!(),
            // Opcode::PSRAW => todo!(),
            // Opcode::PSRLD => todo!(),
            // Opcode::PSRLDQ => todo!(),
            // Opcode::PSRLQ => todo!(),
            // Opcode::PSRLW => todo!(),
            // Opcode::PSUBB => todo!(),
            // Opcode::PSUBD => todo!(),
            // Opcode::PSUBQ => todo!(),
            // Opcode::PSUBSB => todo!(),
            // Opcode::PSUBSW => todo!(),
            // Opcode::PSUBUSB => todo!(),
            // Opcode::PSUBUSW => todo!(),
            // Opcode::PSUBW => todo!(),
            // Opcode::PUNPCKHBW => todo!(),
            // Opcode::PUNPCKHDQ => todo!(),
            // Opcode::PUNPCKHWD => todo!(),
            // Opcode::PUNPCKLBW => todo!(),
            // Opcode::PUNPCKLDQ => todo!(),
            // Opcode::PUNPCKLWD => todo!(),
            // Opcode::PUNPCKLQDQ => todo!(),
            // Opcode::PUNPCKHQDQ => todo!(),
            // Opcode::PXOR => todo!(),
            // Opcode::RCPPS => todo!(),
            // Opcode::RSM => todo!(),
            // Opcode::RSQRTPS => todo!(),
            // Opcode::SHLD => todo!(),
            // Opcode::SHUFPD => todo!(),
            // Opcode::SHUFPS => todo!(),
            // Opcode::SLHD => todo!(),
            // Opcode::SQRTPS => todo!(),
            // Opcode::SQRTPD => todo!(),
            // Opcode::SUBPS => todo!(),
            // Opcode::SUBPD => todo!(),
            // Opcode::SYSENTER => todo!(),
            // Opcode::SYSEXIT => todo!(),
            // Opcode::UCOMISD => todo!(),
            // Opcode::UCOMISS => todo!(),
            // Opcode::VMREAD => todo!(),
            // Opcode::VMWRITE => todo!(),
            // Opcode::XORPS => todo!(),
            // Opcode::XORPD => todo!(),
            // Opcode::VMOVDDUP => todo!(),
            // Opcode::VPSHUFLW => todo!(),
            // Opcode::VPSHUFHW => todo!(),
            // Opcode::VHADDPS => todo!(),
            // Opcode::VHSUBPS => todo!(),
            // Opcode::VADDSUBPS => todo!(),
            // Opcode::VCVTPD2DQ => todo!(),
            // Opcode::VLDDQU => todo!(),
            // Opcode::VCOMISD => todo!(),
            // Opcode::VCOMISS => todo!(),
            // Opcode::VUCOMISD => todo!(),
            // Opcode::VUCOMISS => todo!(),
            // Opcode::VADDPD => todo!(),
            // Opcode::VADDPS => todo!(),
            // Opcode::VADDSD => todo!(),
            // Opcode::VADDSS => todo!(),
            // Opcode::VADDSUBPD => todo!(),
            // Opcode::VAESDEC => todo!(),
            // Opcode::VAESDECLAST => todo!(),
            // Opcode::VAESENC => todo!(),
            // Opcode::VAESENCLAST => todo!(),
            // Opcode::VAESIMC => todo!(),
            // Opcode::VAESKEYGENASSIST => todo!(),
            // Opcode::VBLENDPD => todo!(),
            // Opcode::VBLENDPS => todo!(),
            // Opcode::VBLENDVPD => todo!(),
            // Opcode::VBLENDVPS => todo!(),
            // Opcode::VBROADCASTF128 => todo!(),
            // Opcode::VBROADCASTI128 => todo!(),
            // Opcode::VBROADCASTSD => todo!(),
            // Opcode::VBROADCASTSS => todo!(),
            // Opcode::VCMPSD => todo!(),
            // Opcode::VCMPSS => todo!(),
            // Opcode::VCMPPD => todo!(),
            // Opcode::VCMPPS => todo!(),
            // Opcode::VCVTDQ2PD => todo!(),
            // Opcode::VCVTDQ2PS => todo!(),
            // Opcode::VCVTPD2PS => todo!(),
            // Opcode::VCVTPH2PS => todo!(),
            // Opcode::VCVTPS2DQ => todo!(),
            // Opcode::VCVTPS2PD => todo!(),
            // Opcode::VCVTSS2SD => todo!(),
            // Opcode::VCVTSI2SS => todo!(),
            // Opcode::VCVTSI2SD => todo!(),
            // Opcode::VCVTSD2SI => todo!(),
            // Opcode::VCVTSD2SS => todo!(),
            // Opcode::VCVTPS2PH => todo!(),
            // Opcode::VCVTSS2SI => todo!(),
            // Opcode::VCVTTPD2DQ => todo!(),
            // Opcode::VCVTTPS2DQ => todo!(),
            // Opcode::VCVTTSS2SI => todo!(),
            // Opcode::VCVTTSD2SI => todo!(),
            // Opcode::VDIVPD => todo!(),
            // Opcode::VDIVPS => todo!(),
            // Opcode::VDIVSD => todo!(),
            // Opcode::VDIVSS => todo!(),
            // Opcode::VDPPD => todo!(),
            // Opcode::VDPPS => todo!(),
            // Opcode::VEXTRACTF128 => todo!(),
            // Opcode::VEXTRACTI128 => todo!(),
            // Opcode::VEXTRACTPS => todo!(),
            // Opcode::VFMADD132PD => todo!(),
            // Opcode::VFMADD132PS => todo!(),
            // Opcode::VFMADD132SD => todo!(),
            // Opcode::VFMADD132SS => todo!(),
            // Opcode::VFMADD213PD => todo!(),
            // Opcode::VFMADD213PS => todo!(),
            // Opcode::VFMADD213SD => todo!(),
            // Opcode::VFMADD213SS => todo!(),
            // Opcode::VFMADD231PD => todo!(),
            // Opcode::VFMADD231PS => todo!(),
            // Opcode::VFMADD231SD => todo!(),
            // Opcode::VFMADD231SS => todo!(),
            // Opcode::VFMADDSUB132PD => todo!(),
            // Opcode::VFMADDSUB132PS => todo!(),
            // Opcode::VFMADDSUB213PD => todo!(),
            // Opcode::VFMADDSUB213PS => todo!(),
            // Opcode::VFMADDSUB231PD => todo!(),
            // Opcode::VFMADDSUB231PS => todo!(),
            // Opcode::VFMSUB132PD => todo!(),
            // Opcode::VFMSUB132PS => todo!(),
            // Opcode::VFMSUB132SD => todo!(),
            // Opcode::VFMSUB132SS => todo!(),
            // Opcode::VFMSUB213PD => todo!(),
            // Opcode::VFMSUB213PS => todo!(),
            // Opcode::VFMSUB213SD => todo!(),
            // Opcode::VFMSUB213SS => todo!(),
            // Opcode::VFMSUB231PD => todo!(),
            // Opcode::VFMSUB231PS => todo!(),
            // Opcode::VFMSUB231SD => todo!(),
            // Opcode::VFMSUB231SS => todo!(),
            // Opcode::VFMSUBADD132PD => todo!(),
            // Opcode::VFMSUBADD132PS => todo!(),
            // Opcode::VFMSUBADD213PD => todo!(),
            // Opcode::VFMSUBADD213PS => todo!(),
            // Opcode::VFMSUBADD231PD => todo!(),
            // Opcode::VFMSUBADD231PS => todo!(),
            // Opcode::VFNMADD132PD => todo!(),
            // Opcode::VFNMADD132PS => todo!(),
            // Opcode::VFNMADD132SD => todo!(),
            // Opcode::VFNMADD132SS => todo!(),
            // Opcode::VFNMADD213PD => todo!(),
            // Opcode::VFNMADD213PS => todo!(),
            // Opcode::VFNMADD213SD => todo!(),
            // Opcode::VFNMADD213SS => todo!(),
            // Opcode::VFNMADD231PD => todo!(),
            // Opcode::VFNMADD231PS => todo!(),
            // Opcode::VFNMADD231SD => todo!(),
            // Opcode::VFNMADD231SS => todo!(),
            // Opcode::VFNMSUB132PD => todo!(),
            // Opcode::VFNMSUB132PS => todo!(),
            // Opcode::VFNMSUB132SD => todo!(),
            // Opcode::VFNMSUB132SS => todo!(),
            // Opcode::VFNMSUB213PD => todo!(),
            // Opcode::VFNMSUB213PS => todo!(),
            // Opcode::VFNMSUB213SD => todo!(),
            // Opcode::VFNMSUB213SS => todo!(),
            // Opcode::VFNMSUB231PD => todo!(),
            // Opcode::VFNMSUB231PS => todo!(),
            // Opcode::VFNMSUB231SD => todo!(),
            // Opcode::VFNMSUB231SS => todo!(),
            // Opcode::VGATHERDPD => todo!(),
            // Opcode::VGATHERDPS => todo!(),
            // Opcode::VGATHERQPD => todo!(),
            // Opcode::VGATHERQPS => todo!(),
            // Opcode::VHADDPD => todo!(),
            // Opcode::VHSUBPD => todo!(),
            // Opcode::VINSERTF128 => todo!(),
            // Opcode::VINSERTI128 => todo!(),
            // Opcode::VINSERTPS => todo!(),
            // Opcode::VMASKMOVDQU => todo!(),
            // Opcode::VMASKMOVPD => todo!(),
            // Opcode::VMASKMOVPS => todo!(),
            // Opcode::VMAXPD => todo!(),
            // Opcode::VMAXPS => todo!(),
            // Opcode::VMAXSD => todo!(),
            // Opcode::VMAXSS => todo!(),
            // Opcode::VMINPD => todo!(),
            // Opcode::VMINPS => todo!(),
            // Opcode::VMINSD => todo!(),
            // Opcode::VMINSS => todo!(),
            // Opcode::VMOVAPD => todo!(),
            // Opcode::VMOVAPS => todo!(),
            // Opcode::VMOVD => todo!(),
            // Opcode::VMOVDQA => todo!(),
            // Opcode::VMOVDQU => todo!(),
            // Opcode::VMOVHLPS => todo!(),
            // Opcode::VMOVHPD => todo!(),
            // Opcode::VMOVHPS => todo!(),
            // Opcode::VMOVLHPS => todo!(),
            // Opcode::VMOVLPD => todo!(),
            // Opcode::VMOVLPS => todo!(),
            // Opcode::VMOVMSKPD => todo!(),
            // Opcode::VMOVMSKPS => todo!(),
            // Opcode::VMOVNTDQ => todo!(),
            // Opcode::VMOVNTDQA => todo!(),
            // Opcode::VMOVNTPD => todo!(),
            // Opcode::VMOVNTPS => todo!(),
            // Opcode::VMOVQ => todo!(),
            // Opcode::VMOVSS => todo!(),
            // Opcode::VMOVSD => todo!(),
            // Opcode::VMOVSHDUP => todo!(),
            // Opcode::VMOVSLDUP => todo!(),
            // Opcode::VMOVUPD => todo!(),
            // Opcode::VMOVUPS => todo!(),
            // Opcode::VMPSADBW => todo!(),
            // Opcode::VMULPD => todo!(),
            // Opcode::VMULPS => todo!(),
            // Opcode::VMULSD => todo!(),
            // Opcode::VMULSS => todo!(),
            // Opcode::VPABSB => todo!(),
            // Opcode::VPABSD => todo!(),
            // Opcode::VPABSW => todo!(),
            // Opcode::VPACKSSDW => todo!(),
            // Opcode::VPACKUSDW => todo!(),
            // Opcode::VPACKSSWB => todo!(),
            // Opcode::VPACKUSWB => todo!(),
            // Opcode::VPADDB => todo!(),
            // Opcode::VPADDD => todo!(),
            // Opcode::VPADDQ => todo!(),
            // Opcode::VPADDSB => todo!(),
            // Opcode::VPADDSW => todo!(),
            // Opcode::VPADDUSB => todo!(),
            // Opcode::VPADDUSW => todo!(),
            // Opcode::VPADDW => todo!(),
            // Opcode::VPALIGNR => todo!(),
            // Opcode::VANDPD => todo!(),
            // Opcode::VANDPS => todo!(),
            // Opcode::VORPD => todo!(),
            // Opcode::VORPS => todo!(),
            // Opcode::VANDNPD => todo!(),
            // Opcode::VANDNPS => todo!(),
            // Opcode::VPAND => todo!(),
            // Opcode::VPANDN => todo!(),
            // Opcode::VPAVGB => todo!(),
            // Opcode::VPAVGW => todo!(),
            // Opcode::VPBLENDD => todo!(),
            // Opcode::VPBLENDVB => todo!(),
            // Opcode::VPBLENDW => todo!(),
            // Opcode::VPBROADCASTB => todo!(),
            // Opcode::VPBROADCASTD => todo!(),
            // Opcode::VPBROADCASTQ => todo!(),
            // Opcode::VPBROADCASTW => todo!(),
            // Opcode::VPCLMULQDQ => todo!(),
            // Opcode::VPCMPEQB => todo!(),
            // Opcode::VPCMPEQD => todo!(),
            // Opcode::VPCMPEQQ => todo!(),
            // Opcode::VPCMPEQW => todo!(),
            // Opcode::VPCMPGTB => todo!(),
            // Opcode::VPCMPGTD => todo!(),
            // Opcode::VPCMPGTQ => todo!(),
            // Opcode::VPCMPGTW => todo!(),
            // Opcode::VPCMPESTRI => todo!(),
            // Opcode::VPCMPESTRM => todo!(),
            // Opcode::VPCMPISTRI => todo!(),
            // Opcode::VPCMPISTRM => todo!(),
            // Opcode::VPERM2F128 => todo!(),
            // Opcode::VPERM2I128 => todo!(),
            // Opcode::VPERMD => todo!(),
            // Opcode::VPERMILPD => todo!(),
            // Opcode::VPERMILPS => todo!(),
            // Opcode::VPERMPD => todo!(),
            // Opcode::VPERMPS => todo!(),
            // Opcode::VPERMQ => todo!(),
            // Opcode::VPEXTRB => todo!(),
            // Opcode::VPEXTRD => todo!(),
            // Opcode::VPEXTRQ => todo!(),
            // Opcode::VPEXTRW => todo!(),
            // Opcode::VPGATHERDD => todo!(),
            // Opcode::VPGATHERDQ => todo!(),
            // Opcode::VPGATHERQD => todo!(),
            // Opcode::VPGATHERQQ => todo!(),
            // Opcode::VPHADDD => todo!(),
            // Opcode::VPHADDSW => todo!(),
            // Opcode::VPHADDW => todo!(),
            // Opcode::VPMADDUBSW => todo!(),
            // Opcode::VPHMINPOSUW => todo!(),
            // Opcode::VPHSUBD => todo!(),
            // Opcode::VPHSUBSW => todo!(),
            // Opcode::VPHSUBW => todo!(),
            // Opcode::VPINSRB => todo!(),
            // Opcode::VPINSRD => todo!(),
            // Opcode::VPINSRQ => todo!(),
            // Opcode::VPINSRW => todo!(),
            // Opcode::VPMADDWD => todo!(),
            // Opcode::VPMASKMOVD => todo!(),
            // Opcode::VPMASKMOVQ => todo!(),
            // Opcode::VPMAXSB => todo!(),
            // Opcode::VPMAXSD => todo!(),
            // Opcode::VPMAXSW => todo!(),
            // Opcode::VPMAXUB => todo!(),
            // Opcode::VPMAXUW => todo!(),
            // Opcode::VPMAXUD => todo!(),
            // Opcode::VPMINSB => todo!(),
            // Opcode::VPMINSW => todo!(),
            // Opcode::VPMINSD => todo!(),
            // Opcode::VPMINUB => todo!(),
            // Opcode::VPMINUW => todo!(),
            // Opcode::VPMINUD => todo!(),
            // Opcode::VPMOVMSKB => todo!(),
            // Opcode::VPMOVSXBD => todo!(),
            // Opcode::VPMOVSXBQ => todo!(),
            // Opcode::VPMOVSXBW => todo!(),
            // Opcode::VPMOVSXDQ => todo!(),
            // Opcode::VPMOVSXWD => todo!(),
            // Opcode::VPMOVSXWQ => todo!(),
            // Opcode::VPMOVZXBD => todo!(),
            // Opcode::VPMOVZXBQ => todo!(),
            // Opcode::VPMOVZXBW => todo!(),
            // Opcode::VPMOVZXDQ => todo!(),
            // Opcode::VPMOVZXWD => todo!(),
            // Opcode::VPMOVZXWQ => todo!(),
            // Opcode::VPMULDQ => todo!(),
            // Opcode::VPMULHRSW => todo!(),
            // Opcode::VPMULHUW => todo!(),
            // Opcode::VPMULHW => todo!(),
            // Opcode::VPMULLQ => todo!(),
            // Opcode::VPMULLD => todo!(),
            // Opcode::VPMULLW => todo!(),
            // Opcode::VPMULUDQ => todo!(),
            // Opcode::VPOR => todo!(),
            // Opcode::VPSADBW => todo!(),
            // Opcode::VPSHUFB => todo!(),
            // Opcode::VPSHUFD => todo!(),
            // Opcode::VPSIGNB => todo!(),
            // Opcode::VPSIGND => todo!(),
            // Opcode::VPSIGNW => todo!(),
            // Opcode::VPSLLD => todo!(),
            // Opcode::VPSLLDQ => todo!(),
            // Opcode::VPSLLQ => todo!(),
            // Opcode::VPSLLVD => todo!(),
            // Opcode::VPSLLVQ => todo!(),
            // Opcode::VPSLLW => todo!(),
            // Opcode::VPSRAD => todo!(),
            // Opcode::VPSRAVD => todo!(),
            // Opcode::VPSRAW => todo!(),
            // Opcode::VPSRLD => todo!(),
            // Opcode::VPSRLDQ => todo!(),
            // Opcode::VPSRLQ => todo!(),
            // Opcode::VPSRLVD => todo!(),
            // Opcode::VPSRLVQ => todo!(),
            // Opcode::VPSRLW => todo!(),
            // Opcode::VPSUBB => todo!(),
            // Opcode::VPSUBD => todo!(),
            // Opcode::VPSUBQ => todo!(),
            // Opcode::VPSUBSB => todo!(),
            // Opcode::VPSUBSW => todo!(),
            // Opcode::VPSUBUSB => todo!(),
            // Opcode::VPSUBUSW => todo!(),
            // Opcode::VPSUBW => todo!(),
            // Opcode::VPTEST => todo!(),
            // Opcode::VPUNPCKHBW => todo!(),
            // Opcode::VPUNPCKHDQ => todo!(),
            // Opcode::VPUNPCKHQDQ => todo!(),
            // Opcode::VPUNPCKHWD => todo!(),
            // Opcode::VPUNPCKLBW => todo!(),
            // Opcode::VPUNPCKLDQ => todo!(),
            // Opcode::VPUNPCKLQDQ => todo!(),
            // Opcode::VPUNPCKLWD => todo!(),
            // Opcode::VPXOR => todo!(),
            // Opcode::VRCPPS => todo!(),
            // Opcode::VROUNDPD => todo!(),
            // Opcode::VROUNDPS => todo!(),
            // Opcode::VROUNDSD => todo!(),
            // Opcode::VROUNDSS => todo!(),
            // Opcode::VRSQRTPS => todo!(),
            // Opcode::VRSQRTSS => todo!(),
            // Opcode::VRCPSS => todo!(),
            // Opcode::VSHUFPD => todo!(),
            // Opcode::VSHUFPS => todo!(),
            // Opcode::VSQRTPD => todo!(),
            // Opcode::VSQRTPS => todo!(),
            // Opcode::VSQRTSS => todo!(),
            // Opcode::VSQRTSD => todo!(),
            // Opcode::VSUBPD => todo!(),
            // Opcode::VSUBPS => todo!(),
            // Opcode::VSUBSD => todo!(),
            // Opcode::VSUBSS => todo!(),
            // Opcode::VTESTPD => todo!(),
            // Opcode::VTESTPS => todo!(),
            // Opcode::VUNPCKHPD => todo!(),
            // Opcode::VUNPCKHPS => todo!(),
            // Opcode::VUNPCKLPD => todo!(),
            // Opcode::VUNPCKLPS => todo!(),
            // Opcode::VXORPD => todo!(),
            // Opcode::VXORPS => todo!(),
            // Opcode::VZEROUPPER => todo!(),
            // Opcode::VZEROALL => todo!(),
            // Opcode::VLDMXCSR => todo!(),
            // Opcode::VSTMXCSR => todo!(),
            // Opcode::PCLMULQDQ => todo!(),
            // Opcode::AESKEYGENASSIST => todo!(),
            // Opcode::AESIMC => todo!(),
            // Opcode::AESENC => todo!(),
            // Opcode::AESENCLAST => todo!(),
            // Opcode::AESDEC => todo!(),
            // Opcode::AESDECLAST => todo!(),
            // Opcode::PCMPGTQ => todo!(),
            // Opcode::PCMPISTRM => todo!(),
            // Opcode::PCMPISTRI => todo!(),
            // Opcode::PCMPESTRI => todo!(),
            // Opcode::PACKUSDW => todo!(),
            // Opcode::PCMPESTRM => todo!(),
            // Opcode::PCMPEQQ => todo!(),
            // Opcode::PTEST => todo!(),
            // Opcode::PHMINPOSUW => todo!(),
            // Opcode::DPPS => todo!(),
            // Opcode::DPPD => todo!(),
            // Opcode::MPSADBW => todo!(),
            // Opcode::PMOVZXDQ => todo!(),
            // Opcode::PMOVSXDQ => todo!(),
            // Opcode::PMOVZXBD => todo!(),
            // Opcode::PMOVSXBD => todo!(),
            // Opcode::PMOVZXWQ => todo!(),
            // Opcode::PMOVSXWQ => todo!(),
            // Opcode::PMOVZXBQ => todo!(),
            // Opcode::PMOVSXBQ => todo!(),
            // Opcode::PMOVSXWD => todo!(),
            // Opcode::PMOVZXWD => todo!(),
            // Opcode::PEXTRQ => todo!(),
            // Opcode::PEXTRD => todo!(),
            // Opcode::PEXTRW => todo!(),
            // Opcode::PEXTRB => todo!(),
            // Opcode::PMOVSXBW => todo!(),
            // Opcode::PMOVZXBW => todo!(),
            // Opcode::PINSRQ => todo!(),
            // Opcode::PINSRD => todo!(),
            // Opcode::PINSRB => todo!(),
            // Opcode::EXTRACTPS => todo!(),
            // Opcode::INSERTPS => todo!(),
            // Opcode::ROUNDSS => todo!(),
            // Opcode::ROUNDSD => todo!(),
            // Opcode::ROUNDPS => todo!(),
            // Opcode::ROUNDPD => todo!(),
            // Opcode::PMAXSB => todo!(),
            // Opcode::PMAXSD => todo!(),
            // Opcode::PMAXUW => todo!(),
            // Opcode::PMAXUD => todo!(),
            // Opcode::PMINSD => todo!(),
            // Opcode::PMINSB => todo!(),
            // Opcode::PMINUD => todo!(),
            // Opcode::PMINUW => todo!(),
            // Opcode::BLENDW => todo!(),
            // Opcode::PBLENDVB => todo!(),
            // Opcode::PBLENDW => todo!(),
            // Opcode::BLENDVPS => todo!(),
            // Opcode::BLENDVPD => todo!(),
            // Opcode::BLENDPS => todo!(),
            // Opcode::BLENDPD => todo!(),
            // Opcode::PMULDQ => todo!(),
            // Opcode::MOVNTDQA => todo!(),
            // Opcode::PMULLD => todo!(),
            // Opcode::PALIGNR => todo!(),
            // Opcode::PSIGNW => todo!(),
            // Opcode::PSIGND => todo!(),
            // Opcode::PSIGNB => todo!(),
            // Opcode::PSHUFB => todo!(),
            // Opcode::PMULHRSW => todo!(),
            // Opcode::PMADDUBSW => todo!(),
            // Opcode::PABSD => todo!(),
            // Opcode::PABSW => todo!(),
            // Opcode::PABSB => todo!(),
            // Opcode::PHSUBSW => todo!(),
            // Opcode::PHSUBW => todo!(),
            // Opcode::PHSUBD => todo!(),
            // Opcode::PHADDD => todo!(),
            // Opcode::PHADDSW => todo!(),
            // Opcode::PHADDW => todo!(),
            // Opcode::HSUBPD => todo!(),
            // Opcode::HADDPD => todo!(),
            // Opcode::SHA1RNDS4 => todo!(),
            // Opcode::SHA1NEXTE => todo!(),
            // Opcode::SHA1MSG1 => todo!(),
            // Opcode::SHA1MSG2 => todo!(),
            // Opcode::SHA256RNDS2 => todo!(),
            // Opcode::SHA256MSG1 => todo!(),
            // Opcode::SHA256MSG2 => todo!(),
            // Opcode::LZCNT => todo!(),
            // Opcode::CLGI => todo!(),
            // Opcode::STGI => todo!(),
            // Opcode::SKINIT => todo!(),
            // Opcode::VMLOAD => todo!(),
            // Opcode::VMMCALL => todo!(),
            // Opcode::VMSAVE => todo!(),
            // Opcode::VMRUN => todo!(),
            // Opcode::INVLPGA => todo!(),
            // Opcode::INVLPGB => todo!(),
            // Opcode::TLBSYNC => todo!(),
            // Opcode::MOVBE => todo!(),
            // Opcode::ADCX => todo!(),
            // Opcode::ADOX => todo!(),
            // Opcode::PREFETCHW => todo!(),
            // Opcode::RDPID => todo!(),
            // Opcode::CMPXCHG8B => todo!(),
            // Opcode::CMPXCHG16B => todo!(),
            // Opcode::VMPTRLD => todo!(),
            // Opcode::VMPTRST => todo!(),
            // Opcode::BZHI => todo!(),
            // Opcode::MULX => todo!(),
            // Opcode::SHLX => todo!(),
            // Opcode::SHRX => todo!(),
            // Opcode::SARX => todo!(),
            // Opcode::PDEP => todo!(),
            // Opcode::PEXT => todo!(),
            // Opcode::RORX => todo!(),
            // Opcode::XRSTORS => todo!(),
            // Opcode::XRSTORS64 => todo!(),
            // Opcode::XSAVEC => todo!(),
            // Opcode::XSAVEC64 => todo!(),
            // Opcode::XSAVES => todo!(),
            // Opcode::XSAVES64 => todo!(),
            // Opcode::RDFSBASE => todo!(),
            // Opcode::RDGSBASE => todo!(),
            // Opcode::WRFSBASE => todo!(),
            // Opcode::WRGSBASE => todo!(),
            // Opcode::CRC32 => todo!(),
            // Opcode::SALC => todo!(),
            // Opcode::XLAT => todo!(),
            // Opcode::F2XM1 => todo!(),
            // Opcode::FABS => todo!(),
            // Opcode::FADD => todo!(),
            // Opcode::FADDP => todo!(),
            // Opcode::FBLD => todo!(),
            // Opcode::FBSTP => todo!(),
            // Opcode::FCHS => todo!(),
            // Opcode::FCMOVB => todo!(),
            // Opcode::FCMOVBE => todo!(),
            // Opcode::FCMOVE => todo!(),
            // Opcode::FCMOVNB => todo!(),
            // Opcode::FCMOVNBE => todo!(),
            // Opcode::FCMOVNE => todo!(),
            // Opcode::FCMOVNU => todo!(),
            // Opcode::FCMOVU => todo!(),
            // Opcode::FCOM => todo!(),
            // Opcode::FCOMI => todo!(),
            // Opcode::FCOMIP => todo!(),
            // Opcode::FCOMP => todo!(),
            // Opcode::FCOMPP => todo!(),
            // Opcode::FCOS => todo!(),
            // Opcode::FDECSTP => todo!(),
            // Opcode::FDISI8087_NOP => todo!(),
            // Opcode::FDIV => todo!(),
            // Opcode::FDIVP => todo!(),
            // Opcode::FDIVR => todo!(),
            // Opcode::FDIVRP => todo!(),
            // Opcode::FENI8087_NOP => todo!(),
            // Opcode::FFREE => todo!(),
            // Opcode::FFREEP => todo!(),
            // Opcode::FIADD => todo!(),
            // Opcode::FICOM => todo!(),
            // Opcode::FICOMP => todo!(),
            // Opcode::FIDIV => todo!(),
            // Opcode::FIDIVR => todo!(),
            // Opcode::FILD => todo!(),
            // Opcode::FIMUL => todo!(),
            // Opcode::FINCSTP => todo!(),
            // Opcode::FIST => todo!(),
            // Opcode::FISTP => todo!(),
            // Opcode::FISTTP => todo!(),
            // Opcode::FISUB => todo!(),
            // Opcode::FISUBR => todo!(),
            // Opcode::FLD => todo!(),
            // Opcode::FLD1 => todo!(),
            // Opcode::FLDCW => todo!(),
            // Opcode::FLDENV => todo!(),
            // Opcode::FLDL2E => todo!(),
            // Opcode::FLDL2T => todo!(),
            // Opcode::FLDLG2 => todo!(),
            // Opcode::FLDLN2 => todo!(),
            // Opcode::FLDPI => todo!(),
            // Opcode::FLDZ => todo!(),
            // Opcode::FMUL => todo!(),
            // Opcode::FMULP => todo!(),
            // Opcode::FNCLEX => todo!(),
            // Opcode::FNINIT => todo!(),
            // Opcode::FNOP => todo!(),
            // Opcode::FNSAVE => todo!(),
            // Opcode::FNSTCW => todo!(),
            // Opcode::FNSTENV => todo!(),
            // Opcode::FNSTOR => todo!(),
            // Opcode::FNSTSW => todo!(),
            // Opcode::FPATAN => todo!(),
            // Opcode::FPREM => todo!(),
            // Opcode::FPREM1 => todo!(),
            // Opcode::FPTAN => todo!(),
            // Opcode::FRNDINT => todo!(),
            // Opcode::FRSTOR => todo!(),
            // Opcode::FSCALE => todo!(),
            // Opcode::FSETPM287_NOP => todo!(),
            // Opcode::FSIN => todo!(),
            // Opcode::FSINCOS => todo!(),
            // Opcode::FSQRT => todo!(),
            // Opcode::FST => todo!(),
            // Opcode::FSTP => todo!(),
            // Opcode::FSTPNCE => todo!(),
            // Opcode::FSUB => todo!(),
            // Opcode::FSUBP => todo!(),
            // Opcode::FSUBR => todo!(),
            // Opcode::FSUBRP => todo!(),
            // Opcode::FTST => todo!(),
            // Opcode::FUCOM => todo!(),
            // Opcode::FUCOMI => todo!(),
            // Opcode::FUCOMIP => todo!(),
            // Opcode::FUCOMP => todo!(),
            // Opcode::FUCOMPP => todo!(),
            // Opcode::FXAM => todo!(),
            // Opcode::FXCH => todo!(),
            // Opcode::FXTRACT => todo!(),
            // Opcode::FYL2X => todo!(),
            // Opcode::FYL2XP1 => todo!(),
            // Opcode::LOOPNZ => todo!(),
            // Opcode::LOOPZ => todo!(),
            // Opcode::LOOP => todo!(),
            // Opcode::JRCXZ => todo!(),
            // Opcode::MOVDIR64B => todo!(),
            // Opcode::MOVDIRI => todo!(),
            // Opcode::AESDEC128KL => todo!(),
            // Opcode::AESDEC256KL => todo!(),
            // Opcode::AESDECWIDE128KL => todo!(),
            // Opcode::AESDECWIDE256KL => todo!(),
            // Opcode::AESENC128KL => todo!(),
            // Opcode::AESENC256KL => todo!(),
            // Opcode::AESENCWIDE128KL => todo!(),
            // Opcode::AESENCWIDE256KL => todo!(),
            // Opcode::ENCODEKEY128 => todo!(),
            // Opcode::ENCODEKEY256 => todo!(),
            // Opcode::LOADIWKEY => todo!(),
            // Opcode::HRESET => todo!(),
            // Opcode::FEMMS => todo!(),
            // Opcode::PI2FW => todo!(),
            // Opcode::PI2FD => todo!(),
            // Opcode::PF2IW => todo!(),
            // Opcode::PF2ID => todo!(),
            // Opcode::PMULHRW => todo!(),
            // Opcode::PFCMPGE => todo!(),
            // Opcode::PFMIN => todo!(),
            // Opcode::PFRCP => todo!(),
            // Opcode::PFRSQRT => todo!(),
            // Opcode::PFSUB => todo!(),
            // Opcode::PFADD => todo!(),
            // Opcode::PFCMPGT => todo!(),
            // Opcode::PFMAX => todo!(),
            // Opcode::PFRCPIT1 => todo!(),
            // Opcode::PFRSQIT1 => todo!(),
            // Opcode::PFSUBR => todo!(),
            // Opcode::PFACC => todo!(),
            // Opcode::PFCMPEQ => todo!(),
            // Opcode::PFMUL => todo!(),
            // Opcode::PFMULHRW => todo!(),
            // Opcode::PFRCPIT2 => todo!(),
            // Opcode::PFNACC => todo!(),
            // Opcode::PFPNACC => todo!(),
            // Opcode::PSWAPD => todo!(),
            // Opcode::PAVGUSB => todo!(),
            // Opcode::ENQCMD => todo!(),
            // Opcode::ENQCMDS => todo!(),
            // Opcode::INVEPT => todo!(),
            // Opcode::INVVPID => todo!(),
            // Opcode::INVPCID => todo!(),
            // Opcode::PTWRITE => todo!(),
            // Opcode::GF2P8AFFINEQB => todo!(),
            // Opcode::GF2P8AFFINEINVQB => todo!(),
            // Opcode::GF2P8MULB => todo!(),
            // Opcode::WRUSS => todo!(),
            // Opcode::WRSS => todo!(),
            // Opcode::INCSSP => todo!(),
            // Opcode::SAVEPREVSSP => todo!(),
            // Opcode::SETSSBSY => todo!(),
            // Opcode::CLRSSBSY => todo!(),
            // Opcode::RSTORSSP => todo!(),
            Opcode::ENDBR64 => {
                // End of branch marker.
                // It's a sort of landing pad for jump instructions, so that we can gracefully fail on an invalid jump.
                // It's perfectly valid to implement it as a noop.
            }
            // Opcode::ENDBR32 => todo!(),
            // Opcode::TDCALL => todo!(),
            // Opcode::SEAMRET => todo!(),
            // Opcode::SEAMOPS => todo!(),
            // Opcode::SEAMCALL => todo!(),
            // Opcode::TPAUSE => todo!(),
            // Opcode::UMONITOR => todo!(),
            // Opcode::UMWAIT => todo!(),
            // Opcode::UIRET => todo!(),
            // Opcode::TESTUI => todo!(),
            // Opcode::CLUI => todo!(),
            // Opcode::STUI => todo!(),
            // Opcode::SENDUIPI => todo!(),
            // Opcode::XSUSLDTRK => todo!(),
            // Opcode::XRESLDTRK => todo!(),
            // Opcode::VALIGND => todo!(),
            // Opcode::VALIGNQ => todo!(),
            // Opcode::VBLENDMPD => todo!(),
            // Opcode::VBLENDMPS => todo!(),
            // Opcode::VCOMPRESSPD => todo!(),
            // Opcode::VCOMPRESSPS => todo!(),
            // Opcode::VCVTPD2UDQ => todo!(),
            // Opcode::VCVTTPD2UDQ => todo!(),
            // Opcode::VCVTPS2UDQ => todo!(),
            // Opcode::VCVTTPS2UDQ => todo!(),
            // Opcode::VCVTQQ2PD => todo!(),
            // Opcode::VCVTQQ2PS => todo!(),
            // Opcode::VCVTSD2USI => todo!(),
            // Opcode::VCVTTSD2USI => todo!(),
            // Opcode::VCVTSS2USI => todo!(),
            // Opcode::VCVTTSS2USI => todo!(),
            // Opcode::VCVTUDQ2PD => todo!(),
            // Opcode::VCVTUDQ2PS => todo!(),
            // Opcode::VCVTUSI2USD => todo!(),
            // Opcode::VCVTUSI2USS => todo!(),
            // Opcode::VEXPANDPD => todo!(),
            // Opcode::VEXPANDPS => todo!(),
            // Opcode::VEXTRACTF32X4 => todo!(),
            // Opcode::VEXTRACTF64X4 => todo!(),
            // Opcode::VEXTRACTI32X4 => todo!(),
            // Opcode::VEXTRACTI64X4 => todo!(),
            // Opcode::VFIXUPIMMPD => todo!(),
            // Opcode::VFIXUPIMMPS => todo!(),
            // Opcode::VFIXUPIMMSD => todo!(),
            // Opcode::VFIXUPIMMSS => todo!(),
            // Opcode::VGETEXPPD => todo!(),
            // Opcode::VGETEXPPS => todo!(),
            // Opcode::VGETEXPSD => todo!(),
            // Opcode::VGETEXPSS => todo!(),
            // Opcode::VGETMANTPD => todo!(),
            // Opcode::VGETMANTPS => todo!(),
            // Opcode::VGETMANTSD => todo!(),
            // Opcode::VGETMANTSS => todo!(),
            // Opcode::VINSERTF32X4 => todo!(),
            // Opcode::VINSERTF64X4 => todo!(),
            // Opcode::VINSERTI64X4 => todo!(),
            // Opcode::VMOVDQA32 => todo!(),
            // Opcode::VMOVDQA64 => todo!(),
            // Opcode::VMOVDQU32 => todo!(),
            // Opcode::VMOVDQU64 => todo!(),
            // Opcode::VPBLENDMD => todo!(),
            // Opcode::VPBLENDMQ => todo!(),
            // Opcode::VPCMPD => todo!(),
            // Opcode::VPCMPUD => todo!(),
            // Opcode::VPCMPQ => todo!(),
            // Opcode::VPCMPUQ => todo!(),
            // Opcode::VPCOMPRESSQ => todo!(),
            // Opcode::VPCOMPRESSD => todo!(),
            // Opcode::VPERMI2D => todo!(),
            // Opcode::VPERMI2Q => todo!(),
            // Opcode::VPERMI2PD => todo!(),
            // Opcode::VPERMI2PS => todo!(),
            // Opcode::VPERMT2D => todo!(),
            // Opcode::VPERMT2Q => todo!(),
            // Opcode::VPERMT2PD => todo!(),
            // Opcode::VPERMT2PS => todo!(),
            // Opcode::VPMAXSQ => todo!(),
            // Opcode::VPMAXUQ => todo!(),
            // Opcode::VPMINSQ => todo!(),
            // Opcode::VPMINUQ => todo!(),
            // Opcode::VPMOVSQB => todo!(),
            // Opcode::VPMOVUSQB => todo!(),
            // Opcode::VPMOVSQW => todo!(),
            // Opcode::VPMOVUSQW => todo!(),
            // Opcode::VPMOVSQD => todo!(),
            // Opcode::VPMOVUSQD => todo!(),
            // Opcode::VPMOVSDB => todo!(),
            // Opcode::VPMOVUSDB => todo!(),
            // Opcode::VPMOVSDW => todo!(),
            // Opcode::VPMOVUSDW => todo!(),
            // Opcode::VPROLD => todo!(),
            // Opcode::VPROLQ => todo!(),
            // Opcode::VPROLVD => todo!(),
            // Opcode::VPROLVQ => todo!(),
            // Opcode::VPRORD => todo!(),
            // Opcode::VPRORQ => todo!(),
            // Opcode::VPRORRD => todo!(),
            // Opcode::VPRORRQ => todo!(),
            // Opcode::VPSCATTERDD => todo!(),
            // Opcode::VPSCATTERDQ => todo!(),
            // Opcode::VPSCATTERQD => todo!(),
            // Opcode::VPSCATTERQQ => todo!(),
            // Opcode::VPSRAQ => todo!(),
            // Opcode::VPSRAVQ => todo!(),
            // Opcode::VPTESTNMD => todo!(),
            // Opcode::VPTESTNMQ => todo!(),
            // Opcode::VPTERNLOGD => todo!(),
            // Opcode::VPTERNLOGQ => todo!(),
            // Opcode::VPTESTMD => todo!(),
            // Opcode::VPTESTMQ => todo!(),
            // Opcode::VRCP14PD => todo!(),
            // Opcode::VRCP14PS => todo!(),
            // Opcode::VRCP14SD => todo!(),
            // Opcode::VRCP14SS => todo!(),
            // Opcode::VRNDSCALEPD => todo!(),
            // Opcode::VRNDSCALEPS => todo!(),
            // Opcode::VRNDSCALESD => todo!(),
            // Opcode::VRNDSCALESS => todo!(),
            // Opcode::VRSQRT14PD => todo!(),
            // Opcode::VRSQRT14PS => todo!(),
            // Opcode::VRSQRT14SD => todo!(),
            // Opcode::VRSQRT14SS => todo!(),
            // Opcode::VSCALEDPD => todo!(),
            // Opcode::VSCALEDPS => todo!(),
            // Opcode::VSCALEDSD => todo!(),
            // Opcode::VSCALEDSS => todo!(),
            // Opcode::VSCATTERDD => todo!(),
            // Opcode::VSCATTERDQ => todo!(),
            // Opcode::VSCATTERQD => todo!(),
            // Opcode::VSCATTERQQ => todo!(),
            // Opcode::VSHUFF32X4 => todo!(),
            // Opcode::VSHUFF64X2 => todo!(),
            // Opcode::VSHUFI32X4 => todo!(),
            // Opcode::VSHUFI64X2 => todo!(),
            // Opcode::VCVTTPD2QQ => todo!(),
            // Opcode::VCVTPD2QQ => todo!(),
            // Opcode::VCVTTPD2UQQ => todo!(),
            // Opcode::VCVTPD2UQQ => todo!(),
            // Opcode::VCVTTPS2QQ => todo!(),
            // Opcode::VCVTPS2QQ => todo!(),
            // Opcode::VCVTTPS2UQQ => todo!(),
            // Opcode::VCVTPS2UQQ => todo!(),
            // Opcode::VCVTUQQ2PD => todo!(),
            // Opcode::VCVTUQQ2PS => todo!(),
            // Opcode::VEXTRACTF64X2 => todo!(),
            // Opcode::VEXTRACTI64X2 => todo!(),
            // Opcode::VFPCLASSPD => todo!(),
            // Opcode::VFPCLASSPS => todo!(),
            // Opcode::VFPCLASSSD => todo!(),
            // Opcode::VFPCLASSSS => todo!(),
            // Opcode::VINSERTF64X2 => todo!(),
            // Opcode::VINSERTI64X2 => todo!(),
            // Opcode::VPMOVM2D => todo!(),
            // Opcode::VPMOVM2Q => todo!(),
            // Opcode::VPMOVB2D => todo!(),
            // Opcode::VPMOVQ2M => todo!(),
            // Opcode::VRANGEPD => todo!(),
            // Opcode::VRANGEPS => todo!(),
            // Opcode::VRANGESD => todo!(),
            // Opcode::VRANGESS => todo!(),
            // Opcode::VREDUCEPD => todo!(),
            // Opcode::VREDUCEPS => todo!(),
            // Opcode::VREDUCESD => todo!(),
            // Opcode::VREDUCESS => todo!(),
            // Opcode::VDBPSADBW => todo!(),
            // Opcode::VMOVDQU8 => todo!(),
            // Opcode::VMOVDQU16 => todo!(),
            // Opcode::VPBLENDMB => todo!(),
            // Opcode::VPBLENDMW => todo!(),
            // Opcode::VPCMPB => todo!(),
            // Opcode::VPCMPUB => todo!(),
            // Opcode::VPCMPW => todo!(),
            // Opcode::VPCMPUW => todo!(),
            // Opcode::VPERMW => todo!(),
            // Opcode::VPERMI2B => todo!(),
            // Opcode::VPERMI2W => todo!(),
            // Opcode::VPMOVM2B => todo!(),
            // Opcode::VPMOVM2W => todo!(),
            // Opcode::VPMOVB2M => todo!(),
            // Opcode::VPMOVW2M => todo!(),
            // Opcode::VPMOVSWB => todo!(),
            // Opcode::VPMOVUSWB => todo!(),
            // Opcode::VPSLLVW => todo!(),
            // Opcode::VPSRAVW => todo!(),
            // Opcode::VPSRLVW => todo!(),
            // Opcode::VPTESTNMB => todo!(),
            // Opcode::VPTESTNMW => todo!(),
            // Opcode::VPTESTMB => todo!(),
            // Opcode::VPTESTMW => todo!(),
            // Opcode::VPBROADCASTM => todo!(),
            // Opcode::VPCONFLICTD => todo!(),
            // Opcode::VPCONFLICTQ => todo!(),
            // Opcode::VPLZCNTD => todo!(),
            // Opcode::VPLZCNTQ => todo!(),
            // Opcode::KUNPCKBW => todo!(),
            // Opcode::KUNPCKWD => todo!(),
            // Opcode::KUNPCKDQ => todo!(),
            // Opcode::KADDB => todo!(),
            // Opcode::KANDB => todo!(),
            // Opcode::KANDNB => todo!(),
            // Opcode::KMOVB => todo!(),
            // Opcode::KNOTB => todo!(),
            // Opcode::KORB => todo!(),
            // Opcode::KORTESTB => todo!(),
            // Opcode::KSHIFTLB => todo!(),
            // Opcode::KSHIFTRB => todo!(),
            // Opcode::KTESTB => todo!(),
            // Opcode::KXNORB => todo!(),
            // Opcode::KXORB => todo!(),
            // Opcode::KADDW => todo!(),
            // Opcode::KANDW => todo!(),
            // Opcode::KANDNW => todo!(),
            // Opcode::KMOVW => todo!(),
            // Opcode::KNOTW => todo!(),
            // Opcode::KORW => todo!(),
            // Opcode::KORTESTW => todo!(),
            // Opcode::KSHIFTLW => todo!(),
            // Opcode::KSHIFTRW => todo!(),
            // Opcode::KTESTW => todo!(),
            // Opcode::KXNORW => todo!(),
            // Opcode::KXORW => todo!(),
            // Opcode::KADDD => todo!(),
            // Opcode::KANDD => todo!(),
            // Opcode::KANDND => todo!(),
            // Opcode::KMOVD => todo!(),
            // Opcode::KNOTD => todo!(),
            // Opcode::KORD => todo!(),
            // Opcode::KORTESTD => todo!(),
            // Opcode::KSHIFTLD => todo!(),
            // Opcode::KSHIFTRD => todo!(),
            // Opcode::KTESTD => todo!(),
            // Opcode::KXNORD => todo!(),
            // Opcode::KXORD => todo!(),
            // Opcode::KADDQ => todo!(),
            // Opcode::KANDQ => todo!(),
            // Opcode::KANDNQ => todo!(),
            // Opcode::KMOVQ => todo!(),
            // Opcode::KNOTQ => todo!(),
            // Opcode::KORQ => todo!(),
            // Opcode::KORTESTQ => todo!(),
            // Opcode::KSHIFTLQ => todo!(),
            // Opcode::KSHIFTRQ => todo!(),
            // Opcode::KTESTQ => todo!(),
            // Opcode::KXNORQ => todo!(),
            // Opcode::KXORQ => todo!(),
            // Opcode::VEXP2PD => todo!(),
            // Opcode::VEXP2PS => todo!(),
            // Opcode::VEXP2SD => todo!(),
            // Opcode::VEXP2SS => todo!(),
            // Opcode::VRCP28PD => todo!(),
            // Opcode::VRCP28PS => todo!(),
            // Opcode::VRCP28SD => todo!(),
            // Opcode::VRCP28SS => todo!(),
            // Opcode::VRSQRT28PD => todo!(),
            // Opcode::VRSQRT28PS => todo!(),
            // Opcode::VRSQRT28SD => todo!(),
            // Opcode::VRSQRT28SS => todo!(),
            // Opcode::VGATHERPF0DPD => todo!(),
            // Opcode::VGATHERPF0DPS => todo!(),
            // Opcode::VGATHERPF0QPD => todo!(),
            // Opcode::VGATHERPF0QPS => todo!(),
            // Opcode::VGATHERPF1DPD => todo!(),
            // Opcode::VGATHERPF1DPS => todo!(),
            // Opcode::VGATHERPF1QPD => todo!(),
            // Opcode::VGATHERPF1QPS => todo!(),
            // Opcode::VSCATTERPF0DPD => todo!(),
            // Opcode::VSCATTERPF0DPS => todo!(),
            // Opcode::VSCATTERPF0QPD => todo!(),
            // Opcode::VSCATTERPF0QPS => todo!(),
            // Opcode::VSCATTERPF1DPD => todo!(),
            // Opcode::VSCATTERPF1DPS => todo!(),
            // Opcode::VSCATTERPF1QPD => todo!(),
            // Opcode::VSCATTERPF1QPS => todo!(),
            // Opcode::BNDMK => todo!(),
            // Opcode::BNDCL => todo!(),
            // Opcode::BNDCU => todo!(),
            // Opcode::BNDCN => todo!(),
            // Opcode::BNDMOV => todo!(),
            // Opcode::BNDLDX => todo!(),
            // Opcode::BNDSTX => todo!(),
            // Opcode::VGF2P8AFFINEQB => todo!(),
            // Opcode::VGF2P8AFFINEINVQB => todo!(),
            // Opcode::VPSHRDQ => todo!(),
            // Opcode::VPSHRDD => todo!(),
            // Opcode::VPSHRDW => todo!(),
            // Opcode::VPSHLDQ => todo!(),
            // Opcode::VPSHLDD => todo!(),
            // Opcode::VPSHLDW => todo!(),
            // Opcode::VBROADCASTF32X8 => todo!(),
            // Opcode::VBROADCASTF64X4 => todo!(),
            // Opcode::VBROADCASTF32X4 => todo!(),
            // Opcode::VBROADCASTF64X2 => todo!(),
            // Opcode::VBROADCASTF32X2 => todo!(),
            // Opcode::VBROADCASTI32X8 => todo!(),
            // Opcode::VBROADCASTI64X4 => todo!(),
            // Opcode::VBROADCASTI32X4 => todo!(),
            // Opcode::VBROADCASTI64X2 => todo!(),
            // Opcode::VBROADCASTI32X2 => todo!(),
            // Opcode::VEXTRACTI32X8 => todo!(),
            // Opcode::VEXTRACTF32X8 => todo!(),
            // Opcode::VINSERTI32X8 => todo!(),
            // Opcode::VINSERTF32X8 => todo!(),
            // Opcode::VINSERTI32X4 => todo!(),
            // Opcode::V4FNMADDSS => todo!(),
            // Opcode::V4FNMADDPS => todo!(),
            // Opcode::VCVTNEPS2BF16 => todo!(),
            // Opcode::V4FMADDSS => todo!(),
            // Opcode::V4FMADDPS => todo!(),
            // Opcode::VCVTNE2PS2BF16 => todo!(),
            // Opcode::VP2INTERSECTD => todo!(),
            // Opcode::VP2INTERSECTQ => todo!(),
            // Opcode::VP4DPWSSDS => todo!(),
            // Opcode::VP4DPWSSD => todo!(),
            // Opcode::VPDPWSSDS => todo!(),
            // Opcode::VPDPWSSD => todo!(),
            // Opcode::VPDPBUSDS => todo!(),
            // Opcode::VDPBF16PS => todo!(),
            // Opcode::VPBROADCASTMW2D => todo!(),
            // Opcode::VPBROADCASTMB2Q => todo!(),
            // Opcode::VPMOVD2M => todo!(),
            // Opcode::VPMOVQD => todo!(),
            // Opcode::VPMOVWB => todo!(),
            // Opcode::VPMOVDB => todo!(),
            // Opcode::VPMOVDW => todo!(),
            // Opcode::VPMOVQB => todo!(),
            // Opcode::VPMOVQW => todo!(),
            // Opcode::VGF2P8MULB => todo!(),
            // Opcode::VPMADD52HUQ => todo!(),
            // Opcode::VPMADD52LUQ => todo!(),
            // Opcode::VPSHUFBITQMB => todo!(),
            // Opcode::VPERMB => todo!(),
            // Opcode::VPEXPANDD => todo!(),
            // Opcode::VPEXPANDQ => todo!(),
            // Opcode::VPABSQ => todo!(),
            // Opcode::VPRORVD => todo!(),
            // Opcode::VPRORVQ => todo!(),
            // Opcode::VPMULTISHIFTQB => todo!(),
            // Opcode::VPERMT2B => todo!(),
            // Opcode::VPERMT2W => todo!(),
            // Opcode::VPSHRDVQ => todo!(),
            // Opcode::VPSHRDVD => todo!(),
            // Opcode::VPSHRDVW => todo!(),
            // Opcode::VPSHLDVQ => todo!(),
            // Opcode::VPSHLDVD => todo!(),
            // Opcode::VPSHLDVW => todo!(),
            // Opcode::VPCOMPRESSB => todo!(),
            // Opcode::VPCOMPRESSW => todo!(),
            // Opcode::VPEXPANDB => todo!(),
            // Opcode::VPEXPANDW => todo!(),
            // Opcode::VPOPCNTD => todo!(),
            // Opcode::VPOPCNTQ => todo!(),
            // Opcode::VPOPCNTB => todo!(),
            // Opcode::VPOPCNTW => todo!(),
            // Opcode::VSCALEFSS => todo!(),
            // Opcode::VSCALEFSD => todo!(),
            // Opcode::VSCALEFPS => todo!(),
            // Opcode::VSCALEFPD => todo!(),
            // Opcode::VPDPBUSD => todo!(),
            // Opcode::VCVTUSI2SD => todo!(),
            // Opcode::VCVTUSI2SS => todo!(),
            // Opcode::VPXORD => todo!(),
            // Opcode::VPXORQ => todo!(),
            // Opcode::VPORD => todo!(),
            // Opcode::VPORQ => todo!(),
            // Opcode::VPANDND => todo!(),
            // Opcode::VPANDNQ => todo!(),
            // Opcode::VPANDD => todo!(),
            // Opcode::VPANDQ => todo!(),
            // Opcode::PSMASH => todo!(),
            // Opcode::PVALIDATE => todo!(),
            // Opcode::RMPADJUST => todo!(),
            // Opcode::RMPUPDATE => todo!(),
            _ => {
                // TODO eventually this should fire a recoverable signal.
                panic!("Unimplemented instruction: {}", instruction);
            }
        }

        Ok(StepResult::Continue)
    }
}
