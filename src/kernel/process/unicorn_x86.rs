use super::{Error, Process, Result, StepResult};
use crate::kernel::{
    memory::ProcessMemory, process::Error as ProcessError, Pointer, ProcessId, SyscallRequest,
    Value, ValueSize,
};
use unicorn_engine::{
    unicorn_const::{uc_error, Arch, Mode, Permission},
    InsnSysX86, RegisterX86, Unicorn,
};

// So we can just happily return Unicorn errors.
impl From<uc_error> for ProcessError {
    fn from(error: uc_error) -> ProcessError {
        ProcessError::Custom(match error {
            uc_error::OK => "No error.",
            uc_error::NOMEM => "No memory available or memory not present.",
            uc_error::ARCH => "Invalid/unsupported architecture.",
            uc_error::HANDLE => "Invalid Handle",
            uc_error::MODE => "Invalid Mode",
            uc_error::VERSION => "Different API version between core & binding.",
            uc_error::READ_UNMAPPED => "Invalid memory read.",
            uc_error::WRITE_UNMAPPED => "Invalid memory write.",
            uc_error::FETCH_UNMAPPED => "Invalid memory fetch.",
            uc_error::HOOK => "Invalid hook type.",
            uc_error::INSN_INVALID => "Invalid instruction.",
            uc_error::MAP => "Invalid memory mapping.",
            uc_error::WRITE_PROT => "Write to write-protected memory.",
            uc_error::READ_PROT => "Read from non-readable memory.",
            uc_error::FETCH_PROT => "Fetch from non-executable memory.",
            uc_error::ARG => "Invalid argument.",
            uc_error::READ_UNALIGNED => "Read from unaligned memory.",
            uc_error::WRITE_UNALIGNED => "Write to unaligned memory.",
            uc_error::FETCH_UNALIGNED => "Fetch from unaligned memory.",
            uc_error::HOOK_EXIST => "Hook exists.",
            uc_error::RESOURCE => "Insufficient resource.",
            uc_error::EXCEPTION => "Unhandled CPU exception.",
        })
    }
}

struct UnicornData {
    process_id: ProcessId,
    memory: ProcessMemory,
    syscall_request: Option<SyscallRequest>,
    error: Option<Error>,
}

pub struct UnicornX86Process {
    unicorn: Unicorn<'static, UnicornData>,
}

impl UnicornX86Process {
    pub fn new() -> Result<Box<Self>> {
        let memory = ProcessMemory::new();
        let mut unicorn = Unicorn::new_with_data(
            Arch::X86,
            Mode::MODE_64,
            UnicornData {
                process_id: 0,
                memory,
                syscall_request: None,
                error: None,
            },
        )?;

        // Setup syscalls.
        unicorn.add_insn_sys_hook(InsnSysX86::SYSCALL, 0, 0xFFFFFFFFFFFFFFFF, |uc| {
            // This is just a convinentish way to handle errors.
            let mut trampoline = || -> Result<()> {
                // Stop the emulation.
                uc.emu_stop()?;

                // Collect needed information about the syscall.
                let call_code = uc.reg_read(RegisterX86::RAX)?;
                let arguments = [
                    uc.reg_read(RegisterX86::RDI)?,
                    uc.reg_read(RegisterX86::RSI)?,
                    uc.reg_read(RegisterX86::RDX)?,
                    uc.reg_read(RegisterX86::R10)?,
                    uc.reg_read(RegisterX86::R8)?,
                    uc.reg_read(RegisterX86::R9)?,
                ];

                let data = uc.get_data_mut();

                data.syscall_request = Some(SyscallRequest {
                    process_id: data.process_id,
                    call_code,
                    arguments,
                });

                Ok(())
            };

            let result = trampoline();
            drop(trampoline);

            // Handle errors, if they happen.
            if let Err(error) = result {
                let data = uc.get_data_mut();
                data.syscall_request = None;
                data.error = Some(error);
            }
        })?;

        // Setup memory.
        let read_callback = move |uc: &mut Unicorn<'_, UnicornData>, address, size| {
            let size = ValueSize::new(size as u8);
            let memory = &uc.get_data().memory;
            match memory.read_random(address, size) {
                Ok(value) => value.as_pointer(),
                Err(error) => {
                    // Report error.
                    uc.get_data_mut().error = Some(error.into());

                    // Attempt to stop the emulator.
                    uc.emu_stop().ok();
                    0
                }
            }
        };
        let write_callback = move |uc: &mut Unicorn<'_, UnicornData>, address, size, value| {
            let size = ValueSize::new(size as u8);
            let memory = &uc.get_data().memory;

            let value = Value::Quad(value).dynamic_cast(ValueSize::new(size as u8));

            if let Err(error) = memory.write_random(address, value) {
                // Report error.
                uc.get_data_mut().error = Some(error.into());

                // Attempt to stop the emulator.
                uc.emu_stop().ok();
            }
        };

        unicorn.mmio_map(
            0,
            0xFFFF_FFFF_FFFF_F000,
            Some(read_callback),
            Some(write_callback),
        )?;
        unicorn.mem_protect(
            0,
            0xFFFF_FFFF_FFFF_F000,
            Permission::READ | Permission::WRITE | Permission::EXEC,
        )?;

        // Setup instruction printing for debug.
        unicorn.add_code_hook(0, 0xFFFF_FFFF_F000, |uc, address, size| {
            let mut bytes = [0u8; 15];

            let bytes_result = uc
                .get_data()
                .memory
                .read_random_bytes(address, &mut bytes[..size as usize]);

            match bytes_result {
                Ok(_) => {}
                Err(error) => {
                    uc.get_data_mut().error = Some(Error::Memory(error));
                    uc.emu_stop().ok();
                }
            }
        })?;

        Ok(Box::new(Self { unicorn }))
    }
}

impl Process for UnicornX86Process {
    fn initalize(
        &mut self,
        process_id: ProcessId,
        entry_point: Pointer,
        stack_pointer: Pointer,
        at_exit_pointer: Pointer,
        memory: ProcessMemory,
    ) -> Result<()> {
        self.unicorn.get_data_mut().process_id = process_id;

        self.unicorn.reg_write(RegisterX86::RIP, entry_point)?;
        self.unicorn.reg_write(RegisterX86::RSP, stack_pointer)?;
        self.unicorn.reg_write(RegisterX86::RDX, at_exit_pointer)?;

        // Unmap old memory.
        let regions: Vec<(std::ops::Range<Pointer>, bool, bool, bool)> =
            self.memory().segments().collect();
        for (region, _is_read, _is_write, _is_executable) in regions {
            self.unicorn
                .mem_unmap(region.start, (region.end - region.start) as usize)?;
        }

        self.unicorn.get_data_mut().memory.replace(memory);

        Ok(())
    }

    fn step(
        &mut self,
        instruction_count: u64,
        syscall_result: Option<Pointer>,
    ) -> Result<(StepResult, i64)> {
        if let Some(syscall_result) = syscall_result {
            self.unicorn.reg_write(RegisterX86::RAX, syscall_result)?;
        }

        let pc = self.unicorn.reg_read(RegisterX86::RIP)?;

        // FIXME if we return early (say to handle a syscall) this doesn't report that we went under budget.
        self.unicorn
            .emu_start(pc, 0xFFFF_FFFF_FFFF_FFFF, 0, instruction_count as usize)?;

        if let Some(error) = self.unicorn.get_data_mut().error.take() {
            Err(error)
        } else if let Some(syscall) = self.unicorn.get_data_mut().syscall_request.take() {
            Ok((StepResult::Syscall(syscall), 0))
        } else {
            Ok((StepResult::Continue, 0))
        }
    }

    fn memory(&mut self) -> &ProcessMemory {
        &self.unicorn.get_data().memory
    }
}
