use elf_rs::{Elf, ElfFile};
use syscalls::Sysno;
use thiserror::Error;
use unicorn_engine::{
    unicorn_const::{uc_error, Arch, Mode, Permission},
    InsnSysX86, RegisterX86, Unicorn,
};

#[derive(Error, Debug)]
pub enum Error {
    #[error("Emulation Error: {0}")]
    CPUEmulation(&'static str),

    #[error("Invalid syscall: {0}")]
    InvalidSyscall(u64),

    #[error("Io Error: {0}")]
    Io(#[from] std::io::Error),
}

impl std::convert::From<uc_error> for Error {
    fn from(error: uc_error) -> Self {
        Self::CPUEmulation(match error {
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

type Result<T> = std::result::Result<T, Error>;

struct Kernel {}

pub struct System {
    entry_point: u64,
    cpu: Unicorn<'static, Kernel>,
}

impl System {
    pub fn new() -> Result<Self> {
        Ok(Self {
            entry_point: 0,
            cpu: Unicorn::new_with_data(Arch::X86, Mode::MODE_64, Kernel {})?,
        })
    }

    pub fn load_elf(&mut self, elf_bytes: &[u8]) -> Result<()> {
        let elf = Elf::from_bytes(elf_bytes).unwrap();

        self.entry_point = elf.entry_point();

        for header in elf.program_header_iter() {
            let address = header.paddr();
            let data = header.content();

            let length = ((data.len() / 4096) + 1) * 4096;

            self.cpu.mem_map(address, length, Permission::ALL)?;
            self.cpu.mem_write(address, data)?;
        }

        Ok(())
    }

    pub fn run(&mut self) -> Result<()> {
        self.cpu
            .add_intr_hook(|_cpu, interrupt_id| {
                println!("Got interupt: {}", interrupt_id);
            })
            .unwrap();

        // self.cpu
        //     .add_mem_hook(
        //         HookType::MEM_ALL,
        //         0,
        //         0xFFFFFFFFFFFFFFFF,
        //         |_uc, access, address, size, value| {
        //             dbg!(access, address, size, value);

        //             true
        //         },
        //     )
        //     .unwrap();

        // self.cpu
        //     .add_code_hook(0, 0xFFFFFFFFFFFFFFFF, |_uc, address, _code| {
        //         // TODO We might be able to use IcedX86 to dissassemble this on the fly.
        //         println!("Instruction: {:08x}", address)
        //     })?;

        self.cpu
            .add_insn_sys_hook(InsnSysX86::SYSCALL, 0, 0xFFFFFFFFFFFFFFFF, |uc| {
                // TODO how do we process this error?
                Self::syscall(uc).unwrap();
            })?;

        self.cpu.reg_write(RegisterX86::IP, self.entry_point)?;

        self.cpu
            .emu_start(self.entry_point, 0xFFFFFFFFFFFFFFFF, 0, 0)?;

        Ok(())
    }

    fn syscall(unicorn: &mut Unicorn<'_, Kernel>) -> Result<()> {
        let call_code = unicorn.reg_read(RegisterX86::RAX)?;

        if let Some(call_code) = Sysno::new(call_code as usize) {
            match call_code {
                Sysno::exit => {
                    let exit_code = unicorn.reg_read(RegisterX86::RDI)?;
                    println!("Exit code: {}", exit_code);

                    unicorn.emu_stop()?;

                    Ok(())
                }
                Sysno::write => {
                    let file_handle = unicorn.reg_read(RegisterX86::RDI)?;
                    let message_pointer = unicorn.reg_read(RegisterX86::RSI)?;
                    let message_length = unicorn.reg_read(RegisterX86::RDX)?;

                    let mut file: Box<dyn std::io::Write> = match file_handle {
                        1 => Box::new(std::io::stdout()),
                        2 => Box::new(std::io::stderr()),
                        _ => panic!("Non standard file handals are not yet supported."),
                    };

                    let message =
                        unicorn.mem_read_as_vec(message_pointer, message_length as usize)?;

                    let bytes_written = file.write(&message)?;

                    unicorn.reg_write(RegisterX86::EAX, bytes_written as u64)?;

                    Ok(())
                }
                _ => panic!("Syscall `{}` is not yet supported.", call_code),
            }
        } else {
            Err(Error::InvalidSyscall(call_code))
        }
    }
}
