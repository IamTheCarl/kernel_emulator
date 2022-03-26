mod kernel;

use kernel::*;
use process::X86Process;
use std::collections::HashSet;

fn main() {
    let test_programs: &[&[u8]] = &[
        include_bytes!("../testing/hello_world_asm.elf"),
        include_bytes!("../testing/hello_world_c.elf"),
    ];

    let test_program_names = [
        "../testing/hello_world_asm.elf",
        "../testing/hello_world_c.elf",
    ];

    let mut system = Kernel::new().unwrap();

    let mut processes = HashSet::new();

    for (program, name) in test_programs.iter().zip(test_program_names.iter()) {
        let executable = Kernel::load_elf(program).unwrap();
        let process_x86 = X86Process::new();

        let process_id = system
            .new_process(process_x86, &executable, vec![name.to_string()])
            .unwrap();

        processes.insert(process_id);
    }

    while !processes.is_empty() {
        let results = system.step(0x7FFF_FFFF_FFFF_FFFF);

        for (process_id, exit_code) in results {
            processes.remove(&process_id);
            println!("Process {} exited with code {}.", process_id, exit_code);
        }
    }
}
