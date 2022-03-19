mod kernel;

use kernel::*;

fn main() {
    // let test_program = include_bytes!("../testing/hello_world_asm.elf");
    let test_program = include_bytes!("../testing/hello_world_c.elf");

    let mut system = Kernel::new().unwrap();

    let executable = Kernel::load_elf(test_program).unwrap();
    let result = system
        .execute(&executable, ["application_path".to_string()])
        .unwrap();

    match result {
        ProgramResult::Exit(exit_code) => println!("Exit code: {}", exit_code),
        ProgramResult::Halt => println!("Program Halt."),
    }
}
