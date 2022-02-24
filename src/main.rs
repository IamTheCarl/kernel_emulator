mod kernel;

use kernel::System;

fn main() {
    let test_program = include_bytes!("../testing/hello_world.elf");

    let mut system = System::new().unwrap();

    system.load_elf(test_program).unwrap();
    system.run().unwrap();
}
