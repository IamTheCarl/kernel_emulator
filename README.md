
# Kernel Emulator

This is a *somewhat working* proof of concept for a userland emulator intended to be used in a video game. In this game I desire the player to have computers than can run real software for UNIX systems. The idea is that rather than emulate a full Personal Computer, only emulate the CPU and a kernel by capturing syscalls. This permits many clever tricks to reduce the overhead of emulation, such as multiple instances of an application re-using memory pages like a real kernel does, but between multiple computers. It also removes the need to emulate PCI devices, as you'll only need to emulate device nodes.

At this point in time, this reposetory is just a proof of concept and nothing more. It can't even get through the `_start` entrypoint to enter a real main function written in C, but it can bumble its way through a hand written "Hello, World!" program written in assembly.

While I would love to continue working on this endevor, I need more time and support. I'm going to work on the main game for now and come back to this when time and other resources permit.

## The game in question

The game is called Tears in the Dust. You can download and then play it from [here](https://i-am-the-carl.itch.io/tears-in-the-dust)


Do note that this emulator is currently unavailable in the game.

## Unicorn Engine

Unicorn engine has been used in testing and the really early proof of concept work. It will not be in the final product for two reasons.

1. It has a GPL license, and this project is MIT/Apache
3. It only works on x86. I wish for this emulation environment to work on x86, ARM, and HTML5.

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.