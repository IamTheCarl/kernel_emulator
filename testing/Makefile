
.PHONY:
all: hello_world_asm.elf hello_world_c.elf

%.elf: %.c
	gcc -o $@ $<

hello_world_asm.elf: hello_world_asm.s
	nasm -f elf64 -o hello_world_asm.o $<
	ld -o $@ hello_world_asm.o

.PHONY:
clean:
	rm *.o *.elf