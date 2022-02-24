
.PHONY:
all: hello_world.elf

%.elf: %.o
	ld -o $@ $<

%.o: %.s
	nasm -f elf64 -o $@ $<

.PHONY:
clean:
	rm *.o *.elf