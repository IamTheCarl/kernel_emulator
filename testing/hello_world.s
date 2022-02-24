global _start

section .text

_start:
  mov rax, 1        ; Write syscall
  mov rdi, 1        ; STDOUT file
  mov rsi, msg      ; Pointer to message
  mov rdx, msglen   ; Length of message
  syscall
  
  mov rax, 60 ; Exit syscall
  mov rdi, 0  ; Exit status
  syscall

section .rodata
  msg: db "Hello, world!", 10
  msglen: equ $ - msg
