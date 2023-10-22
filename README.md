# icepop

`icepop` is a rewrite of [`riscvemu`](https://github.com/jmpnz/riscvemu) in Rust
with a few twists.

`icepop` supports dynamic binary translation to x86-64 and allows introspection
of memory accesses and syscalls via hooks allowing an `strace` like view of what
a binary does.

The goal of writing `icepop` was two folds, first learn about using emulators
for binary analysis and second as an exercise in how to design and implement
dynamic binary translation on a real target architecture.

