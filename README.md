# LALU
`lalu_asm` is a library containing assembler/interpreter definitions and implementations

`lalu_cli` is a wrapper which calls `lalu_asm` internally.

In order to build and run this program, simply open the root directory and run `cargo run --release` from a terminal. By default, this will try to open a file `in.txt` and assemble it, writing binary output to `out.lalu` (which can be viewed using a hex editor). This command will also interpret the assembly.

## Interpreting output

At the start and end of the program, and between every instruction that is run, the state of every register is printed in the following format:
`[R0, R1, R2, R3] -> result_of_most_recent_instruction`

There are also lines representing an instruction called, with this format:
`instruction_index: instruction_that_was_run`
