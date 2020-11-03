# Coq JIT
These files describe an implementation and proof of a verified JIT in Coq.

## Install
Typing `make` will:
* Build the Coq development, proofs and implentation
* Extract the Coq functions to an `extraction` folder as OCaml code
* Build the Ocaml executable JIT, from the extracted Coq code and the Ocaml code (profiler, parser etc)

To clean generated files:
`make clean_all` will clean every generated file, `make clean` won't clean the Coq librairies.

## Usage
Once compiled, execute the JIT by typing `./jit prog` where `prog` is a file containing a specIR (or miniLua) program.
Examples can be found in the `progs_specIR` or `progs_lua` directory.

You can give an option:
*  `-o` Print Optimized Functions
*  `-s` Print Debug Strings
*  `-p` Print Debug Program
*  `-k` Disable profiler using hints
*  `-n` Enable unverified native backend
*  `-f` Enable unverified lua frontend
*  `-t` Enable asserts in frontend
*  `-d` Print Native Debugging
*  `-a` Print Native Code
*  `-m` Print Native Heap
*  `-c` Native call always goes through jit_step, even when calling optimized code
*  `-help`  Display this list of options
