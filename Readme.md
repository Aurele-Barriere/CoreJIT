This is the developement of CoreJIT, a verified JIT compiler


# Build Instructions


# CoreJIT code overview

This section details the different components of CoreJIT.
Some definitions have been renamed in the submission.
Here are their equivalent:
- CoreIR     <->   `SpecIR`
- core_sem   <->   `specir_sem`
- Anchor     <->   `Framestate`

## Coq Development

The `src/coqjit` directory contains the Coq development for CoreJIT, operating on CoreIR, our intermediate representation for speculative optimizations and deoptimizations.
CoreIR syntax and semantics are defined in `specIR.v`.

The JIT step that is looped during JIT execution is defined in `jit.v`.
This either calls a CoreIR interpreter `interpreter.v` or a dynamic optimizer `optimizer.v`
The different passes of the dynamic optimizer are in separate files (`const_prop.v, inlining.v`...).

Our developpment uses a few Coq libraries from CompCert. These are located in `src/coqjit/lib`.

## Coq Proofs

Our final Semantic Preservation Theorem is proved in `jit_proof.v`.
Each file ending in `_proof.v` contains the correctness proof of a CoreJIT component.
The Internal Simulation Framework for Dynamic Optimizations is located in `internal_simulations.v`.

## Extraction

The Coq development is extracted to OCaml as specified by the `extract.v` file.
This creates an `extraction` directory where the extracted code is located.
The patch `jit.ml.patch` is applied to the extracted code to enable the backend during the execution.

## Ocaml Develoment

CoreJIT can be run using the extracted OCaml code. The additional OCaml code is out of scope of our verification work.
The `parsing` directory contains a parser of CoreIR (see examples in `progs_specIR` directory).
The `frontend` directory contains a frontend from miniLua (see examples in `progs_lua`) to CoreIR.
The `backend` directory contains an optional backend where CoreIR is translated to LLVM IR and then to native code.

The extracted `jit_step` from `jit.v` is looped in `main.ml`. 
A simple profiler implementation is defined in `profiler.ml`.

# Coq Axioms and Parameters

The profiler, optimization heuristics and memory model are external parameters.
This ensures that the correctness theorems do not depend on their implementation.
These parameters have to be realized for the JIT to be extracted.
The Load and Store implementations may fail (return None), for instance for an out-of-bound access.
This corresponds to blocking behaviors in the semantics, and these behaviors are preserved.

Here is a list of Parameters realized during the Coq extraction:
- `profiler_state`:          a type that the profiler can update
- `initial_profiler_state`:  how to initialiaze the profiler state
- `profiler`:                updating the profiler state
- `optim_policy`:            suggesting to optimize or execute
- `optim_list`:              the list of optimization wishes the profiler wants to perform
- `framestates_to_insert`:   the list of locations the profiler wants to insert framestates at

- `mem_state`:               an abstract type for the memory
- `initial_memory`:          how to initialize the memory
- `Store_`:                  how to implement the Store instruction (may fail)
- `Load_`:                   how to implement the Load instruction (may fail)

- `spacing`:                 a number used as an heuristic for Assume insertion
- `max_optim`:               maximum number of optimization steps the JIT can do
- `interpreter_fuel`:        maximum number of steps the interpreter can perform before going back to the JIT
- `hint`:                    a type to annotate the Nop instructions
- `fuel_fresh`:              a number used as an heuristic for Assume insertion

The CompCert libraries also use 2 Axioms: Functional Extensionality and Classical Logic.

# Running CoreJIT

# Experiments
