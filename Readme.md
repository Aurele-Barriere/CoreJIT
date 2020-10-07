This is the developement of CoreJIT, a verified JIT compiler


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

This artifact comes with a prebuilt version of CoreJIT packaged as an OCI compliant container.
To run this artifact it suffices to run:

```
CR=docker    # or podman
VS=ff0de016566714f54c9b993bc52dbdf38036cfb6
RG=docker.pkg.github.com/aurele-barriere/corejit/jit
$CR run $RG:$VS
```

If the registry is unavailable, then the container is also included as archive which can be imported using `$CR load < image.tgz`.

This container by default executes the [aec](https://github.com/Aurele-Barriere/CoreJIT/blob/master/aec.sh) script, which compiles the proofs, runs all tests and the performance experiments.

There are a number of example programs in CoreJITs IR format in [src/coqjit/progs_specIR](https://github.com/Aurele-Barriere/CoreJIT/tree/master/src/coqjit/progs_specIR). To run one of these programs do the following:

```
H=/home/opam/coqjit/
$CR run $RG:$VS $H/jit $H/progs_specIR/constprop.specir
```

To get the list of options use

```
$CR run $RG:$VS $H/jit -h
```

There are a number of lua programs in [src/coqjit/progs_lua](https://github.com/Aurele-Barriere/CoreJIT/tree/master/src/coqjit/progs_lua). To run one of these programs do the following:

```
$CR run $RG:$VS $H/jit -f $H/progs_lua/scopes.lua
```

To run these steps with the native backend enabled additionally pass the `-n` flag.


## Reproducing performance numbers

```
$CR run $RG:$VS $H/jit -f $H/experiments.sh 10
```

# Building CoreJIT

The container of this artifact includes build dependencies. You can therefore run:

```
$CR run -it $RG:$VS bash
```

And, then make changes to the sources, and build everything using `make`.

This artifact also includes a [Dockerfile](https://github.com/Aurele-Barriere/CoreJIT/blob/master/Dockerfile) to build the container using:

```
docker build . --file Dockerfile
```

The interesting steps are to be found in the [docker-install.sh](https://github.com/Aurele-Barriere/CoreJIT/blob/master/container-install.sh) script. 

Alternatively CoreJIT can be built on any system with opam as follows:

```
cd src/coqjit
wget https://releases.llvm.org/9.0.0/clang+llvm-9.0.0-x86_64-pc-linux-gnu.tar.xz
tar xf clang+llvm-9.0.0-x86_64-pc-linux-gnu.tar.xz
PATH="$PATH:$PWD/clang+llvm-9.0.0-x86_64-pc-linux-gnu/bin"
make install-deps
eval $(opam env)
make
```
