.PHONY: coq ocaml all extract proofs clean clean_all clean_coq clean_extracted clean_ocaml clean_libs coq_depend ../native_lib/native_lib.o

LIBS = Coqlib.v Maps.v Axioms.v Heaps.v Iteration.v Lattice.v Ordered.v Wfsimpl.v Kildall.v events.v Smallstep.v values.v Behaviors.v
FILES = common.v specIR.v interpreter.v def_regs.v framestate_insertion.v lowering.v const_prop.v assume_insertion.v assume_insertion_delay.v inlining.v profiler_types.v optimizer.v jit.v
PROOFS = ir_properties.v internal_simulations.v interpreter_proof.v const_prop_proof.v lowering_proof.v framestate_insertion_proof.v assume_insertion_proof.v assume_insertion_delay_proof.v inlining_proof.v optimizer_proof.v jit_proof.v

COQC=coqc -R lib coqjit.lib
COQDEP=coqdep -R lib coqjit.lib
OCB_FLAGS = -tag bin_annot -I . -I extraction -I parsing -I frontend -I backend -I lib -use-menhir -use-ocamlfind -package coq -package llvm -package llvm.analysis -package llvm.executionengine -package llvm.scalar_opts -package ctypes -package ctypes.foreign -lflag ../../native_lib/native_lib.o
OCB=ocamlbuild $(OCB_FLAGS)

all: coq extract ocaml proofs

%.vo: %.v
	@echo COQC $*.v
	@$(COQC) $*.v

extract.vo: extract.v $(FILES:%.v=%.vo)
	@echo Creating extraction folder
	-@mkdir extraction
	@echo COQC extract.v
	@$(COQC) extract.v
	@patch extraction/jit.mli jit.mli.patch
	@patch extraction/jit.ml jit.ml.patch

coq_libs: $(LIBS:%.v=lib/%.vo)

.depend: $(FILES) $(PROOFS) $(LIBS:%=lib/%)
	@echo COQDEP: Generating dependencies
	@$(COQDEP) # ensure coqdep exists before writing to .depend
	@$(COQDEP) $^ > .depend

coq_depend: .depend

coq: coq_depend coq_libs $(FILES:%.v=%.vo)

extract: coq extract.vo

proofs: coq $(PROOFS:%.v=%.vo)

ocaml: ../native_lib/native_lib.o
	@echo Building the OCaml Extracted JIT
	@$(OCB) main.native
	@mv main.native jit

test_optim: test_optim.ml progs_specIR/test.specir
	@$(OCB) test_optim.native
	@mv test_optim.native test_optim

../native_lib/native_lib.o:
	$(MAKE) -C ../native_lib

clean: clean_coq clean_extracted clean_ocaml

clean_all: clean clean_libs

clean_coq:
	@echo Cleaning Coq compiled files
	-@rm .depend
	-@rm *.vo *.glob .*.aux *.vok *.vos
	-@rm extraction/extract.vo extraction/extract.vok extraction/extract.vos

clean_extracted:
	@echo Cleaning Extracted files
	-@rm -R extraction

clean_ocaml:
	@echo Cleaning OCaml compiled files
	-@rm jit
	-@rm -R _build

clean_libs:
	@echo Cleaning Coq compiled libraries
	-@rm lib/*.vo lib/*.glob lib/.*.aux lib/*.vok lib/*.vos

install-deps:
	opam pin add coqjit . --no-action # tell opam about a local "cogjit" package
	opam install --deps-only coqjit # then install its dependencies

-include .depend
