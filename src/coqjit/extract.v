(* Extracting the Coq JIT to OCaml *)

Require Export List.
Require Export Coqlib.
Require Export Maps.
Require Export common.
Require Export specIR.
Require Export interpreter.
Require Export profiler_types.
Require Export optimizer.
Require Export jit.
Require Export liveness.
Require Extraction.

(* Standard lib *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

(* Datatypes *)
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

(* Avoid name clashes *)
Extraction Blacklist List String Int.

(* Strings *)
(* https://github.com/coq/coq/issues/2747 *)
Extract Inductive string => "string" [ """""" "(fun (a,b) -> (Char.escaped a) ^ b)"] "(fun e c s -> if s = "" then e else c s.[0] (String.sub s 1 (String.length s - 1)))".

(* Realizing parameters *)
Extract Constant hint => "Params.hint".

Extract Constant mem_state => "Memory.mem_state".

Extract Constant initial_memory => "Memory.initial_memory".

Extract Constant Load_ => "Memory.load_".

Extract Constant Store_ => "Memory.store_".

Extract Constant max_optim => "Params.max_optim".

Extract Constant interpreter_fuel => "Params.interpreter_fuel".

Extract Constant profiler_state => "Profiler.profiler_state".

Extract Constant initial_profiler_state => "Profiler.initial_profiler_state".

Extract Constant profiler => "Profiler.profiler".

Extract Constant optim_policy => "Profiler.optim_policy".

Extract Constant optim_list => "Profiler.optim_list".

Extract Constant framestates_to_insert => "Profiler.framestates_to_insert".

Extract Constant fuel_fresh => "Params.fuel_fresh".

Extract Constant spacing => "Params.spacing".

(* Needed in Coq 8.4 to avoid problems with Function definitions. *)
(* Set Extraction AccessOpaque. *)

Cd "extraction".

Separate Extraction jit_step jit_program jit_final_value initial_jit_state
         insert_all_framestates test_optimizer liveness_analyze
         PMap.set PMap.get PMap.init
         Pos.leb Pos.pred Z.succ Z.pred Z.neg Z.add Z.sub Z.mul Z.div Z.modulo Z.compare Z.of_N Z.land.
