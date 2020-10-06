(* The Just in Time step *)

Require Export List.
Require Export Coqlib.
Require Export Maps.
Require Export common.
Require Export specIR.
Require Export interpreter.
Require Export optimizer.

(** * Forging call stackframes *)
(* When the interpreters encounters a Call, it returns a stackframe to add to the JIT stack *)
Definition forge_call_stackframe (s:stack) (osf:option stackframe) : stack :=
  match osf with
  | None => s
  | Some sf => sf :: s
  end.

(** * Forging interpreter states  *)
(* Mimics the semantics of the call, return or deopt *)
Definition forge_interpreter_state (p:program) (current_stack:stack) (s:synchro_state) : res (interpreter_state * stack) :=
  match s with
  | S_Call fid param_vals osf =>
    do func <- try_op (find_function fid p) "Function to call does not exist";
      do version <- OK (current_version func);
      do newrm <- interpreter.init_regs param_vals (fn_params func);
      OK (Int_State version (ver_entry version) newrm, forge_call_stackframe current_stack osf) (* maybe pushed to the stack *)

  | S_Return retval =>
    match current_stack with
    | nil => OK (Int_Final retval,nil)
    | (Stackframe retreg v retlbl rm)::st' =>
      OK (Int_State v retlbl (rm # retreg <- retval), st') (* we popped the stack *)
    end
      
  | S_Deopt (fa,la) synth newrm =>
    do newver <- try_op (find_base_version fa p) "The version to deoptimize to does not exist";
      OK (Int_State newver la newrm, synth++current_stack) (* we added the synth frames to the stack *)

  | Halt int_state => OK (int_state, current_stack)
  end.


(** * Profiler oracle, external heuristics  *)
(* The JIT correctness does not depend on their implementation *)
Parameter initial_profiler_state: profiler_state.
Parameter profiler: profiler_state -> synchro_state -> profiler_state.
Parameter optim_policy: profiler_state -> jit_status.

(** * JIT states  *)
(* The state of the JIT that gets modified with each step *)
Record jit_state: Type := mk_jit_state {
  prog: program;                (* current program *)
  prof_state: profiler_state;   (* state of the profiler *)
  mem: mem_state;               (* state of the memory *)
  stack: stack;                 (* current model of the stack *)
  synchro: synchro_state;       (* current synchronization state *)
  nb_optim: nat                   (* number of optimizations left *)
                            }.    
(* The optimization policy cannot be trusted: it could ask us to optimize at each step *)
(* without ever making any progress. *)
(* The nb_optim nat bounds the total number of optimizations possible *)

(* Maximum number of optimizations to perform *)
Parameter max_optim: nat.

(** * Interpreter  *)
Parameter interpreter_fuel: nat.

Definition interpreter (p:program) (ins:interpreter_state) (ms:mem_state): res (synchro_state * mem_state * trace) :=
  interpreter_loop interpreter_fuel p ins ms. (* calling the interpreter loop *)

(** * Initial JIT state *)
Definition initial_jit_state (p:program) :=
  OK (mk_jit_state p initial_profiler_state initial_memory nil (S_Call (prog_main p) nil None) max_optim).

(* Choosing the next step of the JIT (execution or optimizing) *)
Definition next_status (ps:profiler_state) (nb_optim:nat): jit_status :=
  match nb_optim with
  | O => Exe                    (* force execution if we've reached the max number of optims *)
  | _ => optim_policy ps
  end.


(** * JIT step, to be looped  *)
Definition jit_step (js:jit_state): res (jit_state * trace) :=
  do newps <- OK (profiler (prof_state js) (synchro js));
  match (next_status newps (nb_optim js)) with
  | Exe => do (int_state, newstack) <- forge_interpreter_state (prog js) (stack js) (synchro js);
            do (newsynchro, newmem, output) <- interpreter (prog js) int_state (mem js);
            OK (mk_jit_state
                  (prog js)
                  newps
                  newmem
                  newstack
                  newsynchro
                  (nb_optim js)
                , output)
  | Opt => do newp <- OK (safe_optimize newps (prog js));
            OK (mk_jit_state
                  newp
                  newps
                  (mem js)
                  (stack js)
                  (synchro js)
                  (Nat.pred (nb_optim js)) (* removing one optimization *)
                , E0)
  end.


(* Is the JIT at a Final Value *)
(* Returning the final returned value of the JIT *)
Definition jit_final_value (js:jit_state): option value :=
  match (synchro js) with
  | S_Return v =>
    match (stack js) with
    | nil => Some v
    | _ => None
    end
  | Halt ints =>
    match ints with
    | Int_Final v => Some v
    | _ => None
    end
  | _ => None
  end.
  
(* Returning the program of a JIT state *)
(* Useful if we want to look at the optimizations a JIT performed *)
Definition jit_program (js:jit_state): program :=
  prog js.
