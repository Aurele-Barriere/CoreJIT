(* Optimizer: creates new optimized versions of programs *)

Require Export List.
Require Export Coqlib.
Require Export Maps.
Require Export specIR.
Require Export interpreter.
Require Export framestate_insertion.
Require Export assume_insertion.
Require Export assume_insertion_delay.
Require Export lowering.
Require Export const_prop.
Require Export inlining.
Require Export profiler_types.

(* Profiler state external type *)
Parameter profiler_state: Type.

(* Optimization heuristics *)
Parameter framestates_to_insert : profiler_state -> program -> list (fun_id * (list label)). (* First we insert framestates at various labels *)
Parameter optim_list : profiler_state -> program -> list (fun_id * optim_wish).
(* a list of optims to perform on a given function *)

(* Inserting Framestates in all functions according to the profiler wish *)
Fixpoint process_fs_list (p:program) (l:list (fun_id * list label)): program :=
  match l with
  | nil => p
  | (fid, fs_lbl)::l' => process_fs_list (safe_insert_framestate p fid fs_lbl) l'
  end.

(* Processing each optimization sugeested by the profiler *)
(* Using the safe optimizations: if one fails, it is just ignored by the optimizer *)
Fixpoint process_optim_list (p:program) (l:list (fun_id * optim_wish)): program :=
  match l with
  | nil => p
  | (fid, AS_INS le fs_lbl)::l' => process_optim_list (safe_insert_assume p fid le fs_lbl) l'
  | (fid, AS_INS_DELAY le fs_lbl)::l' => process_optim_list (safe_insert_assume_delay p fid le fs_lbl) l'
  | (fid, CST_PROP)::l' => process_optim_list (safe_constant_propagation p fid) l'
  | (fid, INLINE call_lbl)::l' => process_optim_list (safe_optimize_inline fid call_lbl p) l'
  | (_,   LOWER)::l' => process_optim_list (lowering p) l'
  end.


Definition optimize (ps:profiler_state) (p:program): res program :=
    do optims <- OK (optim_list ps p);
    do fs_list <- OK (framestates_to_insert ps p);
    do pfs <- OK (process_fs_list p fs_list);
    do newp <- OK (process_optim_list pfs optims);
    OK (lowering newp).

(* An error in optimization should not stop the execution *)
Definition safe_optimize (ps:profiler_state) (p:program): program :=
  safe_res (optimize ps) p.


(** * Testing optimizations  *)
(* This is not used by the JIT, simply used for testing the optimizations with safety off *)
Fixpoint unsafe_fs_list (p:program) (l:list (fun_id * list label)): res program :=
  match l with
  | nil => OK p
  | (fid, fs_lbl)::l' =>
    do newp <- insert_framestate fid fs_lbl p;
      unsafe_fs_list newp l'
  end.

Fixpoint unsafe_wishes (p:program) (l:list (fun_id * optim_wish)): res program :=
  match l with
  | nil => OK p
  | (fid, AS_INS le fs_lbl)::l' =>
    do newp <- insert_assume fid le fs_lbl p;
      unsafe_wishes newp l'
  | (fid, AS_INS_DELAY le fs_lbl)::l' =>
    do newp <- insert_assume_delay fid le fs_lbl p;
      unsafe_wishes newp l'
  | (fid, CST_PROP)::l' =>
    do newp <- constant_propagation fid p;
      unsafe_wishes newp l'
  | (fid, INLINE call_lbl)::l' =>
    do newp <- optimize_inline fid call_lbl p;
      unsafe_wishes newp l'
  | (_, LOWER)::l' =>
    do newp <- OK (lowering p);
      unsafe_wishes newp l'
  end.

Definition test_optimizer (p:program) (fs_list: list (fun_id * (list label))) (wishes:list (fun_id * optim_wish)) : res program :=
  do fsp <- unsafe_fs_list p fs_list;
    unsafe_wishes fsp wishes.
