(* Framestate insertion: inserting Framestate instructions *)
(* Such instructions act as templates for the insertion of speculation *)
(* This is the first pass of the dynamic optimizer *)

Require Export List.
Require Export Coqlib.
Require Export Maps.
Require Export specIR.
Require Import Coq.MSets.MSetPositive.
Require Export liveness.
Require Export def_regs.

(* The identity varmap for the set of defined registers *)
(* Maps to each defined register its current value *)
Definition identity_varmap (rs:regset) : varmap :=
  map (fun r => (r, Unexpr Assign (Reg r))) (PositiveSet.elements rs).

Definition defined_rs (abs:def_abs_state) (l:label) : option regset :=
  match (def_absstate_get l abs) with
  | DefFlatRegset.Top => None       (* The analysis wasn't precise enough *)
  | DefFlatRegset.Inj rs => Some rs
  | DefFlatRegset.Bot => None       (* Did not converge *)
  end.

(* The list of labels where we must insert Framestates has to be cleaned *)
(* We can't allow inserting twice at the same place: no duplicates in the list *)
(* And labels must be associated with some code in the original code *)
(* And we can't insert if the analysis failed to get the exact set of defined registers *)
Definition remove_dup (l:list label): list label := nodup Pos.eq_dec l.

Definition is_used (c:code) (l:label) : bool :=
  match (c # l) with
  | Some _ => true
  | None => false
  end.
Definition filter_unused (c:code) (l:list label) := filter (is_used c) l.

Definition is_analyzed (abs:def_abs_state) (l:label) : bool :=
  match (defined_rs abs l) with
  | Some _ => true
  | None => false
  end.

Definition filter_analyzed (abs:def_abs_state) (l:list label) := filter (is_analyzed abs) l.

Definition clean_label_list (def:def_abs_state) (c:code) (l:list label) : list label :=
  filter_analyzed def (filter_unused c (remove_dup l)).

(* The spacing between the inserted Framestate and the replaced instruction *)
(* Used as heuristics for the fresh_label procedure *)
Parameter spacing: positive.

Definition insert_single_framestate (base_c:code) (c:code) (fid:fun_id) (lbl:label) (live:live_abs_state) (def:def_abs_state): res code :=
  do instr <- try_op (c # lbl) "Label is not used in the function"; (* this shouldn't happen (filter_unused) *)
  do rs_def <- try_op (defined_rs def lbl) "Defined regs analysis failed"; (* this shouldn't happen (filter_analyzed) *)
  do rs_live_before <- OK (live_dr_transf base_c lbl (live_absstate_get lbl live));
  (* base_c is needed to remember what was the code like before 
     all the optimisations, in order to apply the transfer function *)
  do identity <- OK (identity_varmap (PositiveSet.inter rs_def rs_live_before));
  (* we assign all the registers that are both defined at the instruction 
     and live before the instruction *)
  do freshlbl <- OK (fresh_label (Pos.add lbl spacing) c);
  do move_instr <- OK (c # freshlbl <- instr); (* moving the old instruction *)
  (* constructing the Framestate instruction *)
  do fs_instr <- OK (Framestate (fid, lbl) identity nil freshlbl); (* deoptimizing to the same function *)
  do new_code <- OK (move_instr # lbl <- fs_instr);           (* inserting the framestate *)
  OK new_code.


Fixpoint insert_list_framestate (base_c:code) (c:code) (fid:fun_id) (lbllist:list label) (live:live_abs_state) (def:def_abs_state): res code :=
  match lbllist with
  | nil => OK c
  | lbl::l => do newc <- insert_single_framestate base_c c fid lbl live def;
              insert_list_framestate base_c newc fid l live def
  end.

Definition fs_insert_version (v:version) (fid:fun_id) (lbllist:list label) (live:live_abs_state) (def:def_abs_state) : res version :=
  do code_ins <- insert_list_framestate (ver_code v) (ver_code v) fid lbllist live def;
  OK (mk_version code_ins (ver_entry v)).

(* Returns the base version and checks that there is no optimized version *)
Definition check_no_opt (f:function): res version :=
  match (fn_opt f) with
  | None => OK (fn_base f)
  | Some _ => Error "Insertion in previously optimized functions is not supported yet"
  end.

(* fid is the identifier of the function to insert framestate in *)
(* lbllist is the places we want to insert framestates at, just before the current instruction *)
Definition insert_framestate (fid:fun_id) (lbllist: list label) (p:program) : res program :=
  do f <- try_op (find_function fid p) "Function to optimize not found";
  do v <- check_no_opt f;      (* gets the base version and checks that there is no opt version *)
  do params <- OK (fn_params f);
  do live <- try_op (liveness_analyze v) "Liveness analysis failed";
  do def <- try_op (defined_regs_analysis (ver_code v) (fn_params f) (ver_entry v)) "Def_regs analysis failed";
  do code <- OK (ver_code v);
  do clean_list <- OK (clean_label_list def code lbllist);
  do new_ver <- fs_insert_version v fid clean_list live def;
  do new_prog <- OK (set_version p fid new_ver);
  OK (new_prog).

(* Tries to insert all possible Framestates *)
Definition insert_all_framestates (fid:fun_id) (p:program): res program :=
  do f <- try_op (find_function fid p) "Function to optimize not found";
  do v <- check_no_opt f;      (* gets the base version and checks that there is no opt version *)
  do params <- OK (fn_params f);
  do live <- try_op (liveness_analyze v) "Liveness analysis failed";
  do def <- try_op (defined_regs_analysis (ver_code v) (fn_params f) (ver_entry v)) "Def_regs analysis failed";
  do code <- OK (ver_code v);
  do clean_list <- OK (clean_label_list def code (map fst (PTree.elements code)));
  do new_ver <- fs_insert_version v fid clean_list live def;
  do new_prog <- OK (set_version p fid new_ver);
  OK (new_prog).


Definition safe_insert_framestate (p:program) (fid: fun_id) (lbllist:list label): program :=
  safe_res (insert_framestate fid lbllist) p.
