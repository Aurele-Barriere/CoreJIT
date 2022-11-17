(* Assume insertion: inserting Assume instructions *)
(* A pass of the dynamic optimizer *)
(* To insert an assume, you need a guard (what to speculate on) *)
(* And you need a label where there is a framestate, that you want to copy the metadata of *)
(* And the Assume is inserted next to that Framestate instruction *)

Require Export List.
Require Export Coqlib.
Require Export Maps.
Require Export specIR.
Require Import Coq.MSets.MSetPositive.
Require Export def_regs.

(** * Guard checking  *)
(* To ensure that the Assume does not intriduce bugs, *)
(* We check that the guard can evaluate without errors *)
Definition check_reg (r:reg) (def:regset) : bool :=
  PositiveSet.mem r def.

Definition check_op (o:op) (def:regset) : bool :=
  match o with
  | Reg r => check_reg r def
  | Cst _ => true
  end.

Definition check_expr (e:expr) (def:regset): bool :=
  match e with
  | Binexpr _ o1 o2 => andb (check_op o1 def) (check_op o2 def)
  | Unexpr _ o => check_op o def
  end.

(* making sure that the guard can evaluate, given a set of defined registers *)
Fixpoint check_guard (guard:list expr) (def:regset): bool :=
  match guard with
  | nil => true
  | e::guard' =>
    andb (check_expr e def) (check_guard guard' def)
  end.   


(** * The optimization that inserts Assume directly after the Framestate *)

(* Verify that the assume can be inserted: no code between assume and Framestate *)
Definition validator (v:version) (fs_lbl: label) (guard:list expr) (params: list reg): res unit :=
  match ((ver_code v)#fs_lbl) with
  | Some (Framestate _ _ _ next) =>
    do abs <- try_op (defined_regs_analysis (ver_code v) params (ver_entry v)) "Def_regs analysis failed";
      do def_regs <- OK(def_absstate_get fs_lbl abs);
      match def_regs with
      | DefFlatRegset.Inj def =>
        match (check_guard guard def) with
        | true => OK tt
        | false => Error "The guard might evaluate to an error"
        end
      | DefFlatRegset.Top => Error "The analysis couldn't get the exact set of defined registers: TOP"
      | DefFlatRegset.Bot => Error "The analysis couldn't get the exact set of defined registers: BOT"
      end
  | _ => Error "Not pointing to a valid Framestate"
  end.

(* Returns the version where the Assume has been inserted *)
Definition insert_assume_version (v:version) (fid:fun_id) (guard:list expr) (fsl:label) (params:list reg): res version :=
  do code <- OK(ver_code v);
    do freshlbl <- OK (fresh_label (Pos.succ fsl) code);
    do _ <- validator v fsl guard params; (* validating that the assume can be inserted *)
    match code # fsl with
    | Some (Framestate tgt vm sl next) =>
      do instr <- try_op (code # next) "Next Label is not used in the function";
        do update_fs <- OK (code # fsl <- (Framestate tgt vm sl freshlbl));
        do new_code <- OK (update_fs # freshlbl <- (Assume guard tgt vm sl next));
        (* in the new assume, the deopt target, the varmap and the synth list are copied from the framestate *)
        OK (mk_version new_code (ver_entry v))
    | _ => Error "Not pointing to a valid Framestate"
    end.

(* The optimization pass *)
Definition insert_assume (fid: fun_id) (guard:list expr) (fs_lbl: label) (p:program): res program :=
  do f <- try_op (find_function fid p) "Function to optimize not found";
    do v <- OK(current_version f); (* the optimized code if it exists, the base version otherwise *)
    do newv <- insert_assume_version v fid guard fs_lbl (fn_params f);
    do new_program <- OK (set_version p fid newv);
    OK (new_program).
    

Definition safe_insert_assume (p:program) (fid:fun_id) (guard:list expr) (fs_lbl: label): program :=
  safe_res (insert_assume fid guard fs_lbl) p.
