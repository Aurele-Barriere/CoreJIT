(* Assume insertion Delay: inserting Assume instruction *)
(* This versions tries to insert an Assume after a Condition Instruction *)
(* This showcases the possible separation of Framestate and Assume *)
(* This is a pass of the dynamic optimizer *)

Require Export List.
Require Export Coqlib.
Require Export Maps.
Require Export specIR.
Require Export assume_insertion.

(* Checks that a label is not in a list *)
Fixpoint not_in_list (l:list label) (lbl:label): bool :=
  match l with
  | nil => true
  | lbl'::l' =>
    match (Pos.eqb lbl' lbl) with
    | true => false
    | false => not_in_list l' lbl
    end
  end.

(* Check that an instruction has for only predecessor some label *)
Definition only_pred (c:code) (next:label) (pred:label): bool :=
  PTree.fold
    (fun b lbl i =>
       andb b
            (match (Pos.eqb lbl pred) with
             | true => true (* at the predecessor, we can point to next *)
             | false => not_in_list (instr_succ i) next (* elsewehere, next should not be a successor *)
             end))
    c true.


(* Verify that the assume can be inserted after a Cond Instruction *)
Definition validator (v:version) (fs_lbl: label) (guard:list expr) (params:list reg): res unit :=
  match ((ver_code v)#fs_lbl) with
  | Some (Framestate _ _ _ next) =>
    match ((ver_code v)#next) with
    | Some (Cond _ iftrue _) =>
      match (only_pred (ver_code v) next fs_lbl) with
      | true => 
        match (Pos.eqb next (ver_entry v)) with
        | false =>
          do abs <- try_op (defined_regs_analysis (ver_code v) params (ver_entry v)) "Def_regs analysis failed";
            do def_regs <- OK(def_absstate_get next abs);
            match def_regs with
            | DefFlatRegset.Inj def =>
              match (check_guard guard def) with
              | true => OK tt
              | false => Error "The guard might evaluate to an error"
              end
            | _ => Error "The analysis couldn't get the exact set of defined registers"
            end
        | true => Error "The Condition is the entry of the version"
        end
      | false => Error "The Framestate instruction does not dominate the Condition"
      end
    | _ => Error "No Condition instruction after the Framestate"
    end
  | _ => Error "Not pointing to a valid Framestate"
  end.

(* Returns the version where the Assume has been inserted *)
Definition insert_assume_version (v:version) (fid:fun_id) (guard:list expr) (fsl:label) (params:list reg): res version :=
  do code <- OK(ver_code v);
    do _ <- validator v fsl guard params; (* validating that the assume can be inserted *)
    match code # fsl with
    | Some (Framestate tgt vm sl next) =>
      match code # next with
      | Some (Cond condexpr iftrue iffalse) =>
        do freshlbl <- OK (fresh_label (Pos.succ next) code);
        do instr <- try_op (code # iftrue) "Next Label is not used in the function";
          do update_cond <- OK (code # next <- (Cond condexpr freshlbl iffalse));
          do new_code <- OK (update_cond # freshlbl <- (Assume guard tgt vm sl iftrue));
          (* in the new assume, the deopt target, the varmap and the synth list are copied from the framestate *)
          OK (mk_version new_code (ver_entry v))
      | _ => Error "The instruction after the Framestate is not a Cond Instruction"
      end
    | _ => Error "Not pointing to a valid Framestate"
    end.

(* The optimization pass *)
Definition insert_assume_delay (fid: fun_id) (guard:list expr) (fs_lbl: label) (p:program): res program :=
  do f <- try_op (find_function fid p) "Function to optimize not found";
    do v <- OK(current_version f); (* the optimized code if it exists, the base version otherwise *)
    do newv <- insert_assume_version v fid guard fs_lbl (fn_params f);
    do new_program <- OK (set_version p fid newv);
    OK (new_program).
    

Definition safe_insert_assume_delay (p:program) (fid:fun_id) (guard:list expr) (fs_lbl: label): program :=
  safe_res (insert_assume_delay fid guard fs_lbl) p.
