(* Lowering: remove framestates, keep assume instruction *)
(* Lowers programs into our final intermediate representation *)
(* This is the last pass of the dynamic optimizer *)

Require Export List.
Require Export Coqlib.
Require Export Maps.
Require Export specIR.


(* Framestates are replaced with Nop *)
Definition transf_instr (i:instruction) : instruction :=
  match i with
  | Framestate _ _ _ next => Nop None next
  | _ => i
  end.

(* replace each instruction in the code *)
Definition lowering_code (c:code) : code :=
  PTree.map1 transf_instr c.

(* Keeping the same entry point *)
Definition lowering_version (v:version) : version :=
  mk_version (lowering_code (ver_code v)) (ver_entry v).

Definition lowering_function (f:function) : function :=
  match (fn_opt f) with
  | None => f
  | Some vopt => 
    mk_function (fn_params f) (fn_base f) (Some (lowering_version vopt)) (base_no_spec f)
  end.

(* We lower the entire program *)
(* We could only lower the modified versions for more efficiency *)
Definition lowering (p:program): program :=
  mk_program (prog_main p)
             (PTree.map1 lowering_function (prog_funlist p)).      
