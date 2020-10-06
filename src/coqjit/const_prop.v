(* Constant propagation *)
(* A pass of the dynamic optimizer *)
Require Export List.
Require Export Coqlib.
Require Export Maps.
Require Export specIR.
Require Export Kildall.
Require Export Lattice.
Require Export interpreter.

(* Decidable equality over values *)
Definition value_eq_dec: forall x y:value, {x = y} + {x <> y}.
  intros [x] [y].
  assert ({x=y} + {x<>y}) by apply Z.eq_dec.
  destruct H.
  - left. f_equal. auto.
  - right. unfold not; intros. inv H. apply n. auto.
Qed.  

Module ValueEq <: EQUALITY_TYPE.
  Definition t:Type := value.
  Definition eq := value_eq_dec.
End ValueEq.

(* the flat lattice for values in constant propagation *)
Module FlatValue := LFlat (ValueEq).
Definition abs_value: Type := FlatValue.t.
(* In this optimization, *)
(* Top means non-constant *)
(* Inj v means the value is constant and equal to v *)
(* Bot means we don't know yet *)
(* Every abstract register starts as Bot, and in the end of the analysis, is either Top or Inj *)

(* The lattice for maps from registers to flat values *)
Module MapFlatValue := LPMap (FlatValue).

(* A data-flow solver, implemented with Kildall algo, for constant propagation *)
Module DS := Dataflow_Solver (MapFlatValue) (NodeSetBackward).

(* Associating an abstract value to each registers *)
Definition abs_regmap: Type := MapFlatValue.t.
Definition init_abs_regmap: abs_regmap := MapFlatValue.bot.

(* Associating an abstract regmap to each label in the code *)
Definition abs_state : Type := PMap.t abs_regmap.
Definition init_abs_state : abs_state := PMap.init init_abs_regmap.

(* Evaluating registers in a map of flat values *)
Definition eval_reg_abs (r:reg) (arm:abs_regmap) : abs_value :=
  MapFlatValue.get r arm.

(* Evaluating operands in a map of flat values *)
Definition eval_op_abs (o:op) (arm:abs_regmap) : abs_value :=
  match o with
  | Cst n => FlatValue.Inj n    (* We know for sure what values constants are *)
  | Reg r => eval_reg_abs r arm
  end.

Definition eval_binop_abs (bo:bin_operation) (o1:op) (o2:op) (arm:abs_regmap) : abs_value :=
  match (eval_op_abs o1 arm) with
  | FlatValue.Top => FlatValue.Top
  | FlatValue.Bot => match (eval_op_abs o2 arm) with
                     | FlatValue.Top => FlatValue.Top
                     | _ => FlatValue.Bot
                     end
  | FlatValue.Inj v1 => match (eval_op_abs o2 arm) with
                       | FlatValue.Inj v2 =>
                         match (eval_binop_values bo v1 v2) with
                         | OK inj => FlatValue.Inj inj
                         | Error _ => FlatValue.Top (* evaluation error *)
                         end
                        | FlatValue.Top => FlatValue.Top
                        | FlatValue.Bot => FlatValue.Bot
                        end
  end.

Definition eval_unop_abs (u:un_operation) (o:op) (arm:abs_regmap) : abs_value :=
  match (eval_op_abs o arm) with
  | FlatValue.Inj v => match (eval_unop_value u v) with
                      | OK inj => FlatValue.Inj inj
                      | Error _ => FlatValue.Top (* evaluation error *)
                      end
  | FlatValue.Bot => FlatValue.Bot
  | FlatValue.Top => FlatValue.Top
  end.

Definition eval_expr_abs (e:expr) (arm:abs_regmap): abs_value :=
  match e with
  | Binexpr b o1 o2 => eval_binop_abs b o1 o2 arm
  | Unexpr u o => eval_unop_abs u o arm
  end.

(* Transforming the abstract state *)
Definition regmap_join (arm1:abs_regmap) (arm2:abs_regmap) : abs_regmap :=
  MapFlatValue.lub arm1 arm2.

Definition regmap_set (r:reg) (absval:abs_value) (arm:abs_regmap) : abs_regmap :=
  MapFlatValue.set r absval arm.

Definition absstate_set (pc:label) (arm:abs_regmap) (abs:abs_state) : abs_state :=
  PMap.set pc arm abs.

Definition absstate_get (pc:label) (abs:abs_state) : abs_regmap :=
  PMap.get pc abs.

Definition get_lbl_list (c:code) :=
  List.map fst (PTree.elements c).

Definition ptree_list_add {A:Type} (p:positive) (a:A) (t:PTree.t (list A)) :=
  match (t # p) with
  | None => t # p <- (a::nil)
  | Some l => t # p <- (a::l)
  end.


(* If we know that e is true, update arm accordingly *)
Definition generate_true (arm:abs_regmap) (e:expr): abs_regmap :=
  match e with
  | Binexpr Eq (Reg r) (Cst v) => regmap_set r (FlatValue.Inj v) arm
  | Binexpr Eq (Cst v) (Reg r) => regmap_set r (FlatValue.Inj v) arm
  | Binexpr Eq (Reg r1) (Reg r2) => arm (* TODO: I'm not sure yet. Is that copy propagation? *)
  | Unexpr Neg (Reg r) => regmap_set r (FlatValue.Inj (Vint 0)) arm
  | _ => arm
  end.

(* If we know that e is false, update arm accordingly *)
Definition generate_false (arm:abs_regmap) (e:expr): abs_regmap :=
  match e with
  | Unexpr Assign (Reg r) => regmap_set r (FlatValue.Inj (Vint 0)) arm
  | _ => arm
  end.

(* Update arm if a list of expressions is true (for assume) *)
Fixpoint generate_true_list (arm:abs_regmap) (le:list expr): abs_regmap :=
  match le with
  | nil => arm
  | e::le' => generate_true_list (generate_true arm e) le'
  end.

(* For the Move, we need to update each register with the abstract expression *)
Fixpoint list_transf' (ml:movelist) (arm_eval:abs_regmap) (arm:abs_regmap) : abs_regmap :=
  match ml with
  | nil => arm
  | (r,e)::ml' => let abs_e := eval_expr_abs e arm_eval in
                regmap_set r abs_e (list_transf' ml' arm_eval arm)
  end.

Definition list_transf (ml:movelist) (arm:abs_regmap) : abs_regmap :=
  list_transf' ml arm arm.  

(* In code c, at label l, update information in abs_regmap *)
Definition constprop_transf (c:code) (l:label) (arm:abs_regmap) : abs_regmap :=
  match c!l with
  | None => arm
  | Some instr => match instr with
                 | Op expr retreg next =>
                   let abs_e := eval_expr_abs expr arm in
                   regmap_set retreg abs_e arm
                 | Move ml next =>
                   list_transf ml arm
                 | Call fid args retreg next => (* calls can return anything *)
                   regmap_set retreg FlatValue.Top arm 
                 | Load ad reg next => (* don't analyze the memory *)
                   regmap_set reg FlatValue.Top arm
                 | Assume le (fa, la) vm synth next =>
                   (* If an Assume passes, we know the list of expressions was true *)
                   generate_true_list arm le
                 | _ => arm    (* other instructions don't change the registers *)
                  end
  end.

Fixpoint init_arm_params (l:list reg): abs_regmap :=
  MapFlatValue.top.

(* The result of the analysis on code [c] with entry [entry] *)
(* The result, if Some, is a map from labels to abs_regmap *)
(* At label [entry], we initially have init_arm_params *)
Definition kildall_constprop_analysis (c:code) (params:list reg) (entry:label): option abs_state:=
  DS.fixpoint
    (PTree.map1 instr_succ c)
    (constprop_transf c)
    ((entry,(init_arm_params params))::nil).


(* After the analysis, replace the known operands with constants *)
Definition replace_op (arm:abs_regmap) (o:op): op :=
  match (eval_op_abs o arm) with
  | FlatValue.Inj v => Cst v    (* replacing known values with constants *)
  | _ => o
  end.

Definition replace_op_list (arm:abs_regmap) (opl:list op): list op :=
  List.map (replace_op arm) opl.

Definition transf_expr (f:op -> op) (e:expr): expr :=
  match e with
  | Binexpr b o1 o2 => Binexpr b (f o1) (f o2)
  | Unexpr u o => Unexpr u (f o)
  end.

Definition transf_expr_list (f:op -> op) (exl:list expr): list expr :=
  List.map (transf_expr f) exl.

Definition transf_vm (f:expr -> expr) (vm:varmap): varmap :=
  List.map (fun re => (fst re, f (snd re))) vm.

Definition transf_ml (f:expr -> expr) (ml:movelist): movelist :=
  List.map (fun re => (fst re, f (snd re))) ml.

(* Apply a transformation on all operands of an instruction *)
Definition apply_transf_op (i:instruction) (f:op -> op): instruction :=
  let fe := transf_expr f in
  let fl := transf_expr_list f in
  let fv := transf_vm fe in
  let fm := transf_ml fe in
  match i with
  | Nop oh next => i
  | Op expr retreg next =>
    Op (fe expr) retreg next
  | Move ml next =>
    Move (fm ml) next       (* modifying only the right hand side *)
  | Call fid exl retreg next =>
    Call fid (fl exl) retreg next
  | IReturn ex =>
    IReturn (fe ex)
  | Cond ex lbl1 lbl2 =>
    Cond (fe ex) lbl1 lbl2
  | Store ex1 ex2 next =>
    Store (fe ex1) (fe ex2) next
  | Load ex reg next =>
    Load (fe ex) reg next
  | Printexpr ex next =>
    Printexpr (fe ex) next
  | Printstring str next =>
    Printstring str next
  | Assume exl (fid, l) vm sl next =>
    Assume (fl exl) (fid, l) (fv vm) sl next
  | Framestate (fid, l) vm sl next =>
    Framestate (fid, l) (fv vm) sl next
  | Fail s => Fail s
  end.

(* Apply a transformation on all expressions of an instruction *)
Definition apply_transf_expr (i:instruction) (f:expr -> expr): instruction :=
  match i with
  | Nop oh next => i
  | Op expr retreg next =>
    Op (f expr) retreg next
  | Move ml next =>
    Move (transf_ml f ml) next (* modifying only the right-hand side *)
  | Call fid exl retreg next =>
    Call fid (List.map f exl) retreg next
  | IReturn ex =>
    IReturn (f ex)
  | Cond ex lbl1 lbl2 =>
    Cond (f ex) lbl1 lbl2
  | Store ex1 ex2 next =>
    Store (f ex1) (f ex2) next
  | Load ex reg next =>
    Load (f ex) reg next
  | Printexpr ex next =>
    Printexpr (f ex) next
  | Printstring str next =>
    Printstring str next
  | Assume exl (fid, l) vm sl next =>
    Assume (List.map f exl) (fid, l) (transf_vm f vm) sl next
  | Framestate (fid, l) vm sl next =>
    Framestate (fid, l) (transf_vm f vm) sl next
  | Fail s => Fail s
  end.


(* Replace all operands in instructions when the values are known *)
Definition replace_ops (arm:abs_regmap) (i:instruction): instruction :=
  apply_transf_op i (replace_op arm).

(* Syntaxical equality of operands *)
Definition value_eqb (v1:value) (v2:value) : bool :=
  match v1 with
  | Vint it1 => match v2 with
               | Vint it2 => Z.eqb it1 it2
               end
  end.

Definition reg_eqb : reg -> reg -> bool := Pos.eqb.
  
Definition op_eqb (o1:op) (o2:op): bool :=
  match o1 with
  | Cst v1 => match o2 with
              | Cst v2 => value_eqb v1 v2
              | Reg _ => false
              end
  | Reg r1 => match o2 with
              | Cst _ => false
              | Reg r2 => reg_eqb r1 r2
              end
  end.                 

(* When their values are known, expressions can be simplified *)
Definition simpl_expr (e:expr): expr :=
  match e with
  | Binexpr binop (Cst v1) (Cst v2) =>
    match (eval_binop_values binop v1 v2) with
    | OK v => Unexpr Assign (Cst v)
    | Error _ => e
    end
  | Unexpr unop (Cst v) =>
    match (eval_unop_value unop v) with
    | OK v' => Unexpr Assign (Cst v')
    | Error _ => e
    end
  | _ => e
  end.

(* Some instructions can be simplified *)
Definition simpl_instr (i:instruction): instruction :=
  match i with
  (* All arguments known *)
  | Op expr retreg next =>
    Op (simpl_expr expr) retreg next
  | Cond expr iftrue iffalse =>
    match (simpl_expr expr) with
    | Unexpr Assign (Cst v) =>
      match v with 
      | Vint 0 => Nop None iffalse
      | Vint _ => Nop None iftrue           (* if the value is known, and <>0, then the true branch is taken *)
      end
    | _ => Cond (simpl_expr expr) iftrue iffalse
    end
  | Assume nil (fid, lbl) vm ls next => Nop None next
  | _ => i
  end.

(* This optimization is orthogonal to constant propagation *)
(* Here we assume Assign to be less costly than other instructions *)
Definition strength_reduction (e:expr): expr :=
  match e with
  | Binexpr Plus o (Cst (Vint 0)) => Unexpr Assign o
  | Binexpr Plus (Cst (Vint 0)) o => Unexpr Assign o
  | Binexpr Minus o (Cst (Vint 0)) => Unexpr Assign o
  | Binexpr Minus (Cst (Vint 0)) o => Unexpr UMinus o
  | Binexpr Minus o1 o2 => match (op_eqb o1 o2) with
                           | true => Unexpr Assign (Cst (Vint 0))
                           | false => e
                           end
  | Binexpr Mult o (Cst (Vint 0)) => Unexpr Assign (Cst (Vint 0))
  | Binexpr Mult (Cst (Vint 0)) o => Unexpr Assign (Cst (Vint 0))
  | Binexpr Mult o (Cst (Vint 1)) => Unexpr Assign o
  | Binexpr Mult (Cst (Vint 1)) o => Unexpr Assign o
  | Binexpr Gt o1 o2 => match (op_eqb o1 o2) with
                        | true => Unexpr Assign (Cst (Vint 0))
                        | false => e
                        end
  | Binexpr Lt o1 o2 => match (op_eqb o1 o2) with
                        | true => Unexpr Assign (Cst (Vint 0))
                        | false => e
                        end
  | Binexpr Geq o1 o2 => match (op_eqb o1 o2) with
                         | true => Unexpr Assign (Cst (Vint 1))
                         | false => e
                         end
  | Binexpr Leq o1 o2 => match (op_eqb o1 o2) with
                         | true => Unexpr Assign (Cst (Vint 1))
                         | false => e
                         end
  | Binexpr Eq o1 o2 => match (op_eqb o1 o2) with
                        | true => Unexpr Assign (Cst (Vint 1))
                        | false => e
                        end
  | _ => e
  end.
 
(* Having done the analysis, its result being in abs, transform instructions *)
Definition transf_instr (abs:abs_state) (pc:label) (instr:instruction): instruction :=
  apply_transf_expr (simpl_instr (replace_ops (absstate_get pc abs) instr)) strength_reduction.

(* Given a version, analyses it and replaces instructions *)
(* Each instruction of the source corresponds to one in the target *)
Definition constant_propagation_version (v:version) (params:list reg): res version :=
  do abs <- try_op (kildall_constprop_analysis (ver_code v) params (ver_entry v)) "Constant Propagation Analysis failed";
    OK(mk_version (PTree.map (transf_instr abs) (ver_code v)) (ver_entry v)).


(* Performs constant propagation in the optimized version of function fid *)
Definition constant_propagation (fid: fun_id) (p:program): res program :=
  do f <- try_op (find_function fid p) "Function to optimize not found";
    do v <- OK(current_version f); (* the optimized code if it exists, the base version otherwise *)
    do newv <- constant_propagation_version v (fn_params f);
    OK (set_version p fid newv).

Definition safe_constant_propagation (p:program) (fid:fun_id): program :=
  safe_res (constant_propagation fid) p.
