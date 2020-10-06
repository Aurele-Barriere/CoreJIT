(* Inlining *)
(* A pass of the dynamic optimizer *)
(* Copies the definition of a function instead of a function call *)

Require Export specIR.
Require Export def_regs.
Require Import Coq.MSets.MSetPositive.

(* Name Mangling: Registers and lables of the inlined function must be modified *)
(* to make sure that there is no conflict with the caller function *)
Definition shift: Type:= positive.

Definition shift_reg (s:shift) (r:reg): reg :=
  Pos.add r s.

Definition unshift_reg (s:shift) (r:reg): reg :=
  Pos.sub r s.

Definition shift_lbl (s:shift) (l:label): label :=
  Pos.add l s.

Definition unshift_lbl (s:shift) (l:label): label :=
  Pos.sub l s.

(* Shift operands *)
Definition shift_op (sr: shift) (o:op): op :=
  match o with
  | Reg r => Reg (shift_reg sr r)
  | Cst v => Cst v
  end.

(* Shift expressions *)
Definition shift_expr (sr:shift) (e:expr): expr :=
  match e with
  | Binexpr b o1 o2 => Binexpr b (shift_op sr o1) (shift_op sr o2)
  | Unexpr u o => Unexpr u (shift_op sr o)
  end.

(* For an assume or framestate, we don't want to change the left-hand side of a varmap, *)
(* Which refers to the original version registers *)
(* Transforms a varmap (right side only)  *)
Definition shift_vm (sr:shift) (vm:varmap): varmap :=
  map (fun re => (fst re, shift_expr sr (snd re))) vm.

Fixpoint shift_syl (sr:shift) (syl:list synth_frame): list synth_frame :=
  match syl with
  | nil => nil
  | (tgt,r,vm)::syl' => (tgt,r, shift_vm sr vm)::(shift_syl sr syl')
  end.

(* For a Move instruction though, both sides refers to the current function *)
(* Transforms a movelist (both sides) *)
Definition shift_ml (sr:shift) (ml:movelist): movelist :=
  map (fun re => (shift_reg sr (fst re), shift_expr sr (snd re))) ml.

(* Given functions to transform registers, expr and labels, transform an instruction *)
Definition transf_instr (i:instruction) (tl:label->label) (sr:shift): instruction :=
  match i with
  | Fail s => Fail s
  | Nop oh l => Nop oh (tl l)
  | Op e r l => Op (shift_expr sr e) (shift_reg sr r) (tl l)
  | Move vm l => Move (shift_ml sr vm) (tl l)
  | Call f le r l => Call f (List.map (shift_expr sr) le) (shift_reg sr r) (tl l)
  | IReturn e => IReturn (shift_expr sr e)
  | Cond e l1 l2 => Cond (shift_expr sr e) (tl l1) (tl l2)
  | Store e1 e2 l => Store (shift_expr sr e1) (shift_expr sr e2) (tl l)
  | Load e r l => Load  (shift_expr sr e) (shift_reg sr r) (tl l)
  | Printexpr e l => Printexpr (shift_expr sr e) (tl l)
  | Printstring str l => Printstring str (tl l)
  | Framestate tgt vm sl l => Framestate tgt (shift_vm sr vm) (shift_syl sr sl) (tl l)
  | Assume le tgt vm sl l => Assume (List.map (shift_expr sr) le) tgt (shift_vm sr vm) (shift_syl sr sl) (tl l)
  end.

(* Synthesizing a new stackframe for the inlined metadata *)
(* In this case, tgt, vm and sl is the Metadata from the Framestate attached to the call to inline *)
(* retreg is the register where was stored the result of the call *)
(* the new stackframe to create is (tgt,retreg,vm) *)
(* If there was any extra stackframes in the attached Framestate, they go at the end *)
(* The extra stackframes that were already in the inlined call stay at the beginning *)
Definition stackframe_synthesis (tgt:deopt_target) (vm:varmap) (sl: list synth_frame) (retreg:reg) (i:instruction): instruction :=
  match i with
  | Framestate tgt' vm' sl' l' =>
    Framestate tgt' vm' (sl' ++ (tgt,retreg,vm)::sl) l'
  | Assume guard tgt' vm' sl' l' =>
    Assume guard tgt' vm' (sl' ++ (tgt,retreg,vm)::sl) l'
  | _ => i
  end.

(* Replacing return statements with an assignment to the return register, and goes to next label *)
Definition replace_return (retreg:reg) (retlbl:label) (i:instruction): instruction :=
  match i with
  | IReturn e => Op e retreg retlbl
  | _ => i
  end.

(* Shift registers and labels of an instruction, replaces return statements *)
(* and add the new stackframes in the metadata *)
Definition inline_instr (shr:shift) (shl:shift) (retreg:reg) (retlbl:label) (tgt:deopt_target) (vm:varmap) (sl:list synth_frame) (i:instruction): instruction :=
  stackframe_synthesis tgt vm sl retreg
  (replace_return retreg retlbl
  (transf_instr i (shift_lbl shl) shr)).

(* Join the callee code (shifted) and the caller code *)
Definition join_code (callee caller:code) (shr shl:shift) (retreg:reg) (retlbl:label) (tgt:deopt_target) (vm:varmap) (sl:list synth_frame): code :=
  fold_left (fun c lbli => PTree.set (shift_lbl shl (fst lbli)) (inline_instr shr shl retreg retlbl tgt vm sl (snd lbli)) c)
           (PTree.elements callee) caller.

(* get the max register used in the caller function *)
(* Once this max reg computed, we know how to shift the callee registers *)
(* And avoid collisions *)
Definition max_reg_op (o:op): reg :=
  match o with
  | Reg r => r
  | Cst v => xH
  end.

Definition max_reg_expr (e:expr): reg :=
  match e with
  | Binexpr b o1 o2 => Pos.max (max_reg_op o1) (max_reg_op o2)
  | Unexpr u o => max_reg_op o
  end.

(* Only the right hand side: for metadata *)
Definition max_reg_varmap (r:varmap) : reg :=
  fold_left (fun p re => Pos.max p (max_reg_expr (snd re))) r xH.

(* Both sides: for movelist *)
Definition max_reg_movelist (ml:movelist) : reg :=
  fold_left (fun p re => Pos.max p (Pos.max (fst re) (max_reg_expr (snd re)))) ml xH.

Definition max_reg_listexpr (le:list expr): reg :=
  fold_left (fun p e => Pos.max p (max_reg_expr e)) le xH.

Definition max_reg_synth_list (syl:list synth_frame) : reg :=
  fold_left (fun p sy => Pos.max p (max_reg_varmap (snd sy))) syl xH.

Definition max_reg_instr (i:instruction): reg :=
  match i with
  | Fail s => xH
  | Nop oh l => xH
  | Op e r l => Pos.max r (max_reg_expr e)
  | Move ml next => max_reg_movelist ml
  | Call f le r l => Pos.max r (max_reg_listexpr le)
  | IReturn e => max_reg_expr e
  | Cond e l1 l2 => max_reg_expr e
  | Store e1 e2 l => Pos.max (max_reg_expr e1) (max_reg_expr e2)
  | Load e r l => Pos.max r (max_reg_expr e)
  | Printexpr e l => max_reg_expr e
  | Printstring str l => xH
  | Framestate tgt vm sl l => Pos.max (max_reg_varmap vm) (max_reg_synth_list sl)
  | Assume g tgt vm sl l => Pos.max (Pos.max (max_reg_listexpr g) (max_reg_varmap vm)) (max_reg_synth_list sl)
  end.

Definition max_reg_code (c:code): reg :=
  PTree.fold1 (fun p i => Pos.max p (max_reg_instr i)) c xH.

(* Computing max label used in the caller, to shift the callee labels without collisions *)
(* The maximum label which has code associated to *)
Definition max_lbl_code (c:code): label :=
  max_label c.

(* finds a label that is fresh for c and that isn't l *)
Definition fresh_label' (c:code) (l:label) : label :=
  Pos.succ (Pos.max l (max_label c)).

(* Assign parameters in a single Move instruction *)
(* To do so, we first need to create the varmap that will be used *)
Fixpoint make_movelist (le:list expr) (params:list reg) (sr:shift): res movelist :=
  match le with
  | nil => match params with
          | nil => OK nil
          | _ => Error ("not enough arguments")
          end
  | expr::le' => match params with
               | nil => Error ("too many arguments")
               | r::params' =>
                 do vm <- make_movelist le' params' sr;
                   OK ((shift_reg sr r, expr)::vm)
               end
  end.

Definition param_assign (c:code) (call_lbl:label) (linl:label) (le:list expr) (params:list reg) (sr:shift) : res code :=
  do ml <- make_movelist le params sr;
    OK (PTree.set call_lbl (Move ml linl) c).

Definition inline_version (caller:version) (callee:version) (call_lbl:label) (args:list expr) (retreg:reg) (next:label) (tgt:deopt_target) (vm:varmap) (sl:list synth_frame) (params:list reg): res version :=
  do shr <- OK (max_reg_code (ver_code caller));
    do shl <- OK (max_lbl_code (ver_code caller));
    do inline_start <- OK (shift_lbl shl (ver_entry callee));
    do inline_code <- OK (join_code (ver_code callee) (ver_code caller) shr shl retreg next tgt vm sl);
    do paramcode <- param_assign inline_code call_lbl inline_start args params shr;
    OK (mk_version paramcode (ver_entry caller)).

(* Checking that the synth_list is empty *)
Definition check_synth_list (sl:list synth_frame): res unit :=
  match sl with
  | nil => OK tt
  | _ => Error "For now, inlining cannot be nested in that direction"
  end.

(* Checking that an element is exactly (retreg, Unexpr Assign (Reg retreg)) *)
Definition check_reconstructed (retreg:reg) (re:reg * expr) : bool :=
  match re with
  | (r,e) =>
    match (Pos.eqb r retreg) with
    | true =>
      match e with
      | Unexpr Assign o =>
        match o with
        | Reg r' => (Pos.eqb r' retreg)
        | _ => false
        end
      | _ => false
      end
    | _ => false
    end
  end.

(* Checking that the vm of the Framestate can be evaluated *)
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

Fixpoint check_varmap_progress (vm:varmap) (def:regset): bool :=
  match vm with
  | nil => true
  | (r,e)::vm' => andb (check_expr e def) (check_varmap_progress vm' def)
  end.

(* Checking that the varmap has a correct form *)
Definition reg_neq (r1:reg) (r2:reg) : bool :=
  negb (Pos.eqb r1 r2).

Definition op_no_use (r:reg) (o:op) : bool :=
  match o with
  | Reg r' => reg_neq r r'
  | Cst _ => true
  end.

Definition expr_no_use (r:reg) (e:expr) :=
  match e with
  | Binexpr _ o1 o2 => andb (op_no_use r o1) (op_no_use r o2)
  | Unexpr _ o => op_no_use r o
  end.

Definition varmap_no_use (r:reg) (vm:varmap): bool :=
  fold_left (fun b re => andb b (andb (reg_neq r (fst re)) (expr_no_use r (snd re)))) vm true.


(* Checking that the varmap is correct for inlining *)
(* In this case, we ask the varmap to contain the assignment (retreg<-retreg), *)
(* And that retreg should only appear here *)
(* In this first version, we check that this is the beginning of the varmap *)
(* We could extend that to varmaps where (retreg<-retreg) appears in the middle *)
Definition check_vm (vm:varmap) (retreg:reg) (abs:abs_dr): res unit :=
  match abs with
  | FlatRegset.Inj def =>
    match (check_varmap_progress vm def) with
    | true =>
      match vm with
      | nil => Error "the varmap does not capture the return register"
      | a::vm' =>
        match (andb (check_reconstructed retreg a) (varmap_no_use retreg vm')) with
        | true => OK tt
        | false => Error "The varmap doesn't have the desired form"
        end
      end
    | false => Error "The analysis can't guarantee progress preservation"
    end
  | _ => Error "The analysis didn't converger"
  end.

(* The deopt target of the Framestate should point to a valid function *)
Definition check_tgt (tgt:deopt_target) (p:program) : res unit :=
  match find_base_version (fst tgt) p with
  | None => Error "Invalid deopt target in the Framestate"
  | _ => OK tt
  end. 

(* The optimization pass *)
(* The profiler should send the label of the call to inline *)
Definition optimize_inline (fidoptim:fun_id) (call_lbl:label) (p:program): res program :=
  do func <- try_op (find_function fidoptim p) "Can't find the function to optimize";
    do caller <- OK (current_version func);
    match (ver_code caller)!call_lbl with
    | Some (Call fid le retreg nextlbl) =>
      match (ver_code caller)!nextlbl with (* making sure that the next lbl is a Framestate *)
      | Some (Framestate tgt vm sl nextlbl') =>
        do abs <- try_op (defined_regs_analysis (ver_code caller) (fn_params func) (ver_entry caller)) "Def_regs analysis failed";
          do def_regs <- OK(absstate_get call_lbl abs);
          do sl_check <- check_synth_list sl;
          do vm_check <- check_vm vm retreg def_regs;
          do tgt_check <- check_tgt tgt p;
          do callee_function <- try_op (find_function fid p) "Function to inline not found";
          do callee <- OK (current_version callee_function);
          do newver <- inline_version caller callee call_lbl le retreg nextlbl tgt vm sl (fn_params callee_function);
          OK(set_version p fidoptim newver)
      | _ => Error "The call to inline isn't folllowed directly with a Framestate instruction"
      end
    | _ => Error "no call to inline"
    end.
    

Definition safe_optimize_inline (fidoptim:fun_id) (call_lbl:label) (p:program): program :=
  safe_res (optimize_inline fidoptim call_lbl) p.

