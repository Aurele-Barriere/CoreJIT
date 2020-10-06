(* The intermediate language of our JIT *)
(* Designed to make speculative optimizations easier *)
(* Inspired by CompCert's RTL and Sourir *)
(* At first, input programs have no optimized versions. *)
(* The framestate insertion inserts framestate instructions *)
(* Dynamic Optimizations and Assume Insertion modify a specIR program *)
(* Lowering transforms a specIR program into a lowered one with no framestate *)

Require Export String.
Require Export ZArith.
Require Export Znumtheory.
Require Export List.
Require Export Maps.
Require Export common.
Require Export events.
Require Export values.
Require Export Smallstep.

(** * Syntax  *)
(* Registers *)
Definition reg: Type := positive.

(* Operands are either registers names or integer constants or addresses *)
Inductive op: Type :=
| Reg : reg -> op
| Cst: value -> op.

(* Labels of the Control-Flow Graph *)
Definition label: Type := positive.

(* Operations and Expressions *)
Inductive bin_operation: Type :=
| Plus : bin_operation          (* CompCert's "Plus" notation for smallstep has been renamed "SPlus" *)
| Minus : bin_operation
| Mult : bin_operation
| Gt : bin_operation
| Lt : bin_operation
| Geq : bin_operation
| Leq : bin_operation
| Eq: bin_operation.

Inductive un_operation: Type :=
| UMinus : un_operation
| Neg : un_operation
| Assign : un_operation.

Inductive expr: Type :=
| Binexpr: bin_operation -> op -> op -> expr
| Unexpr: un_operation -> op -> expr.

(* Function names/identifiers *)
Definition fun_id: Type := positive.

(* Assigning multiple expressions to multiple registers for parallel assignment *)
Definition movelist: Type := list (reg * expr).

(* Binding registers to an expression, for deoptimizations *)
Definition varmap: Type := list (reg * expr).

Definition empty_varmap: varmap := nil.

(* Where to go to when deoptimizing *)
Definition deopt_target: Type := fun_id * label.

(* Information to synthesize new stack frames in an Assume instruction *)
Definition synth_frame: Type :=
  deopt_target * reg * varmap.

(* Instructions as a Control Flow Graph *)
Inductive instruction: Type :=
| Nop : option hint -> label -> instruction
(* [Nop oh next] simply goes to the [next] instruction. [oh] may be a hint for the profiler *)
| Op: expr -> reg -> label -> instruction
(* [Op expr reg next] evaluates [expr], puts the result in [reg] and moves to [next] *)
| Move: movelist -> label -> instruction
(* [Move l next] updates the left-hand side of [l] with an evaluation of its right-hand side *)
| Call : fun_id -> list expr -> reg -> label -> instruction
(* [Call f exl retreg next] puts the returned value of [(f exl)] in [retreg] and moves to [next] *)
| IReturn : expr -> instruction
(* [Return expr] evaluates [expr] and returns it *)
| Cond : expr -> label -> label -> instruction
(* [Cond expr iftrue iffalse] evaluates [expr]. If it is 0, move to [iffalse], else to [iftrue] *)
| Store : expr -> expr -> label -> instruction
(* [Store expr1 expr2 next] stores the value of [expr1] in address [expr2] and moves to [next] *)
| Load : expr -> reg -> label -> instruction
(* [Load expr reg next] loads the value at address [expr] puts it in reg [reg], and moves to [next] *)
| Printexpr : expr -> label -> instruction
(* [Printexpr expr next] prints the value of [expr] and moves to [next] *)
| Printstring : string -> label -> instruction
(* [Printstring s next] prints the string [s] then moves to [next] *)
| Framestate : deopt_target -> varmap -> list synth_frame -> label -> instruction
(* [Framestate  (f,l) vm sl next] can either move to [next] or deoptimize to the base version of *)
(* function [f] label [l], reconstructing the original environment with [vm] and [sl] *)
| Assume : list expr -> deopt_target -> varmap -> list synth_frame -> label -> instruction
(* [Assume le (f,l) vm sl next] first evaluates [le]. If all expressions are true then, *)
(* it moves to [next]. Otherwise, we deoptimize to the base version of function [f] label [l] *)
(* with the registers updated with the evaluation of [vm] *)
(* each element of [sl] corresponds to a new stackframe to be synthesized *)
| Fail : string -> instruction.
(* [Fail s] has blocking semantics. The interpreter should fail with the error message s *)

(* Successors of an instruction *)
(* Only inside the specIR program, does not account for deoptimization *)
Definition instr_succ (i:instruction): list label :=
  match i with
  | Nop _ next => next::nil
  | Op _ _ next => next::nil
  | Move _ next => next::nil
  | Call _ _ _ next => next::nil
  | IReturn _ => nil
  | Cond _ next1 next2 => next1::(next2::nil)
  | Store _ _ next => next::nil
  | Load _ _ next => next::nil
  | Printexpr _ next => next::nil
  | Printstring _ next => next::nil
  | Framestate _ _ _ next => next::nil 
  | Assume _ _ _ _ next => next::nil
  | Fail _ => nil
  end.

(** * Multi-language Programs  *)

(* Some code for a function is a correspondence between labels and instructions *)
Definition code: Type := PTree.t instruction.

(* A version is some code and an entry point *)
Record version: Type := mk_version {
  ver_code: code;
  ver_entry: label;
}.

(* Defining base versions: no speculative (Framestate & Assume) instructions *)
Inductive is_spec: instruction -> Prop :=
| spec_assume: forall g tgt vm sl next,
    is_spec (Assume g tgt vm sl next)
| spec_framestate: forall tgt vm sl next,
    is_spec (Framestate tgt vm sl next).           

Definition base_code (c:code): Prop :=
  forall (pc:label) (i:instruction), c!pc = Some i -> ~ (is_spec i).

Definition base_version (v:version): Prop :=
  base_code (ver_code v).

(* A function contains a baseline version of the code, and may contain a speculative version as well if it has been optimized *)
Record function': Type := mk_function {
  fn_params : list reg;
  fn_base : version;
  fn_opt : option version;
  base_no_spec: base_version fn_base
}.

Definition function: Type := function'.

(* A program is a list of functions, associated with a fun_id, and the main function's id *)
Record program: Type := mk_program {
  prog_main : fun_id;
  prog_funlist : PTree.t function;
}.

(** * Semantics  *)
Definition find_function_list (fid:fun_id) (funlist:PTree.t function): option function :=
  funlist ! fid.

Definition find_function (fid:fun_id) (p:program): option function :=
  find_function_list fid (prog_funlist p).

(* Find a base version given a function id and a program *)
Definition find_base_version (fid:fun_id) (p:program): option version :=
  match (find_function fid p) with
  | None => None
  | Some f => Some (fn_base f)
  end.

(* Find current version in a function *)
Definition current_version (f:function): version :=
  match (fn_opt f) with
  | None => fn_base f
  | Some o => o
  end.

(* Find the current version of a function in a program *)
Definition find_currver (fid:fun_id) (p:program): option version :=
  match (find_function fid p) with
  | None => None
  | Some f => Some (current_version f)
  end.

(* The state of all registers *)
Definition reg_map: Type := PTree.t value.
Definition empty_regmap: reg_map := PTree.empty value.

(* Stackframes *)
(* Return register, calling function, next instruction in calling function, state of the registers in calling function *)
Inductive stackframe: Type :=
| Stackframe : reg -> version -> label -> reg_map -> stackframe.

(* The stack model is simply a list of stack frames *)
(* The top of the stack is the head of the list *)
Definition stack: Type := list stackframe.


(** * Memory Model  *)
(* These are external parameters *)
Parameter mem_state: Type.
Parameter initial_memory: mem_state.
Parameter Load_: mem_state -> value -> option value.
Parameter Store_: mem_state -> value -> value -> option mem_state.


(** * Semantics sates *)
Inductive state: Type :=
| State:
    forall (s:stack)                 (* call stack *)
           (v:version)          (* current version being executed *)
           (pc:label)           (* current label *)
           (rm:reg_map)         (* state of the registers *)
           (ms:mem_state),      (* state of the memory *)
      state
| Final:                        (* go into final state after returning from function main *)
    forall (v:value)
           (ms:mem_state),
      state.

(* Final value if it exists *)
Definition final_value (s:state): option value :=
  match s with
  | State _ _ _ _ _ => None
  | Final v _ => Some v
  end.

(* Initial state of a program *)
Inductive initial_state (p:program): state -> Prop :=
| intro_init_state:
    forall f v
      (FINDF: find_function (prog_main p) p = Some f)
      (NOARGS: fn_params f = nil) (* the main function should have no parameters *)
      (CURRVER: current_version f = v),
      initial_state p (State nil v (ver_entry v) empty_regmap initial_memory).

Inductive final_state (p:program): state -> value -> Prop :=
| intro_final_state:
    forall v ms,
      final_state p (Final v ms) v.

(* Evaluating operands *)
Inductive eval_op : op -> reg_map -> value -> Prop :=
| Eval_const: forall n rm, eval_op (Cst n) rm n
| Eval_reg: forall v r rm
              (GETRM: rm # r = Some v),
    eval_op (Reg r) rm v.

(* Conditions are done on values *)
Definition bool_to_val (b:bool): value :=
  match b with
  | true => Vint 1
  | false => Vint 0
  end.


(* Evaluating Binary operations on values *)
Inductive eval_binop_values: bin_operation -> value -> value -> value -> Prop :=
| Eval_plus : forall v1 v2, eval_binop_values Plus (Vint v1) (Vint v2) (Vint (v1+v2))
| Eval_minus : forall v1 v2, eval_binop_values Minus (Vint v1) (Vint v2) (Vint (v1-v2))
| Eval_mult : forall v1 v2, eval_binop_values Mult (Vint v1) (Vint v2) (Vint (v1*v2))
| Eval_gt : forall v1 v2, eval_binop_values Gt (Vint v1) (Vint v2) (bool_to_val(Z.gtb v1 v2))
| Eval_lt : forall v1 v2, eval_binop_values Lt (Vint v1) (Vint v2) (bool_to_val(Z.ltb v1 v2))
| Eval_geq : forall v1 v2, eval_binop_values Geq (Vint v1) (Vint v2) (bool_to_val(Z.geb v1 v2))
| Eval_leq : forall v1 v2, eval_binop_values Leq (Vint v1) (Vint v2) (bool_to_val(Z.leb v1 v2))
| Eval_eq : forall v1 v2, eval_binop_values Eq (Vint v1) (Vint v2) (bool_to_val(Z.eqb v1 v2)).


(* Evaluating Binary operations *)
Inductive eval_binop: bin_operation -> op -> op -> reg_map -> value -> Prop :=
| Eval_binop:
    forall binop o1 o2 v1 v2 v rm
      (EVALL: eval_op o1 rm v1)
      (EVALR: eval_op o2 rm v2)
      (EVALV: eval_binop_values binop v1 v2 v),
      eval_binop binop o1 o2 rm v.

(* Negation of a value *)
Definition int_neg (i:Z) : Z :=
  match i with
  | 0 => 1
  | _ => 0
  end.

(* Evaluating Unary operations on a value *)
Inductive eval_unop_value: un_operation -> value -> value -> Prop :=
| Eval_uminus: forall v, eval_unop_value UMinus (Vint v) (Vint (-v))
| Eval_neg: forall v, eval_unop_value Neg (Vint v) (Vint (int_neg v))
| Eval_assign: forall v, eval_unop_value Assign v v. 

(* Evaluating Unary operations *)
Inductive eval_unop: un_operation -> op -> reg_map -> value -> Prop :=
| Eval_unop: forall unop o rm v vres
    (EVAL: eval_op o rm v)
    (EVALV: eval_unop_value unop v vres),
    eval_unop unop o rm vres.

(* Evaluating expressions *)
Inductive eval_expr: expr -> reg_map -> value -> Prop :=
| expr_binop:
    forall binop o1 o2 rm v
      (EVAL: eval_binop binop o1 o2 rm v),
      eval_expr (Binexpr binop o1 o2) rm v
| expr_unop:
    forall unop o rm v
      (EVAL: eval_unop unop o rm v),
      eval_expr (Unexpr unop o) rm v.
      
(* Computing the next pc of [Cond op iftrue iffalse] when [op] evaluates to [v] *)
Definition pc_cond (v:value) (iftrue:label) (iffalse:label): label :=
  match v with
  | Vint 0 => iffalse
  | Vint _ => iftrue
  end.

(* Checks if a list of expressions are all true (some Vint != Vint 0) *)
(* Used to verify if the guard of an Assume should pass *)
(* If an evaluation fails,  the list does not evaluate to a boolean *)
Inductive eval_list_expr: list expr -> reg_map -> bool -> Prop :=
| eval_nil:
    forall rm, eval_list_expr nil rm true
| eval_cons_false:
    forall ex le rm
      (EVAL: eval_expr ex rm (Vint 0)),
      eval_list_expr (ex::le) rm false
| eval_cons_true:
    forall ex le rm v res
      (EVALH: eval_expr ex rm (Vint v))
      (TRUE: Zne v 0)                (* v <> 0 *)
      (EVALL: eval_list_expr le rm res),
      eval_list_expr (ex::le) rm res.      

(* evaluates a list of operands (arguments) *)
Inductive eval_list: list expr -> reg_map -> list value -> Prop :=
| eval_list_nil:
    forall rm, eval_list nil rm nil
| eval_list_cons:
    forall le rm lv ex v
      (EVALH: eval_expr ex rm v)
      (EVALL: eval_list le rm lv),
      eval_list (ex::le) rm (v::lv).

(* Initialize the register map when calling a function *)
Fixpoint init_regs (valist:list value) (params:list reg): option reg_map :=
  match params with
  | nil => match valist with
           | nil => Some empty_regmap
           | _ => None          (* too many arguments *)
           end
  | par::params' => match valist with
                    | nil => None (* not enough arguments *)
                    | val::valist' => match (init_regs valist' params') with
                                     | None => None
                                     | Some rm => Some (rm # par <- val)
                                     end
                    end
  end.

(* Updates the reg_map [rm] with the bindings of [ml] *)
(* [rmeval] is the original [rm], used to evaluate the operands of [vm] *)
Inductive update_movelist' : movelist -> reg_map -> reg_map -> reg_map -> Prop :=
| eval_ml_nil: forall rm rmeval,
    update_movelist' nil rmeval rm rm
| eval_ml_cons: forall r e ml v rmeval rm rm'
    (EVAL: eval_expr e rmeval v)
    (UPDATE: update_movelist' ml rmeval rm rm'),
    update_movelist' ((r,e)::ml) rmeval rm (rm' # r <- v).

Definition update_movelist (ml:movelist) (rm:reg_map) (rm':reg_map): Prop :=
  update_movelist' ml rm rm rm'.

(** * Deoptimization Semantics  *)
(* Creates a new Register Mapping given a varmap *)
Inductive update_regmap: varmap -> reg_map -> reg_map -> Prop :=
| update_nil: forall rm,
    update_regmap nil rm empty_regmap (* now we construct from the empty regmap *)
| update_cons: forall r e vm v rm rm'
    (EVAL: eval_expr e rm v)
    (UPDATE: update_regmap vm rm rm'),
    update_regmap ((r,e)::vm) rm (rm' # r <- v).
      

(* [synthesize_frame p rm sl s]: the list [sl] synthesizes the stack [s] under [rm] and [p] *)
Inductive synthesize_frame: program -> reg_map -> list synth_frame -> stack -> Prop :=
| Synth_nil: forall p rm,
    synthesize_frame p rm nil nil
| Synth_cons: forall p s rm sl f l r vm update version
    (UPDATE: update_regmap vm rm update)
    (FINDV: find_base_version f p = Some version)
    (SYNTH: synthesize_frame p rm sl s),
    synthesize_frame p rm (((f,l),r,vm)::sl) ((Stackframe r version l update)::s).

(** * Small-step transition system *)
(* [step p s1 e s2] means that in program [p], state [s1] transitions to [s2] with event [e] *)
(* This is the semantics of lowered programs (no Framestates) *)
Inductive lowered_step: program -> state -> trace -> state -> Prop :=
| exec_Nop:
    forall p s f pc rm ms next oh
      (CODE: (ver_code f)!pc = Some (Nop oh next)),
      lowered_step p (State s f pc rm ms) E0 (State s f next rm ms)
| exec_Op:
    forall p s f pc rm ms expr reg next v
      (CODE: (ver_code f)!pc = Some (Op expr reg next))
      (EVAL: eval_expr expr rm v),
      lowered_step p (State s f pc rm ms) E0 (State s f next (rm # reg <- v) ms)
| exec_Move:
    forall p s f pc rm ms ml next newrm
      (CODE: (ver_code f)!pc = Some (Move ml next))
      (UPDATE: update_movelist ml rm newrm),
      lowered_step p (State s f pc rm ms) E0 (State s f next newrm ms)
| exec_Cond:
    forall p s f pc rm ms expr iftrue iffalse newpc v
      (CODE: (ver_code f)!pc = Some (Cond expr iftrue iffalse))
      (EVAL: eval_expr expr rm v)
      (NEXT: pc_cond v iftrue iffalse = newpc),
      lowered_step p (State s f pc rm ms) E0 (State s f newpc rm ms)
| exec_Call:
    forall p s f pc rm ms fid args retreg next func valist newrm version
      (CODE: (ver_code f)!pc = Some (Call fid args retreg next))
      (FINDF: find_function fid p = Some func)
      (CURRVER: current_version func = version)
      (EVALL: eval_list args rm valist)
      (INIT_REGS: init_regs valist func.(fn_params) = Some newrm),
      lowered_step p (State s f pc rm ms) E0 (State (Stackframe retreg f next rm ::s) version version.(ver_entry) newrm ms)
| exec_Return:
    forall p s fcurr fprev pc next rmcurr rmprev ms retex retval retreg
      (CODE: (ver_code fcurr)!pc = Some (IReturn retex))
      (EVAL: eval_expr retex rmcurr retval),
      lowered_step p (State (Stackframe retreg fprev next rmprev ::s) fcurr pc rmcurr ms) E0
           (State s fprev next (rmprev # retreg <- retval) ms)
| exec_Return_Final:
    forall p f pc rm ms rex retval
      (CODE: (ver_code f)!pc = Some (IReturn rex))
      (EVAL: eval_expr rex rm retval),
      lowered_step p (State nil f pc rm ms) E0 (Final retval ms)
| exec_Printexpr:
    forall p s f pc rm ms expr next printval
      (CODE: (ver_code f)!pc = Some (Printexpr expr next))
      (EVAL: eval_expr expr rm printval),
      lowered_step p (State s f pc rm ms) ((Valprint printval)::E0) (State s f next rm ms)
| exec_Printstring:
    forall p s f pc rm ms str next
      (CODE: (ver_code f)!pc = Some (Printstring str next)),
      lowered_step p (State s f pc rm ms) ((Stringprint str)::E0) (State s f next rm ms)
| exec_Store:
    forall p s f pc rm ms expr1 expr2 next val addr newms
      (CODE: (ver_code f)!pc = Some (Store expr1 expr2 next))
      (EVAL_ST: eval_expr expr1 rm val)
      (EVAL_AD: eval_expr expr2 rm addr)
      (STORE: Store_ ms addr val = Some newms), (* using the Store_ parameter *)
      lowered_step p (State s f pc rm ms) E0 (State s f next rm newms)
| exec_Load:
    forall p s f pc rm ms reg next expr addr val
      (CODE: (ver_code f)!pc = Some (Load expr reg next))
      (EVAL: eval_expr expr rm addr)
      (LOAD: Load_ ms addr = Some val), (* using the Load_ parameter *)
      lowered_step p (State s f pc rm ms) E0 (State s f next (rm # reg <- val) ms)
| exec_Assume_holds:
    forall p s f pc rm ms le tgt vm sl next
      (CODE: (ver_code f)! pc = Some (Assume le tgt vm sl next))
      (ASSUME_TRUE: eval_list_expr le rm true),
      lowered_step p (State s f pc rm ms) E0 (State s f next rm ms)
| exec_Assume_fails:
    forall p s f pc rm ms le fa la vm sl next newver newrm synth
      (CODE: (ver_code f)! pc = Some (Assume le (fa,la) vm sl next))
      (ASSUME_FAILS: (eval_list_expr le rm false)) (* at least one assertion fails *)
      (FINDF: find_base_version fa p = Some newver) (* the version we deoptimize to *)
      (UPDATE: update_regmap vm rm newrm) (* updating the regmap as indicated in the assume *)
      (SYNTH: synthesize_frame p rm sl synth), (* new synthesized stackframes *)
      lowered_step p (State s f pc rm ms) E0 (State (synth++s) newver la newrm ms).

(* Semantics given a lowered program *)
Definition lowered_sem (p:program) : semantics :=
  Semantics_gen lowered_step (initial_state p) (final_state p) p.

(** *  Non-deterministic semantics for speculative code *)
Inductive deopt_conditions : program -> state -> label -> stack -> version -> label -> reg_map -> Prop :=
| deopt_cond:
    forall p s f pc rm ms fa la vm sl next newver newrm synth
      (CODE: (ver_code f)! pc = Some (Framestate (fa,la) vm sl next))
      (FINDF: find_base_version fa p = Some newver) (* the version we deoptimize to *)
      (UPDATE: update_regmap vm rm newrm) (* updating the regmap as indicated in the assume *)
      (SYNTH: synthesize_frame p rm sl synth), (* new synthesized stackframes *)
      deopt_conditions p (State s f pc rm ms) next synth newver la newrm.

(* Non-deterministic semantics for the Framestate *)
Inductive specir_step: program -> state -> trace -> state -> Prop :=
| nd_exec_lowered:
    forall p s t s'
      (STEP: lowered_step p s t s'),
      specir_step p s t s'
| nd_exec_Framestate_go_on:
    forall p s f pc rm ms la next newver newrm synth
      (DEOPT_COND: deopt_conditions p (State s f pc rm ms) next synth newver la newrm),
      specir_step p (State s f pc rm ms) E0 (State s f next rm ms)
| nd_exec_Framestate_deopt:
    forall p s f pc rm ms la next newver newrm synth
      (DEOPT_COND: deopt_conditions p (State s f pc rm ms) next synth newver la newrm),
      specir_step p (State s f pc rm ms) E0 (State (synth++s) newver la newrm ms).

Definition specir_sem (p:program) : semantics :=
  Semantics_gen specir_step (initial_state p) (final_state p) p.

(** *  Loud semantics *)
(* Semantics that explicitly outputs Go_on or Deopt events when going through Framestates *)
(* This make the semantics determinate *)

(* Semantics where the Framestate produce observable events *)
Inductive loud_step: program -> state -> trace -> state -> Prop :=
| loud_exec_lowered:
    forall p s t s'
      (STEP: lowered_step p s t s'),
      loud_step p s t s'
| loud_exec_Framestate_go_on:
    forall p s f pc rm ms la next newver newrm synth
      (DEOPT_COND: deopt_conditions p (State s f pc rm ms) next synth newver la newrm),
      loud_step p (State s f pc rm ms) (Loud_Go_on::nil) (State s f next rm ms)
| loud_exec_Framestate_deopt:
    forall p s f pc rm ms la next newver newrm synth
      (DEOPT_COND: deopt_conditions p (State s f pc rm ms) next synth newver la newrm),
      loud_step p (State s f pc rm ms) (Loud_Deopt::nil) (State (synth++s) newver la newrm ms).

Definition loud_sem (p:program) : semantics :=
  Semantics_gen loud_step (initial_state p) (final_state p) p.


(** * Helper functions  *)
(* Replacing the optimized version of a function *)
Program Definition set_version_function (v:version) (f:function): function :=
  mk_function (fn_params f) (fn_base f) (Some v) _.
Next Obligation.
  apply (base_no_spec f).
Qed.

(* Removes the optimized version *)
Program Definition remove_opt_function (f:function): function :=
  mk_function (fn_params f) (fn_base f) None _.
Next Obligation.
  apply (base_no_spec f).
Qed.

(* Update a fun_list with the new function containing the new version *)
Definition set_version_funlist (fid:fun_id) (v:version) (fl:PTree.t function): PTree.t function :=
  match (fl ! fid) with
  | None => fl
  | Some f => fl # fid <- (set_version_function v f)
  end.

Definition remove_opt_funlist (fid:fun_id) (fl:PTree.t function): PTree.t function :=
  match (fl ! fid) with
  | None => fl
  | Some f => fl # fid <- (remove_opt_function f)
  end.

(* Updates versions in a program. *)
Definition set_version (p:program) (fid:fun_id) (v:version): program :=
  mk_program (prog_main p) (set_version_funlist fid v (prog_funlist p)).

Definition remove_opt (p:program) (fid:fun_id): program :=
  mk_program (prog_main p) (remove_opt_funlist fid (prog_funlist p)).

(* Max positive used in a PTree *)
Fixpoint max_pos' {A:Type} (vl:list (positive * A)): positive :=
  match vl with
  | nil => xH
  | (vid,v)::vl' => Pos.max vid (max_pos' vl')
  end.

Definition max_pos {A:Type} (tree:PTree.t A): positive :=
  max_pos' (PTree.elements tree).

Definition max_label (c:code): label :=
  max_pos c.

(** * Finding fresh labels  *)
(* Finds a label unused in c *)
Definition fresh_label' (c:code) :=
  Pos.succ (max_label c).
(* This simple version is often not good enough *)
(* As the Kildall fixpoint solver is more efficient on programs with sorted labels *)
(* It is often better to insert new instructions at a label that corresponds to its position in the code *)
(* We use this other fresh_label function that tries to insert at a given label *)
(* If it fails (the label is already used), it defaults to fresh_label' *)

(* The number of tries before defaulting to fresh_label' *)
Parameter fuel_fresh: nat.

(* Takes a suggested label *)
Fixpoint fresh_label_fuel (fuel:nat) (sug:label) (c:code): label :=
  match fuel with
  | O => fresh_label' c
  | S fuel' =>
    match (c!sug) with
    | None => sug
    | Some _ => fresh_label_fuel fuel' (Pos.succ sug) c
    end
  end.

Definition fresh_label (sug:label) (c:code): label :=
  fresh_label_fuel fuel_fresh sug c.


(** * Lowered Programs  *)
(* Lowered Programs do not contain the Framestate instruction anymore *)
Inductive is_fs: instruction -> Prop :=
| Is_Fs: forall tgt vm sl next,
    is_fs (Framestate tgt vm sl next).

(* Some lowered code has no Framestate instruction *)
Definition lowered_code (c:code): Prop :=
  forall (pc:label) (i:instruction), c!pc = Some i -> ~ (is_fs i).

Definition lowered_version (v:version): Prop :=
  lowered_code (ver_code v).

Definition lowered_function (f:function): Prop :=
  forall v, fn_opt f = Some v -> lowered_version v.

Definition lowered_program (p:program): Prop :=
  forall fid f, find_function fid p = Some f -> lowered_function f.


(** * Input Programs *)
(* An input program does not have any optimized version *)
Definition input_function (f:function): Prop :=
  (fn_opt f) = None.

Definition input_program (p:program): Prop :=
  forall fid f, find_function fid p = Some f -> input_function f.


