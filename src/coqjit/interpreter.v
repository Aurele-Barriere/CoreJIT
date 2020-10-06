(* Interpret a program according to the semantics of the ir *)

Require Export List.
Require Export Coqlib.
Require Export Maps.
Require Export String.
Require Export common.
Require Export specIR.

(* Interpreting operands *)
Definition eval_op (o:op) (rm:reg_map): res value :=
  match o with
  | Reg r => try_op (PTree.get r rm) "Unassigned register"
  | Cst n => OK n
  end.


(* Interpreting Binary operations *)
Definition eval_binop_values (bo:bin_operation) (v1:value) (v2:value) : res value :=
  match v1 with
  | Vint vi1 =>
    match v2 with
    | Vint vi2 =>
      match bo with
      | Plus => OK (Vint (vi1 + vi2))
      | Minus => OK (Vint (vi1 - vi2))
      | Mult => OK (Vint (vi1 * vi2))
      | Gt => OK (bool_to_val(Z.gtb vi1 vi2))
      | Lt => OK (bool_to_val(Z.ltb vi1 vi2))
      | Geq => OK (bool_to_val(Z.geb vi1 vi2))
      | Leq => OK (bool_to_val(Z.leb vi1 vi2))
      | Eq => OK (bool_to_val(Z.eqb vi1 vi2))
      end
    end
  end.

Definition eval_binop (bo:bin_operation) (o1:op) (o2:op) (rm:reg_map): res value :=
  do v1 <- eval_op o1 rm;
    do v2 <- eval_op o2 rm;
    eval_binop_values bo v1 v2.

(* Interpreting Unary operations *)
Definition eval_unop_value (u:un_operation) (v:value): res value :=
  match u with
  | UMinus => match v with
             | Vint vi =>  OK (Vint (-vi))
             end
  | Neg => match v with
          | Vint vi => OK (Vint (int_neg vi))
          end
  | Assign => OK v
  end.

Definition eval_unop (u:un_operation) (o:op) (rm:reg_map): res value :=
  do v <- eval_op o rm;
    eval_unop_value u v.

(* Interpreting expressions *)
Definition eval_expr (e:expr) (rm:reg_map): res value :=
  match e with
  | Binexpr binop o1 o2 => eval_binop binop o1 o2 rm
  | Unexpr unop o => eval_unop unop o rm
  end.

(* Checks if a list of expressions are all true (!= 0) *)
Fixpoint eval_list_expr (le:list expr) (rm:reg_map): res bool :=
  match le with
  | nil => OK true
  | ex::le' => do v <- eval_expr ex rm;
                 match v with
                 | Vint 0 => OK false
                 | Vint _ => eval_list_expr le' rm
                 end
  end.

(* In case there is an error in the evaluation of the guard of an Assume, we want to deoptimize *)
Definition safe_eval_list_expr (le:list expr) (rm:reg_map): bool :=
  match eval_list_expr le rm with
  | OK b => b
  | Error _ => false             (* ignore the errors in guard evaluation *)
  end.

(* Interprets a list of expressions (arguments) *)
(* lv is the list of values already evaluated *)
Fixpoint eval_list (le:list expr) (rm:reg_map): res (list value) :=
  match le with
  | nil => OK nil
  | ex::le' => do v <- eval_expr ex rm;
                 do lv <- eval_list le' rm;
                 OK (v::lv)
  end.

(* Initialize the register map when calling a function *)
Fixpoint init_regs (valist:list value) (params:list reg): res reg_map :=
  match valist with
  | nil => match params with
           | nil => OK empty_regmap
           | _ => Error "Not enough arguments"
           end
  | val::valist' => match params with
                   | nil => Error "Too many arguments"
                   | par::params' => do rm' <- init_regs valist' params';
                                       OK (rm' # par <- val)
                    end
  end.

(* Updates the reg_map [rm] with the binding of [ml] *)
(* rmeval is the original regmap, to evaluate all ops *)
Fixpoint update_movelist' (ml:movelist) (rmeval:reg_map) (rm:reg_map) : res reg_map :=
  match ml with
  | nil => OK rm
  | (r,e)::ml' => do v <- eval_expr e rmeval;
                  do rm' <- update_movelist' ml' rmeval rm;
                  OK (rm' # r <- v)
  end.

Definition update_movelist (ml:movelist) (rm:reg_map) : res reg_map :=
  update_movelist' ml rm rm.

(* Creating a new Register Mapping from a Varmap *)
Fixpoint update_regmap (vm:varmap) (rm:reg_map): res reg_map :=
  match vm with
  | nil => OK empty_regmap
  | (r,e)::vm' =>
    do v <- eval_expr e rm;
      do rm' <- update_regmap vm' rm;
      OK (rm' # r <- v)
  end.

(* [synthesize_frame p rm sl]: the stack synthesized by the list [sl] under [rm] and [p] *)
Fixpoint synthesize_frame (p:program) (rm:reg_map) (sl:list synth_frame): res stack :=
  match sl with
  | nil => OK nil
  | ((f,l),r,vm)::sl' =>
    do rmupdate <- update_regmap vm rm;
      do version <- try_op (find_base_version f p) "The version for the new stackframe does not exist";
      do stack <- synthesize_frame p rm sl';
      OK ((Stackframe r version l rmupdate)::stack)
  end.

(* Returning states without any trace *)
Definition OK0 {A:Type} (s:A) := OK (s,E0).

Definition check_nil {X:Type} (l:list X) : res unit :=
  match l with
  | nil => OK tt
  | _ => Error "The main function should not require any arguments"
  end.

(* Compute the initial state of a program *)
Definition initial_state (p:program) : res state :=
  do f <- try_op (find_function (prog_main p) p) "Can't find main function of the program";
    do check <- check_nil (fn_params f);
    do v <- OK (current_version f);
    OK (State nil v (ver_entry v) empty_regmap initial_memory).

(** * Internal interpreter state *)
(* The internal state of the interpreter. Does not need the stack, as it stops upon Call, Return and Deopt *)
Inductive interpreter_state: Type :=
| Int_State: version -> label -> reg_map -> interpreter_state
| Int_Final: value -> interpreter_state.

(** * Synchronization states  *)
(* The output of the interpreter and native calls *)
Inductive synchro_state:=
| S_Call: fun_id -> list value -> option stackframe -> synchro_state
| S_Return: value -> synchro_state
| S_Deopt: deopt_target -> (list stackframe) -> reg_map -> synchro_state
| Halt: interpreter_state -> synchro_state.
(* The stack returned in the Deopt case is the new synthesized stackframes *)
(* Halt allows the interpreter to go back to the JIT even when a synchro points hasn't been reached *)
(* The interpreter synthesizes its own stackframe on a call *)

(* Returning states without any trace, nor stackframe *)
Definition OK_ (sm:(synchro_state * mem_state)) : res (synchro_state * mem_state * trace) :=
  OK (sm,E0).

(** * Internal interpreter step  *)
Definition int_step (p:program) (ins:interpreter_state) (ms:mem_state): res (synchro_state * mem_state * trace) :=
  match ins with
  | Int_State v pc rm =>
    do instr <- try_op ((ver_code v) ! pc) "No code to execute";
      match instr with
      | Nop oh next => OK_ (Halt (Int_State v next rm), ms)

      | Op expr reg next =>
        do val <- eval_expr expr rm;
          OK_ (Halt (Int_State v next (rm # reg <- val)), ms)

      | Move ml next =>
        do newrm <- update_movelist ml rm;
          OK_ (Halt (Int_State v next newrm), ms)

      | Cond ex iftrue iffalse =>
        do val <- eval_expr ex rm;
          do nextlbl <- OK (pc_cond val iftrue iffalse);
          OK_ (Halt (Int_State v nextlbl rm), ms)

      | Printexpr ex next =>
        do printval <- eval_expr ex rm;
          OK (Halt (Int_State v next rm), ms, Valprint printval::E0)

      | Printstring str next =>
        OK (Halt (Int_State v next rm), ms, Stringprint str::E0)

      | Store ex1 ex2 next =>
        do val <- eval_expr ex1 rm;
          do addr <- eval_expr ex2 rm;
          do newms <- try_op (Store_ ms addr val) "Store_ failed";
          OK_ (Halt (Int_State v next rm), newms) 

      | Load ex reg next =>
        do addr <- eval_expr ex rm;
          do val <- try_op (Load_ ms addr) "Load_ failed";
          OK_ (Halt (Int_State v next (rm # reg <- val)), ms)

      | Call fid args retreg next =>
        do valist <- eval_list args rm;
          (* to make sure the result can be forged *)
          do func <- try_op (find_function fid p) "Function doesn't exist"; 
          do newrm <- init_regs valist (fn_params func);
          OK (S_Call fid valist (Some (Stackframe retreg v next rm)), ms, E0)

      | IReturn retex =>
        do retval <- eval_expr retex rm;
          OK_ (S_Return retval, ms)
              
      | Assume g (fa,la) vm sl next =>
        do assertion <- eval_list_expr g rm; 
          match assertion with
          | true => OK_ (Halt (Int_State v next rm), ms)
          | false =>
            do synth <- synthesize_frame p rm sl;
              do newrm <- update_regmap vm rm;
              (* to make sure the result can be forged *)
              do newver <- try_op (find_base_version fa p) "The version to deoptimize to does not exist";
              OK_ (S_Deopt (fa,la) synth newrm, ms)
          end

      | Framestate (fa,la) vm sl next =>
        do findf <- try_op (find_base_version fa p) "No deopt conditions";
        do synth <- synthesize_frame p rm sl;
        do newrm <- update_regmap vm rm;
        OK_ (Halt (Int_State v next rm), ms)
      (* we give Framestate a behavior, just to make progress preservation proof easier *)
      (* Actually, since Framestates are lowered, the interpreter will never see them *)

      | Fail s => Error s        (* Fail should make the interpreter crash *)
            
      end
  | Int_Final retval =>
    Error "Called interpreter on Final"
  end.
  

(** * Interpreter loop  *)

(** Safe interpreter step  *)
(*  version of the interpreter step that returns to the JIT when seeing an error *)
(* The bool tells you if you should keep on interpreting if you still have fuel *)
(* It also returns just after an event is outputed *)
Definition safe_int_step p ins ms : (synchro_state * mem_state * trace * bool) :=
  match (int_step p ins ms) with
  | OK (synchro, newms, t) => match t with
                             | nil => (synchro, newms, t, true)
                             | _ => (synchro, newms, t, false) (* stops after outputs *)
                             end
  | Error _ => (Halt ins, ms, E0, false) (* stops before errors *)
  end.

(* looping the safe_step and halting just before an error if there is one *)
Fixpoint interpreter_safe_loop (fuel: nat) (p:program) (ins:interpreter_state) (ms:mem_state): (synchro_state * mem_state * trace) :=
  match fuel with
  | O => (Halt ins, ms, E0)
  | S fuel' =>
    let '(synchro, newms, t, b) := safe_int_step p ins ms in
    match b with
    | false => (synchro, newms, t) (* the interpreter has encountered an error, time to return to the JIT *)
    | true => 
      match synchro with
      | Halt int_state => let '(synchro', newms', t') := interpreter_safe_loop fuel' p int_state newms in
                         (synchro', newms', t++t')
      | _ => (synchro, newms, t)
      end
    end
  end.

Definition interpreter_loop (fuel: nat) (p:program) (ins:interpreter_state) (ms:mem_state): res (synchro_state * mem_state * trace) :=
  do (synchro, newms, t) <- int_step p ins ms; (* first step may fail *)
    match t with
    | nil => 
      match synchro with
      | Halt int_state =>           (* we may call the safe loop to go a bit further *)
        let '(synchro', newms', t') := interpreter_safe_loop fuel p int_state newms in
        OK (synchro', newms', t ++ t')
      | _ => OK (synchro, newms, t) (* we reached a synchronization point *)
      end
    | _ => OK (synchro, newms, t) (* we outputed something in the very first step *)
    end.
