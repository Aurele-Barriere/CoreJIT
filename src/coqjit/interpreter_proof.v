(* Proving that the interpreter corresponds to the inductive small-step semantics *)

Require Export List.
Require Export Coqlib.
Require Export Maps.
Require Export String.
Require Export common.
Require Export specIR.
Require Export jit.
Require Export interpreter.

(* Operands equivalence *)
Theorem eval_op_correct:
  forall op rm v,
    specIR.eval_op op rm v <-> interpreter.eval_op op rm = OK(v).
Proof.
  intros.
  apply conj; intros.
  - destruct op.
    + simpl. inversion H. subst. rewrite GETRM. simpl. reflexivity.
    + simpl. inversion H. reflexivity.
  - destruct op.
    + simpl in H. unfold try_op in H. apply Eval_reg.
      destruct (rm # r); inversion H. reflexivity.
    + simpl in H. inversion H. apply Eval_const.
Qed.

(* Operations equivalence *)
Theorem eval_binop_values_correct:
  forall b v1 v2 r,
    specIR.eval_binop_values b v1 v2 r <-> eval_binop_values b v1 v2 = OK r.
Proof.
  intros. split; intros.
  - inv H; simpl; auto.
  - destruct b; destruct v1; destruct v2; inv H; try constructor.
Qed.

Theorem eval_binop_correct:
  forall binop op1 op2 rm v,
    specIR.eval_binop binop op1 op2 rm v <-> interpreter.eval_binop binop op1 op2 rm = OK(v).
Proof.
  intros; unfold eval_binop.
  apply conj; intros.
  - inversion H; subst;
      rewrite eval_op_correct in EVALL, EVALR; simpl; repeat ok_do;
        unfold eval_binop_values; inv EVALV; try reflexivity.
  - destruct binop; simpl in H; repeat do_ok; 
      econstructor; try erewrite eval_op_correct; eauto; try erewrite eval_binop_values_correct; eauto.
Qed.

Theorem eval_unop_value_correct:
  forall u v r,
    specIR.eval_unop_value u v r <-> eval_unop_value u v = OK r.
Proof.
  intros. split; intros.
  - inv H; simpl; auto.
  - destruct u; destruct v; inv H; simpl; try constructor.
Qed.

Theorem eval_unop_correct:
  forall unop op rm v,
    specIR.eval_unop unop op rm v <-> interpreter.eval_unop unop op rm = OK(v).
Proof.
  intros; unfold eval_unop. apply conj; intros.
  - inversion H; subst;
      rewrite eval_op_correct in EVAL; simpl; ok_do;
        unfold eval_unop_value; inv EVALV; eauto. 
  - destruct unop; simpl in H; do_ok;
      econstructor; try eapply eval_op_correct; eauto; try rewrite eval_unop_value_correct; auto.
Qed.

(* Expressions equivalence *)
Theorem eval_expr_correct:
  forall e rm v,
    specIR.eval_expr e rm v <-> interpreter.eval_expr e rm = OK(v).
Proof.
  intros; unfold eval_expr. split; intros.
  - destruct e. inv H. apply eval_binop_correct. auto.
    inv H. apply eval_unop_correct. auto.
  - destruct e; simpl in H; constructor.
    apply eval_binop_correct. auto.
    apply eval_unop_correct. auto.
Qed.

Theorem eval_list_expr_correct:
  forall le rm bool,
    specIR.eval_list_expr le rm bool <-> interpreter.eval_list_expr le rm = OK(bool).
Proof.
  intros. apply conj; intros.
  - induction le.
    + inv H. auto.
    + inv H. rewrite eval_expr_correct in EVAL. simpl. rewrite EVAL. simpl. auto.
      apply IHle in EVALL. rewrite eval_expr_correct in EVALH.
      simpl. ok_do. destruct v.
      unfold Zne in TRUE. exfalso. apply TRUE. auto. auto. auto.
  - induction le.
    + simpl in H. inv H. apply eval_nil.
    + simpl in H. do_ok. destruct v; inv H1.
      destruct z eqn:HV.
      * inv H0. constructor. apply eval_expr_correct. auto.
      * econstructor. apply eval_expr_correct. eauto.
        unfold Zne. unfold not. intros. inv H. apply IHle. auto.
      * econstructor. apply eval_expr_correct. eauto.
        unfold Zne. unfold not. intros. inv H. apply IHle. auto.
Qed.          

Theorem eval_list_correct:
  forall le rm lv,
    specIR.eval_list le rm lv <-> interpreter.eval_list le rm = OK(lv).
Proof.
  intros. apply conj; intros.
  - generalize dependent lv. induction le; intros.
    + simpl. inv H. auto.
    + simpl. inv H. apply eval_expr_correct in EVALH.
      apply IHle in EVALL. repeat ok_do. auto.
  - generalize dependent lv. induction le; intros.
    + simpl in H. inv H. constructor.
    + inv H. repeat do_ok. constructor. apply eval_expr_correct. auto.
      apply IHle. auto.
Qed.      


Theorem init_regs_correct:
  forall valist params rm,
    specIR.init_regs valist params = Some rm <-> interpreter.init_regs valist params = OK(rm).
Proof.
  intros. apply conj; intros.
  - generalize dependent rm. generalize dependent params. induction valist; intros.
    + simpl. destruct params; inv H. auto.
    + inv H. destruct params. inv H1.
      simpl. destruct (specIR.init_regs valist params) eqn:HIR; inv H1.
      apply IHvalist in HIR. ok_do. auto.
  - generalize dependent rm. generalize dependent params. induction valist; intros.
    + simpl in H. destruct params; inv H. auto.
    + simpl. simpl in H. destruct params. inv H.
      do_ok. apply IHvalist in HDO. rewrite HDO. auto.
Qed.


(* update_regmap equivalence *)
Theorem update_regmap_correct:
  forall vm rm rm',
    specIR.update_regmap vm rm rm' <-> interpreter.update_regmap vm rm = OK(rm').
Proof.
  intros. split; intros.
  - generalize dependent rm. generalize dependent rm'. induction vm; intros.
    + simpl. inv H. auto.
    + simpl. destruct a as [r v].
      inversion H. rewrite eval_expr_correct in EVAL. rewrite EVAL. simpl.
      apply IHvm in UPDATE. rewrite UPDATE. simpl. auto.
  - generalize dependent rm. generalize dependent rm'. induction vm; intros.
    + simpl in H. inv H. constructor.
    + simpl in H. destruct a as [r v]. repeat do_ok.
      apply IHvm in HDO0. constructor. apply eval_expr_correct. auto. auto.
Qed.

(* update_movelist equivalence *)
Theorem update_movelist_correct':
  forall vm rm rmeval rm',
    specIR.update_movelist' vm rm rmeval rm' <-> interpreter.update_movelist' vm rm rmeval = OK(rm').
Proof.
  intros. apply conj; intros.
  - generalize dependent rm. generalize dependent rm'. induction vm; intros.
    + simpl. inv H. auto.
    + simpl. destruct a as [r v].
      inversion H. rewrite eval_expr_correct in EVAL. rewrite EVAL. simpl.
      apply IHvm in UPDATE. rewrite UPDATE. simpl. auto.
  - generalize dependent rm. generalize dependent rm'. induction vm; intros.
    + simpl in H. inv H. constructor.
    + simpl in H. destruct a as [r v]. repeat do_ok.
      apply IHvm in HDO0. constructor. apply eval_expr_correct. auto. auto.
Qed.

Theorem update_movelist_correct:
  forall vm rm rm',
    specIR.update_movelist vm rm rm' <-> interpreter.update_movelist vm rm = OK(rm').
Proof.
  intros. unfold specIR.update_movelist, update_movelist.
  apply update_movelist_correct'.
Qed.

(* synthesize_frame equivalence *)
Theorem synthesize_frame_correct:
  forall p rm sl s,
    specIR.synthesize_frame p rm sl s <-> interpreter.synthesize_frame p rm sl = OK(s).
Proof.
  intros. apply conj; intros.
  - generalize dependent s. induction sl; intros.
    + simpl. inv H. auto.
    + destruct a as [[[fa la] reg] vm]. simpl.
      inv H. apply update_regmap_correct in UPDATE.
      apply IHsl in SYNTH. repeat ok_do. auto.
  - generalize dependent s. induction sl; intros.
    + simpl in H. inv H. constructor.
    + destruct a as [[[fa la] reg] vm]. simpl in H.
      repeat do_ok.
      constructor. apply update_regmap_correct. auto. auto.
      apply IHsl. auto.
Qed.

(* Initialization *)
Theorem initial_state_correct:
  forall p s,
    specIR.initial_state p s <-> interpreter.initial_state p = OK(s).
Proof.
  intros. unfold initial_state. apply conj; intros.
  - inv H. repeat ok_do. rewrite NOARGS. simpl. auto.
  - repeat do_ok. econstructor; eauto. destruct (fn_params f); auto. inv HDO0.
Qed.

(* make a semantic state from an interpreter state, a stack and a memory state *)
Definition make_state (ins:interpreter_state) (s:specIR.stack) (ms:mem_state) : state :=
  match ins with
  | Int_State v pc rm =>
    (State s v pc rm ms)
  | Int_Final retval =>
    (Final retval ms)
  end.           

(** * Progress preservation of the interpreter  *)
(* Two versions. The first one only guarantees that we get a result *)
(* The second version guarantee that this result can be forged into an interpreter state *)

Theorem int_step_progress:
  forall p s v pc rm ms t s',
    lowered_step p (State s v pc rm ms) t s' ->
    exists result, interpreter.int_step p (Int_State v pc rm) ms = OK result.
Proof.
  intros. simpl. inv H; rewrite CODE; simpl; try unfold OK_; eauto.
  - apply eval_expr_correct in EVAL. rewrite EVAL. simpl. eauto.
  - apply update_movelist_correct in UPDATE. rewrite UPDATE. simpl. eauto.
  - apply eval_expr_correct in EVAL. rewrite EVAL. simpl. eauto.
  - apply eval_list_correct in EVALL. rewrite EVALL. rewrite FINDF.
    apply init_regs_correct in INIT_REGS. simpl. rewrite INIT_REGS. simpl. eauto.
  - apply eval_expr_correct in EVAL. rewrite EVAL. simpl. eauto.
  - apply eval_expr_correct in EVAL. rewrite EVAL. simpl. eauto.
  - apply eval_expr_correct in EVAL. rewrite EVAL. simpl. eauto.
  - apply eval_expr_correct in EVAL_ST. rewrite EVAL_ST.
    apply eval_expr_correct in EVAL_AD. rewrite EVAL_AD. simpl. rewrite STORE. simpl. eauto.
  - apply eval_expr_correct in EVAL. rewrite EVAL. simpl. rewrite LOAD. simpl. eauto.
  - apply eval_list_expr_correct in ASSUME_TRUE. rewrite ASSUME_TRUE. simpl. destruct tgt. eauto.
  - apply eval_list_expr_correct in ASSUME_FAILS. rewrite ASSUME_FAILS. simpl.
    apply synthesize_frame_correct in SYNTH. rewrite SYNTH. simpl.
    apply update_regmap_correct in UPDATE. rewrite FINDF. rewrite UPDATE. simpl. eauto.
Qed.

Theorem int_step_progress':
  forall p s v pc rm ms t s',
    Step (specir_sem p) (State s v pc rm ms) t s' ->
    exists result, interpreter.int_step p (Int_State v pc rm) ms = OK result.
Proof.
  intros p s v pc rm ms t s' H. inv H.
  - eapply int_step_progress; eauto.
  - inv DEOPT_COND. unfold int_step; rewrite CODE. simpl.
    simpl in FINDF. rewrite FINDF. apply synthesize_frame_correct in SYNTH. simpl in SYNTH. rewrite SYNTH.
    apply update_regmap_correct in UPDATE. rewrite UPDATE. simpl. unfold OK_. eauto.
  - inv DEOPT_COND. unfold int_step; rewrite CODE. simpl.
    simpl in FINDF. rewrite FINDF. apply synthesize_frame_correct in SYNTH. simpl in SYNTH. rewrite SYNTH.
    apply update_regmap_correct in UPDATE. rewrite UPDATE. simpl. unfold OK_. eauto.
Qed.

Theorem interpreter_loop_progress:
  forall p s v pc rm ms t s' fuel,
    Step (specir_sem p) (State s v pc rm ms) t s' ->
    exists result, interpreter.interpreter_loop fuel p (Int_State v pc rm) ms = OK result.
Proof.
  intros p s v pc rm ms t s' fuel H.
  apply int_step_progress' in H as [result H]. unfold interpreter_loop. rewrite H.
  simpl. destruct result as [[synchro ms']t']. simpl.
  destruct t'; destruct synchro; eauto.
  destruct (interpreter_safe_loop fuel p i ms') as [[synchro2 ms2]t2]. eauto.
Qed.

(** * Correctness of the result  *)
(* When the interpreter returns a result, it can be forged *)
Lemma int_step_correct_result:
  forall p ins synchro newms t stk ms,
    interpreter.int_step p ins ms = OK (synchro, newms, t) ->
    exists ins' stk', forge_interpreter_state p stk synchro = OK (ins',stk').
Proof.
  intros p ins synchro newms t stack ms H. destruct ins. 2: inv H.
  unfold int_step in H.
  destruct ((ver_code v) # l) eqn:CODE. 2: inv H.
  destruct i; simpl in H; inv H; repeat do_ok; try solve[repeat (esplit; eauto)].
  - simpl. rewrite HDO2. simpl. rewrite HDO1. simpl. eauto.
  - destruct stack.
    + simpl. eauto.
    + simpl. destruct s. eauto.
  - destruct d. repeat do_ok. simpl. eauto.
  - destruct d. repeat do_ok. destruct b.
    + inv H0. simpl. eauto.
    + repeat do_ok. simpl. rewrite HDO3. simpl. eauto.
Qed.

Lemma safe_int_step_correct_result:
  forall p ins synchro newms t b stk ms,
    interpreter.safe_int_step p ins ms = (synchro, newms, t, b) ->
    exists ins' stk', forge_interpreter_state p stk synchro = OK (ins',stk').
Proof.
  intros p ins synchro newms t b stack ms H. unfold safe_int_step in H.
  destruct (int_step p ins ms) eqn:INT_STEP.
  - destruct p0. destruct p0.
    apply int_step_correct_result with (stk:=stack) in INT_STEP as [ins' [stack' FORGE]].
    exists ins'. exists stack'. destruct t0; inv H; auto.
  - inv H. simpl. eauto.
Qed.

Lemma safe_int_loop_correct_result:
  forall fuel p ins synchro newms t stk ms,
    interpreter_safe_loop fuel p ins ms = (synchro, newms, t) ->
    exists ins' stk', forge_interpreter_state p stk synchro = OK (ins',stk').
Proof.
  intros fuel. induction fuel; intros.
  - simpl in H. inv H. simpl. eauto.
  - simpl in H. destruct (safe_int_step p ins ms) as [[[synchro' newms'] t']b'] eqn:SAFE_STEP.
    destruct b'; simpl in H.
    + destruct synchro'; inv H; simpl; eauto.
      * apply safe_int_step_correct_result with (stk:=stk) in SAFE_STEP.
        destruct SAFE_STEP as [ins' [stack' FORGE]]. exists ins'. exists stack'. eauto.
      * apply safe_int_step_correct_result with (stk:=stk) in SAFE_STEP.
        destruct SAFE_STEP as [ins' [stack' FORGE]]. exists ins'. exists stack'. eauto.
      * apply safe_int_step_correct_result with (stk:=stk) in SAFE_STEP.
        destruct SAFE_STEP as [ins' [stack' FORGE]]. exists ins'. exists stack'. eauto.
      * destruct (interpreter_safe_loop fuel p i newms') as [[synchro'' newms''] t''] eqn:LOOP.
        inv H1. apply IHfuel with (stk:=stk) in LOOP. destruct LOOP as [ins' [stack' FORGE]].
        exists ins'. exists stack'. auto.
    + inv H. apply safe_int_step_correct_result with (stk:=stk) in SAFE_STEP.
      destruct SAFE_STEP as [ins' [stack' FORGE]]. exists ins'. exists stack'. eauto.
Qed.

Theorem interpreter_loop_correct_result:
  forall fuel p ins synchro newms t stk ms,
    interpreter_loop fuel p ins ms = OK (synchro, newms, t) ->
    exists ins' stk', forge_interpreter_state p stk synchro = OK (ins',stk').
Proof.
  intros fuel p ins synchro newms t stack ms H. unfold interpreter_loop in H.
  destruct (int_step p ins ms) as [[[synchro' newms']t']| ] eqn:INT_STEP; simpl in H.
  2: inv H.
  destruct t'.
  - destruct synchro'; inv H.
    + apply int_step_correct_result with (stk:=stack) in INT_STEP. eauto.
    + apply int_step_correct_result with (stk:=stack) in INT_STEP. eauto.
    + apply int_step_correct_result with (stk:=stack) in INT_STEP. eauto.
    + destruct (interpreter_safe_loop fuel p i newms') as [[synchro'' newms'']t''] eqn:INT_LOOP.
      inv H1. apply safe_int_loop_correct_result with (stk:=stack) in INT_LOOP. eauto.
  - inv H. apply int_step_correct_result with (stk:=stack) in INT_STEP. eauto.
Qed.

(** * Correctness of the new interpreter step (returning synchronization states)  *)
(* The internal step of the interpreter is correct *)
Theorem int_step_correct:
  forall p v pc rm ms stk synchro newms t ins newstack,
    interpreter.int_step p (Int_State v pc rm) ms = OK (synchro, newms, t) ->
    forge_interpreter_state p stk synchro = OK (ins, newstack) ->
    Step (specir_sem p) (State stk v pc rm ms) t (make_state ins newstack newms).
Proof.
  intros p v pc rm ms stack synchro newms t ins newstack STEP FORGE.
  unfold int_step in STEP. repeat do_ok. rename HDO0 into CODE. rename H0 into STEP.
  destruct i; inv STEP; repeat do_ok; try inv FORGE.
  - apply nd_exec_lowered. eapply exec_Nop; eauto.
  - apply nd_exec_lowered. eapply exec_Op; eauto. apply eval_expr_correct; auto.
  - apply nd_exec_lowered. eapply exec_Move; eauto. apply update_movelist_correct; auto.
  - apply nd_exec_lowered. repeat do_ok. eapply exec_Call; eauto. apply eval_list_correct; eauto.
    apply init_regs_correct; eauto.
  - apply nd_exec_lowered. apply eval_expr_correct in HDO. destruct stack; inv H0.
    eapply exec_Return_Final; eauto. destruct s. inv H1. eapply exec_Return; eauto.
  - apply nd_exec_lowered. eapply exec_Cond; eauto. apply eval_expr_correct; auto.
  - apply nd_exec_lowered. eapply exec_Store; eauto. apply eval_expr_correct; auto.
    apply eval_expr_correct; auto.
  - apply nd_exec_lowered. eapply exec_Load; eauto. apply eval_expr_correct; auto.
  - apply nd_exec_lowered. eapply exec_Printexpr; eauto. apply eval_expr_correct; auto.
  - apply nd_exec_lowered. eapply exec_Printstring; eauto.
  - destruct d. repeat do_ok. inv H1. eapply nd_exec_Framestate_go_on. econstructor; eauto.
    apply update_regmap_correct; eauto. apply synthesize_frame_correct; eauto.
  - apply nd_exec_lowered. destruct d. repeat do_ok. destruct b.
    + inv H2. inv H1. eapply exec_Assume_holds; eauto. apply eval_list_expr_correct; auto.
    + repeat do_ok. inv H1. repeat do_ok. eapply exec_Assume_fails; eauto.
      apply eval_list_expr_correct; eauto. apply update_regmap_correct; eauto.
      apply synthesize_frame_correct; auto.
Qed.
      
(** * Correctness of the new interpreter loop  *)
(* This new loop Halts when it sees an error after the first step *)
(* So that it can be proved to preserve progress *)
(* And it stops after seeing an event to respect safety *)

(* Running the interpreter on final states *)
Lemma int_step_final:
  forall retval p ms result, int_step p (Int_Final retval) ms = OK result -> False.
Proof.
  intros. unfold int_step in H. inv H.
Qed.

Lemma safe_int_step_final:
  forall retval p ms, safe_int_step p (Int_Final retval) ms = (Halt (Int_Final retval), ms, E0, false).
Proof.
  intros. unfold safe_int_step. simpl. auto.
Qed.

Lemma safe_int_loop_final:
  forall retval p ms fuel, interpreter_safe_loop fuel p (Int_Final retval) ms = (Halt (Int_Final retval), ms, E0).
Proof.
  intros. unfold interpreter_safe_loop. destruct fuel; auto.
Qed.

(* The safe step to be looped corresponds to a star, with the behavior at the end *)
(* either a single step with a bheavior, or a silent star *)
Theorem safe_int_step_correct:
  forall p v pc rm ms stk synchro newms t ins newstack b,
    interpreter.safe_int_step p (Int_State v pc rm) ms = (synchro, newms, t, b) ->
    forge_interpreter_state p stk synchro = OK (ins, newstack) ->
    Step (specir_sem p) (State stk v pc rm ms) t (make_state ins newstack newms) \/
    (Star (specir_sem p) (State stk v pc rm ms) E0 (make_state ins newstack newms) /\ t=E0 /\ b = false).
Proof.
  intros p v pc rm ms stack synchro newms t ins newstack b SAFE FORGE.
  destruct (int_step p (Int_State v pc rm) ms) as [[[synchro' ms']t' ]|] eqn:INT_STEP.
  - unfold safe_int_step in SAFE. rewrite INT_STEP in SAFE.
    destruct t' eqn:OUTPUT; inv SAFE; eapply int_step_correct in INT_STEP; eauto.
  - unfold safe_int_step in SAFE. rewrite INT_STEP in SAFE. inv SAFE.
    inv FORGE. right. split. apply star_refl. auto.
Qed.

Theorem safe_int_step_correct_true:
  forall p v pc rm ms stk synchro newms t ins newstack,
    interpreter.safe_int_step p (Int_State v pc rm) ms = (synchro, newms, t, true) ->
    forge_interpreter_state p stk synchro = OK (ins, newstack) ->
    Step (specir_sem p) (State stk v pc rm ms) E0 (make_state ins newstack newms) /\ t=E0.
Proof.
  intros p v pc rm ms stack synchro newms t ins newstack SAFE FORGE.
  destruct (int_step p (Int_State v pc rm) ms) as [[[synchro' ms']t' ]|] eqn:INT_STEP.
  - unfold safe_int_step in SAFE. rewrite INT_STEP in SAFE. destruct t'; inv SAFE.
    eapply int_step_correct in INT_STEP; eauto.
  - unfold safe_int_step in SAFE. rewrite INT_STEP in SAFE. inv SAFE.
Qed.    

Theorem safe_int_step_correct_false:
  forall p v pc rm ms stk synchro newms t ins newstack,
    interpreter.safe_int_step p (Int_State v pc rm) ms = (synchro, newms, t, false) ->
    forge_interpreter_state p stk synchro = OK (ins, newstack) ->
    Step (specir_sem p) (State stk v pc rm ms) t (make_state ins newstack newms) \/
    (Star (specir_sem p) (State stk v pc rm ms) E0 (make_state ins newstack newms) /\ t=E0).
Proof.
  intros. eapply safe_int_step_correct in H; eauto. destruct H. left; auto. destruct H. right; auto.
  split; auto. destruct H1; auto.
Qed.

(* The safe loop corresponds to a silent star, and then a step *)
Theorem safe_int_loop_correct:
  forall fuel p v pc rm ms stk synchro newms t ins newstack,
    interpreter_safe_loop fuel p (Int_State v pc rm) ms = (synchro, newms, t) ->
    forge_interpreter_state p stk synchro = OK (ins, newstack) ->
    (Star (specir_sem p) (State stk v pc rm ms) E0 (make_state ins newstack newms) /\ t=E0) \/
    exists s', Star (specir_sem p) (State stk v pc rm ms) E0 s' /\
          Step (specir_sem p) s' t (make_state ins newstack newms).
Proof.
  assert (H: forall fuel p,            (* for any fuel number *)
             forall v pc rm ms synchro newms t, (* for any loop of that number *)
               interpreter_safe_loop fuel p (Int_State v pc rm) ms = (synchro, newms, t) ->
               forall stack ins newstack, (* for any result once forged *)
                 forge_interpreter_state p stack synchro = OK (ins, newstack) ->
                 (Star (specir_sem p) (State stack v pc rm ms) E0 (make_state ins newstack newms) /\ t=E0) \/
                 exists s', Star (specir_sem p) (State stack v pc rm ms) E0 s' /\
                       Step (specir_sem p) s' t (make_state ins newstack newms)).

  { intros fuel p. induction fuel.
    - intros v pc rm ms synchro newms t LOOP stack ins newstack FORGE.
      unfold interpreter_safe_loop in LOOP. inv LOOP. inv FORGE.
      left. split. apply star_refl. auto.

    - intros v pc rm ms synchro newms t LOOP stack ins newstack FORGE.
      unfold interpreter_safe_loop in LOOP.
      destruct (safe_int_step p (Int_State v pc rm)) as [[[synchro1 ms1] t1]b1] eqn:SAFE_STEP. (* 1st step *)
      destruct b1.
      +                         (* b1 is true: the int_step has made a silent step *)
        destruct synchro1.
        * inv LOOP. eapply safe_int_step_correct_true in SAFE_STEP as [STEP NIL]; eauto. subst.
          left. split. apply plus_star. apply plus_one. auto. auto.
        * inv LOOP. eapply safe_int_step_correct_true in SAFE_STEP as [STEP NIL]; eauto. subst.
          left. split. apply plus_star. apply plus_one. auto. auto.
        * inv LOOP. eapply safe_int_step_correct_true in SAFE_STEP as [STEP NIL]; eauto. subst.
          left. split. apply plus_star. apply plus_one. auto. auto.

        * fold interpreter_safe_loop in LOOP.
          destruct (interpreter_safe_loop fuel p i ms1) as [[synchro2 ms2]t2] eqn:LOOP2. (* result loop *)
          inv LOOP. destruct i as [v1 pc1 rm1 | retval]. (* the intermediate interpreter_state *) simpl.
          2: { rewrite safe_int_loop_final in LOOP2. inv LOOP2.
               eapply safe_int_step_correct_true in SAFE_STEP as [STEP NIL]; eauto. subst.
               left. split. eapply plus_star. apply plus_one. auto. auto. }
          specialize (IHfuel v1 pc1 rm1 ms1 synchro newms t2 LOOP2). 
          specialize (IHfuel stack ins newstack FORGE).
          eapply safe_int_step_correct_true with (stk:=stack) in SAFE_STEP; repeat (esplit;eauto).
          destruct SAFE_STEP as [STEP1 H]. subst. simpl in STEP1.
          destruct IHfuel as [[STAR NIL]|[s' [STAR STEP2]]]; subst.
          ** left. split; auto. eapply star_trans; eauto. apply plus_star. apply plus_one. eauto. auto.
          ** right. exists s'. split; auto. eapply star_trans; eauto. apply plus_star. apply plus_one. eauto.
             auto. 

      +                         (* b1 is false: the int_step has seen an error or a non-silent t *)
        inv LOOP. eapply safe_int_step_correct_false in SAFE_STEP; eauto.
        destruct SAFE_STEP as [STEP | [STAR NIL]].
        * right. exists (State stack v pc rm ms). split. apply star_refl. auto.
        * left. split; auto. }

  intros. eapply H; eauto.
Qed.

(* weaker proof *)
(* The safe loop corresponds to a star *)
Theorem safe_int_loop_correct_star:
  forall fuel p v pc rm ms stk synchro newms t ins newstack,
    interpreter_safe_loop fuel p (Int_State v pc rm) ms = (synchro, newms, t) ->
    forge_interpreter_state p stk synchro = OK (ins, newstack) ->
    Star (specir_sem p) (State stk v pc rm ms) t (make_state ins newstack newms).
Proof.
  intros. eapply safe_int_loop_correct in H; eauto.
  destruct H as [[STAR NIL]|[s' [STAR STEP]]].
  - subst. auto.
  - eapply star_trans; eauto. apply plus_star. apply plus_one. eauto. auto.
Qed.

Inductive star0 (p:program): state -> state -> Prop:=
| star0_refl: forall s, (star0 p) s s
| star0_cons: forall s1 s2 s3, Step (specir_sem p) s1 E0 s2 -> (star0 p) s2 s3 -> (star0 p) s1 s3.

Lemma star_star0:               (* for a better induction scheme *)
  forall p s1 s2,
    Star (specir_sem p) s1 E0 s2 <-> (star0 p) s1 s2.
Proof.
  intros. split; intros.
  - eapply star_E0_ind; intros; auto.
    apply star0_refl. eapply star0_cons; eauto. auto.
  - induction H. apply star_refl. eapply star_step; eauto.
Qed.

Lemma star_step_nil_inv:
  forall p s1 s2 s3,
    Step (specir_sem p) s1 E0 s2 ->
    Star (specir_sem p) s2 E0 s3 ->
    exists s', Star (specir_sem p) s1 E0 s' /\ Step (specir_sem p) s' E0 s3.
Proof.
  intros. rewrite star_star0 in H0. generalize dependent s1. induction H0; intros.
  - exists s1. split. apply star_refl. auto.
  - specialize (IHstar0 s1 H). destruct IHstar0 as [s' [STAR STEP]].
    exists s'. split.
    + apply plus_one in H1. apply plus_star in H1. eapply star_trans; eauto.
    + auto.
Qed.

(* On success, the interpreter loop corresponds to a silent star then a step in the semantics *)
Theorem interpreter_loop_correct:
  forall fuel p v pc rm ms stk synchro newms t ins newstack,
    interpreter_loop fuel p (Int_State v pc rm) ms = OK (synchro, newms, t) ->
    forge_interpreter_state p stk synchro = OK (ins, newstack) ->
    exists s', Star (specir_sem p) (State stk v pc rm ms) E0 s' /\
          Step (specir_sem p) s' t (make_state ins newstack newms).
Proof.
  intros. unfold interpreter_loop in H. repeat do_ok.
  destruct p0 as [[synchro1 ms1] t1]. simpl in H2.
  destruct t1; inv H2.
  - destruct synchro1; inv H1.
    + eapply int_step_correct in HDO; eauto. exists (State stk v pc rm ms). split. apply star_refl. auto.
    + eapply int_step_correct in HDO; eauto. exists (State stk v pc rm ms). split. apply star_refl. auto.
    + eapply int_step_correct in HDO; eauto. exists (State stk v pc rm ms). split. apply star_refl. auto.
    + destruct (interpreter_safe_loop fuel p i ms1) as [[synchro2 ms2] t2] eqn:SAFE_LOOP. inv H2.
      destruct i as [v1 pc1 rm1|retval].
      * eapply safe_int_loop_correct in SAFE_LOOP; eauto.
        subst. eapply int_step_correct with (stk:=stk) in HDO. 2: repeat (esplit; eauto).
        destruct SAFE_LOOP as [[STAR NIL]|[s' [STAR STEP]]].
        ** subst. simpl in HDO. eapply star_step_nil_inv in HDO; eauto.
        ** exists s'. split. simpl in HDO. eapply star_trans; eauto. apply plus_star. apply plus_one.
           eauto. auto. auto.
      * rewrite safe_int_loop_final in SAFE_LOOP. inv SAFE_LOOP.
        eapply int_step_correct in HDO; eauto. exists (State stk v pc rm ms). split. apply star_refl. auto.
  - eapply int_step_correct in HDO; eauto. exists (State stk v pc rm ms).
    split. apply star_refl. auto.
Qed.
