(* Proving that any behavior of the JIT matches a behavior of the source program *)

Require Export List.
Require Export Coqlib.
Require Export Maps.
Require Export String.
Require Export common.
Require Export specIR.
Require Export ir_properties.
Require Export interpreter.
Require Export interpreter_proof.
Require Export optimizer_proof.
Require Export jit.
Require Export Behaviors.


(** * Index and order for the external simulation  *)
(* The number of optimizations left *)
Definition optim_index: Type := nat.
Definition optim_order: optim_index -> optim_index -> Prop := lt.

Lemma optim_order_wf: well_founded optim_order.
Proof.
  unfold optim_order. apply lt_wf.
Qed.


(* The decreasing order, during the execution, given by the current backward simulation *)
Record exec_index : Type := mkindex {
  index_type: Type; 
  matchs: index_type -> state -> state -> Prop;
  index: index_type;
  order: index_type -> index_type -> Prop;
  wf: well_founded order;
                              }.

(* Update the exec_index with a new index *)
Definition change_index (e:exec_index) (i:(index_type e)) : exec_index :=
  mkindex (index_type e) (matchs e) i (order e) (wf e).

(* This order decreases only if the order and relation stay the same *)
Inductive exec_order: exec_index -> exec_index -> Prop :=
| exec_ord :
    forall e i,
      (order e) i (index e) ->
      exec_order (change_index e i) e.

Lemma acc_exec_order:
  forall idxt (ord:idxt -> idxt -> Prop) i
    (WF: well_founded ord),
    Acc ord i -> forall ms, Acc exec_order (mkindex idxt ms i ord WF).
Proof.
  induction 1. intros.
  apply Acc_intro. intros. inv H1. simpl in H2.
  apply H0. auto.
Qed.

Lemma exec_order_wf: well_founded exec_order.
Proof.
  unfold well_founded. intros. destruct a.
  apply acc_exec_order. unfold well_founded in wf0. apply wf0. 
Qed.

(* The order that decreases each time the JIT takes a stuttering step *)
Definition jit_index: Type := optim_index * exec_index.

(* Helper functions *)
Definition joptim: jit_index -> optim_index := fst.
Definition jexec: jit_index -> exec_index := snd.
Definition jtype (ji:jit_index) := index_type (jexec ji).
Definition jrel (ji:jit_index) := matchs (jexec ji).
Definition jindex (ji:jit_index) := index (jexec ji).
Definition jorder (ji:jit_index) := order (jexec ji).

(* Update the index, but not the order or relation *)
Definition jupdate (ji:jit_index) (i:jtype ji) : jit_index :=
  (joptim ji, change_index (jexec ji) i).

Lemma optim_update:
  forall ji i,
    joptim ji = joptim (jupdate ji i).
Proof. intros. unfold jupdate. simpl. auto. Qed.
           
Definition jit_order: jit_index -> jit_index -> Prop :=
  lex_ord lt exec_order.

Definition optim_decreases:= lex_ord_left.
Definition exec_decreases:= lex_ord_right.

(* The JIT order that decreases on stuttering steps is well-founded *)
Theorem jit_order_wf: well_founded jit_order.
Proof.
  unfold jit_order. apply wf_lex_ord. apply lt_wf. apply exec_order_wf.
Qed.

Ltac destruct_jit_index :=
  let optim_idx := fresh "optim_idx" in
  let exec_idx := fresh "exec_idx" in
  match goal with
  | [ji: jit_index |- _ ] => destruct ji as [optim_idx exec_idx]
  end.

Ltac destruct_exec_index :=
  let idxt := fresh "index_type" in
  let matchs := fresh "match_states" in
  let idx := fresh "index" in
  let ord := fresh "order" in
  let refl := fresh "REFL" in
  let wf := fresh "WF" in
  match goal with
  | [e: exec_index |- _ ] => destruct e as [idxt matchs idx ord refl wf]
  end.

(** * External match_states  *)
(* Relating semantic states of the original program and jit states *)
Inductive match_states: program -> jit_index -> state -> jit_state -> Prop :=
| jit_match: forall p ji jitp jitps stack synchro int_state newstack src_state ms
               (INTERNAL_SIM: backward_internal_simulation' p jitp (jorder ji) (jrel ji))
               (FORGE: forge_interpreter_state jitp stack synchro = OK (int_state, newstack))
               (INTERNAL_MATCH: (jrel ji) (jindex ji) src_state (make_state int_state newstack ms)),
    match_states p ji
                 src_state
                 (mk_jit_state jitp jitps ms stack synchro (joptim ji))
    
| final_match: forall p ji retval ms jitp jitps,
    match_states p ji
                 (Final retval ms)
                 (mk_jit_state jitp jitps ms nil (S_Return retval) (joptim ji)).

(** * JIT Semantics  *)
(* We define a semantics using CompCert's formalism *)
(* The extracted JIt uses only the functions *)
(* But this simple inductive definition matches the functions *)

(* An inductive definition to match CompCert's formalism *)
Inductive jit_step_prop: unit -> jit_state -> trace -> jit_state -> Prop :=
| Jstep: forall js1 js2 t
           (JIT_STEP: jit_step js1 = OK (js2, t)),
    jit_step_prop tt js1 t js2.

Inductive init_jit_prop: program -> jit_state -> Prop :=
| Jinit: forall p js
           (JIT_INIT: initial_jit_state p = OK js),
    init_jit_prop p js.

Inductive final_jit_prop: jit_state -> value -> Prop :=
| Jfinal: forall js v
            (JIT_FINAL: jit_final_value js = Some v),
    final_jit_prop js v.

(* The jit semantics, to prove a backward simulation on and preserve behavior *)
Definition jit_sem (p:program) : semantics :=
  Semantics_gen jit_step_prop (init_jit_prop p) final_jit_prop tt.


(** * External Backward Simulation  *)
Definition init_exec_index: exec_index :=
  mkindex refl_type refl_match_states tt refl_order (* refl_refl *) wf_refl.
Definition init_jit_index: jit_index :=
  (max_optim, init_exec_index).

(* The backward simulation used to get behavior refinement *)
Theorem jit_simulation:
  forall (p:program),
    backward_simulation (specir_sem p) (jit_sem p).
Proof.
  intros p. eapply Backward_simulation with (bsim_order := jit_order) (bsim_match_states := match_states p).
  - apply jit_order_wf.         (* well-foundness  *)
  - intros s1 H. simpl in H.    (* initial_state exists *)
    destruct (initial_jit_state p) as [j|] eqn:INIT. 2:inv INIT. exists j. constructor. auto.

  - intros s1 s2 INIT1 INIT2. simpl in INIT1. inv INIT2. (* init states match *)
    exists init_jit_index. simpl. exists s1. split; auto. inv JIT_INIT. inv INIT1. eapply jit_match.
    + unfold init_jit_index, init_exec_index, jorder, jexec, jrel. simpl. apply backward_refl.
    + simpl. rewrite FINDF. simpl. destruct (fn_params f); simpl. eauto. inv NOARGS.
    + unfold init_jit_index, init_exec_index, jrel, jindex, make_state. simpl. constructor.

  - intros i s1 s2 r MATCH SAFE FINAL. inv FINAL. inv MATCH. (* final values match *)
    + eapply (match_final_states INTERNAL_SIM) in INTERNAL_MATCH; eauto.
      destruct synchro; destruct stack; inv JIT_FINAL. inv FORGE. simpl. constructor.
      destruct i0; inv H0. inv FORGE. constructor.
      destruct i0; inv H0. inv FORGE. constructor.
    + exists (Final retval ms). split. apply star_refl. inv JIT_FINAL. constructor.
      
  - intros i s1 s2 MATCH SAFE. inv MATCH. (* progress *)
    + apply (progress INTERNAL_SIM) in INTERNAL_MATCH as [[retval FINAL]|[t [s2' STEP]]] ; auto.
      * left. simpl. exists retval. constructor. destruct int_state; inv FINAL. 
        destruct synchro; inv FORGE; try destruct d; repeat do_ok.
        destruct stack; try destruct s; inv H0. auto. constructor.
        
      * right. simpl. destruct (next_status (profiler jitps synchro) (joptim i)) eqn:STATUS.
        ** destruct int_state; simpl in STEP.
           2: { inv STEP. inv STEP0. }
           eapply interpreter_loop_progress with (fuel:=interpreter_fuel) in STEP.
           destruct STEP as [[[synchro' ms']t']STEP]. simpl in STEP.
           set (newps := profiler jitps synchro).
           exists t'. exists (mk_jit_state jitp newps ms' newstack synchro' (joptim i)). constructor.
           unfold jit_step. simpl. rewrite STATUS. rewrite FORGE. simpl. unfold interpreter.
           rewrite STEP. simpl. auto.
        **  set (newps := profiler jitps synchro). set (newp := safe_optimize newps jitp).
           exists E0. exists (mk_jit_state newp newps ms stack synchro (Nat.pred (joptim i))).
           constructor. unfold jit_step. simpl. rewrite STATUS. auto.
    + left. exists retval. constructor. constructor.

  - intros s2 t s2' H i s1 MATCH SAFE. (* backward diagram *)
    inv MATCH.
    + simpl in H. inv H. destruct (next_status (profiler jitps synchro) (joptim i)) eqn:STATUS.

      * unfold jit_step in JIT_STEP. simpl in JIT_STEP. rewrite STATUS in JIT_STEP. (* EXE *)
        repeat do_ok. inv FORGE. rename HDO0 into INTERP. unfold interpreter in INTERP.
        destruct int_state as [v pc rm | retval]; simpl in INTERP.
        2: { unfold interpreter_loop in INTERP. simpl in INTERP. inv INTERP.  }
        destruct p1 as [[synchro1 ms1]t1].
        unfold make_state in INTERNAL_MATCH. 
        { destruct (forge_interpreter_state jitp newstack synchro1) as [[ins nextstack]|] eqn:FORGE_AFTER.
          - eapply interpreter_loop_correct in INTERP; eauto. destruct INTERP as [s' [STAR STEP]].
            specialize (exploit_starstep INTERNAL_SIM).
            intros DIAG. specialize (DIAG (State newstack v pc rm ms) t1 s' (make_state ins nextstack ms1)).
            specialize (DIAG STAR STEP (jindex i) s1 INTERNAL_MATCH SAFE). destruct DIAG as [i' [s1' DIAG]].
            exists (jupdate i i'). exists s1'.
            destruct DIAG as [[PLUS|[STAR' ORD]] MATCH].
            + split. left. simpl. auto. erewrite optim_update. eapply jit_match; eauto.
            + split. right. simpl. split; auto. unfold jorder, jindex in ORD. unfold jupdate. destruct i.
              apply exec_decreases. simpl in ORD. constructor. auto.
              erewrite optim_update. eapply jit_match; eauto.
          - apply interpreter_loop_correct_result with (stk:=newstack) in INTERP as [ins [stack' FORGE]].
            rewrite FORGE_AFTER in FORGE. inv FORGE. }

      * unfold jit_step in JIT_STEP. simpl in JIT_STEP. rewrite STATUS in JIT_STEP. (* OPT *)
        set (newps := profiler jitps synchro). set (newp := safe_optimize newps jitp).
        (* The optimization gives a simulated new program *)
        assert (OPT_CORRECT: exists optidx (optorder:optidx->optidx->Prop) optms,
                   backward_internal_simulation' jitp newp optorder optms).
        { unfold newp. apply backward_eq. eapply safe_optimize_correct. eauto. }
        destruct OPT_CORRECT as [optidx [optorder [optms OPT_SIM]]].
        specialize (match_states_refl OPT_SIM). intros H. unfold reflexive_forge in H.
        specialize (H synchro stack int_state newstack ms FORGE).
        destruct H as [int_state1 [newstack2 [FORGE2 [i2 OPT_MATCH]]]].

        (* Composing the two simulations *)
        eapply compose_backward_simulation' in OPT_SIM as NEW_SIM; eauto.
        2: { apply specir_single_events. } 

        (* Constructing the new index, with a new relation and new order *)
        set (neword:= lex_ord (Relation_Operators.clos_trans (index_type (jexec i)) (jorder i)) optorder).
        set (newms := bb_ms jitp (jrel i) optms).
        assert (NEWWF: well_founded neword) by apply (order_wf NEW_SIM).
        fold neword in NEW_SIM. fold newms in NEW_SIM.
        exists (Nat.pred (joptim i), mkindex (index_type (jexec i) * optidx) newms (jindex i, i2) neword NEWWF).
        exists s1.                   (* no progress during optimization *) split.
        ** right. split. inv JIT_STEP. apply star_refl. destruct i. apply optim_decreases.
           unfold joptim. simpl. apply Nat.lt_pred_l. destruct o. inv STATUS. omega.
        ** inv JIT_STEP. eapply jit_match. apply NEW_SIM. fold newp. apply FORGE2.
           unfold jrel. simpl. unfold jindex. simpl. unfold newms.
           eapply bb_match_at'. unfold jindex in INTERNAL_MATCH. eauto. auto.

    + inv H. unfold jit_step in JIT_STEP. simpl in JIT_STEP.
      destruct (next_status (profiler jitps (S_Return retval)) (joptim i)) eqn:STATUS. (* final jit states can still optimize *)
      inv JIT_STEP. exists (Nat.pred (joptim i), jexec i). exists (Final retval ms). split.
      * right. split. inv JIT_STEP. apply star_refl.  destruct i. apply optim_decreases.
        unfold joptim. simpl. apply Nat.lt_pred_l. destruct o. inv STATUS. omega.
      * inv JIT_STEP. apply final_match. 
Qed.

(** * Behavior preservation  *)
Theorem jit_behavior_improves:
  forall (p:program),
  forall (beh_jit:program_behavior),
    program_behaves (jit_sem p) beh_jit ->
    exists (beh_src:program_behavior),
      program_behaves (specir_sem p) beh_src /\ behavior_improves beh_src beh_jit.
Proof.
  intros p. eapply backward_simulation_behavior_improves; eauto. apply jit_simulation.
Qed.

Corollary jit_same_safe_behavior:
  forall (p:program),
    (forall beh, program_behaves (specir_sem p) beh -> not_wrong beh) ->
    (forall beh, program_behaves (jit_sem p) beh -> program_behaves (specir_sem p) beh).
Proof.
  intros p. apply backward_simulation_same_safe_behavior. apply jit_simulation.
Qed.
