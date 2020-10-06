(* Modified Smallstep library to verify dynamic optimizations *)

Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import events.
Require Import values.
Require Import jit.
Require Import Smallstep.
Require Import specIR.
Require Import ir_properties.
Require Import interpreter_proof.

Set Implicit Arguments.

(** * Reflexivity of our match_states relations  *)
Definition reflexive {index:Type} {state:Type} (match_states: index -> state -> state -> Prop): Prop :=
  forall s, exists i, match_states i s s.

(* new definition that accounts for changes in the way the interpreter state is forged *)
Definition reflexive_forge {index:Type} (p1 p2:program) (match_states: index -> specIR.state -> specIR.state -> Prop): Prop :=
  forall (s:synchro_state) (stack:specIR.stack) r1 s1 ms,
    forge_interpreter_state p1 stack s = OK (r1, s1) ->
    exists r2 s2, forge_interpreter_state p2 stack s = OK (r2, s2) /\ (* forge is preserved *)
             exists (i:index), match_states i (make_state r1 s1 ms) (make_state r2 s2 ms).


(** * Forward Internal Loud Simulations between two transition semantics. *)
(** The general form of a forward internal simulation. *)
Record forward_internal_loud_simulation (p1 p2: program) : Type :=
  Forward_internal_loud_simulation {
    fsim_index: Type;
    fsim_order: fsim_index -> fsim_index -> Prop;
    fsim_order_wf: well_founded fsim_order;
    fsim_match_states :> fsim_index -> specIR.state -> specIR.state -> Prop;
    fsim_match_states_refl: reflexive_forge p1 p2 fsim_match_states;
    fsim_match_final_states:
      forall i s1 s2 r,
      fsim_match_states i s1 s2 -> final_state p1 s1 r -> final_state p2 s2 r;
    fsim_simulation:
      forall s1 t s1', Step (loud_sem p1) s1 t s1' ->
      forall i s2, fsim_match_states i s1 s2 ->
      exists i', exists s2',
         (SPlus (loud_sem p2) s2 t s2' \/ (Star (loud_sem p2) s2 t s2' /\ fsim_order i' i))
      /\ fsim_match_states i' s1' s2';
  }.

(* Implicit Arguments forward_simulation []. *)
Arguments forward_internal_loud_simulation: clear implicits.

(** An alternate form of the simulation diagram *)

Lemma fsim_simulation':
  forall p1 p2 (S: forward_internal_loud_simulation p1 p2),
  forall i s1 t s1', Step (loud_sem p1) s1 t s1' ->
  forall s2, S i s1 s2 ->
  (exists i', exists s2', SPlus (loud_sem p2) s2 t s2' /\ S i' s1' s2')
  \/ (exists i', fsim_order S i' i /\ t = E0 /\ S i' s1' s2).
Proof.
  intros. exploit fsim_simulation; eauto.
  intros [i' [s2' [A B]]]. intuition.
  left; exists i'; exists s2'; auto.
  inv H2.
  right; exists i'; auto.
  left; exists i'; exists s2'; split; auto. econstructor; eauto.
Qed.

(** ** Forward simulation diagrams. *)

(** Various simulation diagrams that imply forward simulation *)
(* TODO *)

(** ** Forward simulation of transition sequences *)
(* not needed *)

(** ** Composing two forward simulations *)
(* We only compose backward simulations now *)


(** * Backward simulations between two transition semantics. *)
(** The general form of a backward internal simulation. *)
(* The one used as an invariant of the JIT execution, on silent semantics *)
Record backward_internal_simulation (p1 p2: program) : Type :=
  Backward_internal_simulation {
    bsim_index: Type;
    bsim_order: bsim_index -> bsim_index -> Prop;
    bsim_order_wf: well_founded bsim_order;
    bsim_order_trans: transitive _ bsim_order;
    bsim_match_states :> bsim_index -> state -> state -> Prop;
    bsim_match_states_refl: reflexive_forge p1 p2 bsim_match_states;
    bsim_match_final_states:
      forall i s1 s2 r,
      bsim_match_states i s1 s2 -> safe (specir_sem p1) s1 -> final_state p2 s2 r ->
      exists s1', Star (specir_sem p1) s1 E0 s1' /\ final_state p1 s1' r;
    bsim_progress:
      forall i s1 s2,
      bsim_match_states i s1 s2 -> safe (specir_sem p1) s1 ->
      (exists r, final_state p2 s2 r) \/
      (exists t, exists s2', Step (specir_sem p2) s2 t s2');
    bsim_simulation:
      forall s2 t s2', Step (specir_sem p2) s2 t s2' ->
      forall i s1, bsim_match_states i s1 s2 -> safe (specir_sem p1) s1 ->
      exists i', exists s1',
         (SPlus (specir_sem p1) s1 t s1' \/ (Star (specir_sem p1) s1 t s1' /\ bsim_order i' i))
      /\ bsim_match_states i' s1' s2';
  }.

(** An alternate form of the simulation diagram *)
Lemma bsim_simulation':
  forall p1 p2 (S: backward_internal_simulation p1 p2),
  forall i s2 t s2', Step (specir_sem p2) s2 t s2' ->
  forall s1, S i s1 s2 -> safe (specir_sem p1) s1 ->
  (exists i', exists s1', SPlus (specir_sem p1) s1 t s1' /\ S i' s1' s2')
  \/ (exists i', bsim_order S i' i /\ t = E0 /\ S i' s1 s2').
Proof.
  intros. exploit bsim_simulation; eauto.
  intros [i' [s1' [A B]]]. intuition.
  left; exists i'; exists s1'; auto.
  inv H3.
  right; exists i'; auto.
  left; exists i'; exists s1'; split; auto. econstructor; eauto.
Qed.

(** ** Backward simulation diagrams. *)

(** ** Backward simulation of transition sequences *)
Section BACKWARD_SIMULATION_SEQUENCES.

Variable p1: program.
Variable p2: program.
Variable S: backward_internal_simulation p1 p2.

Lemma bsim_E0_star:
  forall s2 s2', Star (specir_sem p2) s2 E0 s2' ->
  forall i s1, S i s1 s2 -> safe (specir_sem p1) s1 ->
  exists i', exists s1', Star (specir_sem p1) s1 E0 s1' /\ S i' s1' s2'.
Proof.
  intros s20 s20' STAR0. pattern s20, s20'. eapply star_E0_ind; eauto.
(* base case *)
  intros. exists i; exists s1; split; auto. apply star_refl.
(* inductive case *)
  intros. exploit bsim_simulation; eauto. intros [i' [s1' [A B]]].
  assert (Star (specir_sem p1) s0 E0 s1'). intuition. apply plus_star; auto.
  exploit H0. eauto. eapply star_safe; eauto. intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto. eapply star_trans; eauto.
Qed.

Lemma bsim_safe:
  forall i s1 s2,
  S i s1 s2 -> safe (specir_sem p1) s1 -> safe (specir_sem p2) s2.
Proof.
  intros; red; intros.
  exploit bsim_E0_star; eauto. intros [i' [s1' [A B]]].
  eapply bsim_progress; eauto. eapply star_safe; eauto.
Qed.

Lemma bsim_E0_plus:
  forall s2 t s2', SPlus (specir_sem p2) s2 t s2' -> t = E0 ->
  forall i s1, S i s1 s2 -> safe (specir_sem p1) s1 ->
     (exists i', exists s1', SPlus (specir_sem p1) s1 E0 s1' /\ S i' s1' s2')
  \/ (exists i', clos_trans _ (bsim_order S) i' i /\ S i' s1 s2').
Proof.
  induction 1 using plus_ind2; intros; subst t.
(* base case *)
  exploit bsim_simulation'; eauto. intros [[i' [s1' [A B]]] | [i' [A [B C]]]].
  left; exists i'; exists s1'; auto.
  right; exists i'; intuition.
(* inductive case *)
  exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  exploit bsim_simulation'; eauto. intros [[i' [s1' [A B]]] | [i' [A [B C]]]].
  exploit bsim_E0_star. apply plus_star; eauto. eauto. eapply star_safe; eauto. apply plus_star; auto.
  intros [i'' [s1'' [P Q]]].
  left; exists i''; exists s1''; intuition. eapply plus_star_trans; eauto.
  exploit IHplus; eauto. intros [P | [i'' [P Q]]].
  left; auto.
  right; exists i''; intuition. eapply t_trans; eauto. apply t_step; auto.
Qed.

Lemma star_non_E0_split:
  forall s2 t s2', Star (specir_sem p2) s2 t s2' -> (length t = 1)%nat ->
  exists s2x, exists s2y, Star (specir_sem p2) s2 E0 s2x /\ Step (specir_sem p2) s2x t s2y /\ Star (specir_sem p2) s2y E0 s2'.
Proof.
  induction 1; intros.
  simpl in H; discriminate.
  subst t.
  assert (EITHER: t1 = E0 \/ t2 = E0).
    unfold Eapp in H2; rewrite app_length in H2.
    destruct t1; auto. destruct t2; auto. simpl in H2; omegaContradiction.
  destruct EITHER; subst.
  exploit IHstar; eauto. intros [s2x [s2y [A [B C]]]].
  exists s2x; exists s2y; intuition. eapply star_left; eauto.
  rewrite E0_right. exists s1; exists s2; intuition. apply star_refl.
Qed.

End BACKWARD_SIMULATION_SEQUENCES.

(* Transitive closure is transitive *)
Lemma clos_trans_trans :
  forall (X:Type) R, transitive X (clos_trans X R).
Proof.
  intros X R. unfold transitive. intros x y z H. generalize dependent z.
  induction H; intros.
  - apply t_trans with (y:=y). apply t_step. auto. auto.
  - apply IHclos_trans1. apply IHclos_trans2. auto.
Qed.


(** ** Composing two backward simulations *)

Section COMPOSE_INTERNAL_BACKWARD_SIMULATIONS.

Variable p1: program.
Variable p2: program.
Variable p3: program.
Hypothesis p3_single_events: single_events (specir_sem p3).
Variable S12: backward_internal_simulation p1 p2.
Variable S23: backward_internal_simulation p2 p3.

Let bb_index : Type := (bsim_index S12 * bsim_index S23)%type.

Let bb_order : bb_index -> bb_index -> Prop :=
  lex_ord (clos_trans _ (bsim_order S12)) (bsim_order S23).

Inductive bb_match_states: bb_index -> state -> state -> Prop :=
  | bb_match_later: forall i1 i2 s1 s3 s2x s2y,
      S12 i1 s1 s2x -> Star (specir_sem p2) s2x E0 s2y -> S23 i2 s2y s3 ->
      bb_match_states (i1, i2) s1 s3.

Lemma bb_match_at: forall i1 i2 s1 s3 s2,
  S12 i1 s1 s2 -> S23 i2 s2 s3 ->
  bb_match_states (i1, i2) s1 s3.
Proof.
  intros. econstructor; eauto. apply star_refl.
Qed.


Lemma bb_simulation_base:
  forall s3 t s3', Step (specir_sem p3) s3 t s3' ->
  forall i1 s1 i2 s2, S12 i1 s1 s2 -> S23 i2 s2 s3 -> safe (specir_sem p1) s1 ->
  exists i', exists s1',
    (SPlus (specir_sem p1) s1 t s1' \/ (Star (specir_sem p1) s1 t s1' /\ bb_order i' (i1, i2)))
    /\ bb_match_states i' s1' s3'.
Proof.
  intros.
  exploit (bsim_simulation' S23); eauto. eapply bsim_safe; eauto. 
  intros [ [i2' [s2' [PLUS2 MATCH2]]] | [i2' [ORD2 [EQ MATCH2]]]].
  (* 1 L2 makes one or several transitions *)
  assert (EITHER: t = E0 \/ (length t = 1)%nat).
  exploit p3_single_events; eauto.
    destruct t; auto. destruct t; auto. simpl. intros. omegaContradiction.
  destruct EITHER.
  (* 1.1 these are silent transitions *)
  subst t. exploit bsim_E0_plus; eauto.
  intros [ [i1' [s1' [PLUS1 MATCH1]]] | [i1' [ORD1 MATCH1]]].
  (* 1.1.1 L1 makes one or several transitions *)
  exists (i1', i2'); exists s1'; split. auto. eapply bb_match_at; eauto.
  (* 1.1.2 L1 makes no transitions *)
  exists (i1', i2'); exists s1; split.
  right; split. apply star_refl. left; auto.
  eapply bb_match_at; eauto.
  (* 1.2 non-silent transitions *)
  exploit star_non_E0_split. apply plus_star; eauto. auto.
  intros [s2x [s2y [P [Q R]]]].
  exploit bsim_E0_star. eexact P. eauto. auto. intros [i1' [s1x [X Y]]].
  exploit bsim_simulation'. eexact Q. eauto. eapply star_safe; eauto.
  intros [[i1'' [s1y [U V]]] | [i1'' [U [V W]]]]; try (subst t; discriminate).
  exists (i1'', i2'); exists s1y; split.
  left. eapply star_plus_trans; eauto. eapply bb_match_later; eauto.
  (* 2. L2 makes no transitions *)
  subst. exists (i1, i2'); exists s1; split.
  right; split. apply star_refl. right; auto.
  eapply bb_match_at; eauto.
Qed.

Lemma bb_simulation:
  forall s3 t s3', Step (specir_sem p3) s3 t s3' ->
  forall i s1, bb_match_states i s1 s3 -> safe (specir_sem p1) s1 ->
  exists i', exists s1',
    (SPlus (specir_sem p1) s1 t s1' \/ (Star (specir_sem p1) s1 t s1' /\ bb_order i' i))
    /\ bb_match_states i' s1' s3'.
Proof.
  intros. inv H0.
  exploit star_inv; eauto. intros [[EQ1 EQ2] | PLUS].
  (* 1. match at *)
  subst. eapply bb_simulation_base; eauto.
  (* 2. match later *)
  exploit bsim_E0_plus; eauto.
  intros [[i1' [s1' [A B]]] | [i1' [A B]]].
  (* 2.1 one or several silent transitions *)
  exploit bb_simulation_base. eauto. auto. eexact B. eauto.
    eapply star_safe; eauto. eapply plus_star; eauto.
  intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto.
  left. eapply plus_star_trans; eauto.
  destruct C as [P | [P Q]]. apply plus_star; eauto. eauto.
  traceEq.
  (* 2.2 no silent transition *)
  exploit bb_simulation_base. eauto. auto. eexact B. eauto. auto.
  intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto.
  intuition. right; intuition.
  inv H6. left. eapply t_trans; eauto. left; auto.
Qed.

Lemma compose_backward_simulation: backward_internal_simulation p1 p3.
Proof.
  apply Backward_internal_simulation with (bsim_order := bb_order) (bsim_match_states := bb_match_states).
(* well founded *)
  unfold bb_order. apply wf_lex_ord. apply wf_clos_trans. apply bsim_order_wf. apply bsim_order_wf.
  (* transitivity *)
  { unfold bb_order. apply transitive_lex_ord.
    - apply clos_trans_trans.
    - apply (bsim_order_trans S23). }  
  (* reflexivity *)
  { unfold reflexive_forge. intros s stack r1 s1 ms FORGE1.
    specialize (bsim_match_states_refl S12). intros H. unfold reflexive_forge in H.
    specialize (H s stack r1 s1 ms FORGE1). destruct H as [r2 [s2 [FORGE2 [i2 MATCH1]]]].
    specialize (bsim_match_states_refl S23). intros H. unfold reflexive_forge in H.
    specialize (H s stack r2 s2 ms FORGE2). destruct H as [r3 [s3 [FORGE3 [i3 MATCH2]]]].
    exists r3. exists s3. split; auto. exists (i2, i3). eapply bb_match_at; eauto. }

  (* { unfold reflexive. intros. *)
  (*   assert (reflexive (bsim_match_states S12)) by apply (bsim_match_states_refl S12). *)
  (*   unfold reflexive in H. specialize (H s). destruct H as [i12 MATCH12]. *)
  (*   assert (reflexive (bsim_match_states S23)) by apply (bsim_match_states_refl S23). *)
  (*   unfold reflexive in H. specialize (H s). destruct H as [i23 MATCH23]. *)
  (*   exists (i12, i23). econstructor; eauto. apply star_refl. }   *)
(* match final states *)
  intros i s1 s3 r MS SAFE FIN. inv MS.
  exploit (bsim_match_final_states S23); eauto.
    eapply star_safe; eauto. eapply bsim_safe; eauto.
  intros [s2' [A B]].
  exploit bsim_E0_star. eapply star_trans. eexact H0. eexact A. auto. eauto. auto.
  intros [i1' [s1' [C D]]].
  exploit (bsim_match_final_states S12); eauto. eapply star_safe; eauto.
  intros [s1'' [P Q]].
  exists s1''; split; auto. eapply star_trans; eauto.
(* progress *)
  intros i s1 s3 MS SAFE. inv MS.
  eapply (bsim_progress S23). eauto. eapply star_safe; eauto. eapply bsim_safe; eauto.
(* simulation *)
  exact bb_simulation.
Qed.


End COMPOSE_INTERNAL_BACKWARD_SIMULATIONS.

(** ** Converting a forward simulation to a backward simulation *)

Section LOUD_BACKWARD.

(* First we define loud backward simulations  *)
Record backward_loud_simulation (p1 p2: program) : Type :=
  Backward_loud_simulation {
    bsiml_index: Type;
    bsiml_order: bsiml_index -> bsiml_index -> Prop;
    bsiml_order_wf: well_founded bsiml_order;
    bsiml_order_trans: transitive bsiml_index bsiml_order;
    bsiml_match_states :> bsiml_index -> state -> state -> Prop;
    bsiml_match_states_refl: reflexive_forge p1 p2 bsiml_match_states;
    bsiml_match_final_states:
      forall i s1 s2 r,
      bsiml_match_states i s1 s2 -> safe (loud_sem p1) s1 -> final_state p2 s2 r ->
      exists s1', Star (loud_sem p1) s1 E0 s1' /\ final_state p1 s1' r;
    bsiml_progress:
      forall i s1 s2,
      bsiml_match_states i s1 s2 -> safe (loud_sem p1) s1 ->
      (exists r, final_state p2 s2 r) \/
      (exists t, exists s2', Step (loud_sem p2) s2 t s2');
    bsiml_simulation:
      forall s2 t s2', Step (loud_sem p2) s2 t s2' ->
      forall i s1, bsiml_match_states i s1 s2 -> safe (loud_sem p1) s1 ->
      exists i', exists s1',
         (SPlus (loud_sem p1) s1 t s1' \/ (Star (loud_sem p1) s1 t s1' /\ bsiml_order i' i))
      /\ bsiml_match_states i' s1' s2';
  }.

(** * Loud Semantics Properties  *)
Inductive lowered_event: event -> Prop :=
| lw_debug: forall di, lowered_event (Debug di)
| lw_print: forall v, lowered_event (Valprint v)
| lw_str: forall str, lowered_event (Stringprint str).

Inductive lowered_trace: trace -> Prop :=
| lw_nil: lowered_trace E0
| lw_cons: forall e t, lowered_event e -> lowered_trace t -> lowered_trace (e::t).

Fixpoint erase_loud (t:trace) : trace :=
  match t with
  | nil => nil
  | (e::t') => match e with
             | Debug di => e::(erase_loud t')
             | Valprint v => e::(erase_loud t')
             | Stringprint str => e::(erase_loud t')
             | Loud_Deopt => erase_loud t'
             | Loud_Go_on => erase_loud t'
             end
  end.

Lemma erase_app:
  forall t1 t2,
    erase_loud (t1 ** t2) = (erase_loud t1 ) ** (erase_loud t2).
Proof.
  intros. induction t1; auto.
  simpl. destruct a; simpl; rewrite IHt1; auto.
Qed.

Lemma erase_silent:
  forall t,
    lowered_trace t ->
    erase_loud t = t.
Proof.
  intros. induction t; auto.
  inv H. simpl. specialize (IHt H3). rewrite IHt. destruct a; inv H2; auto.
Qed.

Lemma step_lw:
  forall p s t s',
    lowered_step p s t s' -> lowered_trace t.
Proof.
  intros. inv H; constructor; constructor.
Qed.

Lemma match_lowered:
  forall t1 t2,
    lowered_trace t1 ->
    match_traces t1 t2 ->
    t1 = t2.
Proof.
  intros t1 t2 H H0. inv H0; auto; inv H; inv H2.
Qed.

(** * Loud Semantics determinacy *)
Theorem loud_determinacy:
  forall (p:program), determinate (loud_sem p).
Proof.
  intros. split.
  - intros s t1 s1 t2 s2 H H0.
    inv H; inv H0; try solve [inv DEOPT_COND; inv STEP; rewrite CODE0 in CODE; inv CODE].
    + eapply internal_determinism in STEP; eauto. destruct STEP. subst. split; auto.
      inv STEP0; constructor.
    + split. constructor. intros. inv DEOPT_COND. inv DEOPT_COND0. rewrite CODE0 in CODE.
      inv CODE. auto.
    + split. constructor. intros. inv H.
    + split. constructor. intros. inv H.
    + split. constructor. intros. inv DEOPT_COND. inv DEOPT_COND0.
      rewrite CODE0 in CODE. inv CODE. synth_determ. rewrite FINDF0 in FINDF. inv FINDF. regmap_determ.
  - unfold single_events. intros. inv H; auto. inv STEP; auto.
  - intros s1 s2 H H0. inv H. inv H0. rewrite FINDF0 in FINDF. inv FINDF. auto.
  - intros s r H. inv H. unfold nostep, not. intros. inv H. inv STEP.
  - intros s r1 r2 H H0. inv H. inv H0. auto.
Qed.

(** * Loud Semantics Receptiveness  *)
Theorem loud_receptive:
  forall (p:program), receptive (loud_sem p).
Proof.
  intros p. split.
  - intros s t1 s1 t2 STEP MATCH. inv STEP.
    + exists s1. constructor. apply step_lw in STEP0 as LW. apply match_lowered in MATCH; auto.
      rewrite <- MATCH. auto.
    + inv MATCH.
      * exists (State s0 f next rm ms). eapply loud_exec_Framestate_go_on; eauto.
      * exists (State (synth++s0) newver la newrm ms). eapply loud_exec_Framestate_deopt; eauto.
    + inv MATCH.
      * exists (State (synth++s0) newver la newrm ms). eapply loud_exec_Framestate_deopt; eauto.
      * exists (State s0 f next rm ms). eapply loud_exec_Framestate_go_on; eauto.
  - unfold single_events. intros. inv H; auto. inv STEP; auto.
Qed.

(** * Loud Semantics Simulations *)
Lemma silent_step:
  forall p s s',
    loud_step p s E0 s' -> specir_step p s E0 s'.
Proof.
  intros p s s' H. inv H. constructor. auto.
Qed.

Lemma silent_step':
  forall p s s' t,
    loud_step p s t s' ->
    specir_step p s (erase_loud t) s'.
Proof.
  intros. inv H.
  - apply step_lw in STEP as LW. apply erase_silent in LW. rewrite LW. constructor; auto.
  - simpl. eapply nd_exec_Framestate_go_on. eauto.
  - simpl. eapply nd_exec_Framestate_deopt. eauto.
Qed.

Lemma step_silenced:
  forall p s s' t,
    specir_step p s t s' -> exists t', loud_step p s t' s'.
Proof.
  intros. inv H.
  - exists t. constructor. auto.
  - exists (Loud_Go_on::nil). eapply loud_exec_Framestate_go_on. eauto.
  - exists (Loud_Deopt::nil). eapply loud_exec_Framestate_deopt. eauto.
Qed.  

Lemma silent_star:
  forall p s s',
    Star (loud_sem p) s E0 s' -> Star (specir_sem p) s E0 s'.
Proof.
  intros p s s' H.
  assert (IND: forall t, Star (loud_sem p) s t s' -> t = E0 -> Star (specir_sem p) s t s').
  { intros t STAR. induction STAR; intros.
    - apply star_refl.
    - rewrite H2 in H1. destruct t1. 2: inv H1. destruct t2. 2: inv H1. inv H1.
      specialize (IHSTAR STAR). econstructor; eauto.
      apply silent_step; auto. auto. }
  apply IND; auto.
Qed.

Lemma silent_star':
  forall p s s' t,
    Star (loud_sem p) s t s' -> Star (specir_sem p) s (erase_loud t) s'.
Proof.
  intros p s s' t H. induction H.
  - apply star_refl.
  - apply silent_step' in H. eapply star_step; eauto. rewrite H1. rewrite erase_app. auto.
Qed.

Lemma silent_plus':
  forall p s s' t,
    SPlus (loud_sem p) s t s' -> SPlus (specir_sem p) s (erase_loud t) s'.
Proof.
  intros. inv H. apply silent_step' in H0. apply silent_star' in H1. econstructor; eauto.
  apply erase_app.
Qed.
  
Lemma safe_loud:
  forall p s,
    safe (specir_sem p) s -> safe (loud_sem p) s.
Proof.
  intros p s H. unfold safe in *. 
  intros s' H0. apply silent_star in H0. specialize (H s' H0) as [[r FINAL] | [t [s'' STEP]]].
  - left. exists r. auto.
  - right. apply step_silenced in STEP as [t' STEP]. exists t'. exists s''. auto.
Qed.

(* A loud backward simulation implies an internal backward simulation *)
Theorem bwd_loud:
  forall psrc popt,
    backward_loud_simulation psrc popt ->
    backward_internal_simulation psrc popt.
Proof.
  intros psrc popt LOUD.
  inv LOUD. apply Backward_internal_simulation with (p1:=psrc) (p2:=popt) (bsim_index:=bsiml_index0) (bsim_order:=bsiml_order0) (bsim_match_states:=bsiml_match_states0); auto.
  - intros i s1 s2 r H H0 H1. apply safe_loud in H0.
    specialize (bsiml_match_final_states0 i s1 s2 r H H0 H1).
    destruct bsiml_match_final_states0 as [s1' [STAR FINAL]]. exists s1'. split; auto.
    apply silent_star; auto.
  - intros i s1 s2 H H0. apply safe_loud in H0.
    specialize (bsiml_progress0 i s1 s2 H H0).
    destruct bsiml_progress0 as [[r FINAL]|[t [s2' STEP]]].
    + left. exists r. auto.
    + right. apply silent_step' in STEP. exists (erase_loud t). exists s2'. auto.
  - intros s2 t s2' STEP i s1 MATCH SAFE.
    apply safe_loud in SAFE.
    inv STEP.
    + assert (LSTEP: loud_step popt s2 t s2') by (constructor; auto).
      assert (LW: lowered_trace t). { eapply step_lw; eauto. } apply erase_silent in LW.
      specialize (bsiml_simulation0 s2 t s2' LSTEP i s1 MATCH SAFE) as [i' [s1' [[PLUS | [STAR ORDER]] MATCH']]].
      * exists i'. exists s1'. split; auto. left. apply silent_plus' in PLUS. rewrite LW in PLUS. auto.
      * exists i'. exists s1'. split; auto. right. apply silent_star' in STAR. rewrite LW in STAR. split; auto.
    + assert (LSTEP: loud_step popt (State s f pc rm ms) (Loud_Go_on::nil) (State s f next rm ms)).
      { eapply loud_exec_Framestate_go_on; eauto. }
      specialize (bsiml_simulation0 (State s f pc rm ms) ((Loud_Go_on)::nil) (State s f next rm ms) LSTEP i s1 MATCH SAFE) as [i' [s1' [[PLUS | [STAR ORDER]] MATCH']]].
      * exists i'. exists s1'. split; auto. left. apply silent_plus' in PLUS. simpl in PLUS. auto.
      * exists i'. exists s1'. split; auto. right. apply silent_star' in STAR. simpl in STAR. auto.
    + assert (LSTEP: loud_step popt (State s f pc rm ms) (Loud_Deopt::nil) (State (synth++s) newver la newrm ms)).
      { eapply loud_exec_Framestate_deopt; eauto. }
      specialize (bsiml_simulation0 (State s f pc rm ms) ((Loud_Deopt)::nil) (State (synth++s) newver la newrm ms) LSTEP i s1 MATCH SAFE) as [i' [s1' [[PLUS | [STAR ORDER]] MATCH']]].
      * exists i'. exists s1'. split; auto. left. apply silent_plus' in PLUS. simpl in PLUS. auto.
      * exists i'. exists s1'. split; auto. right. apply silent_star' in STAR. simpl in STAR. auto.
Qed.
End LOUD_BACKWARD.

Section FORWARD_TO_BACKWARD.

Variable p1: program.
Variable p2: program.
Variable FS: forward_internal_loud_simulation p1 p2.
Hypothesis p1_receptive: receptive (loud_sem p1).
Hypothesis p2_determinate: determinate (loud_sem p2).

(** Exploiting forward simulation *)

Inductive f2b_transitions: state -> state -> Prop :=
  | f2b_trans_final: forall s1 s2 s1' r,
      Star (loud_sem p1) s1 E0 s1' ->
      final_state p1 s1' r ->
      final_state p2 s2 r ->
      f2b_transitions s1 s2
  | f2b_trans_step: forall s1 s2 s1' t s1'' s2' i' i'',
      Star (loud_sem p1) s1 E0 s1' ->
      Step (loud_sem p1) s1' t s1'' ->
      SPlus (loud_sem p2) s2 t s2' ->
      FS i' s1' s2 ->
      FS i'' s1'' s2' ->
      f2b_transitions s1 s2.

Lemma f2b_progress:
  forall i s1 s2, FS i s1 s2 -> safe (loud_sem p1) s1 -> f2b_transitions s1 s2.
Proof.
  intros i0; pattern i0. apply well_founded_ind with (R := fsim_order FS).
  apply fsim_order_wf.
  intros i REC s1 s2 MATCH SAFE.
  destruct (SAFE s1) as [[r FINAL] | [t [s1' STEP1]]]. apply star_refl.
  (* final state reached *)
  eapply f2b_trans_final; eauto.
  apply star_refl.
  eapply fsim_match_final_states; eauto.
  (* L1 can make one step *)
  exploit (fsim_simulation FS); eauto. intros [i' [s2' [A MATCH']]].
  assert (B: SPlus (loud_sem p2) s2 t s2' \/ (s2' = s2 /\ t = E0 /\ fsim_order FS i' i)).
    intuition.
    destruct (star_inv H0); intuition.
  clear A. destruct B as [PLUS2 | [EQ1 [EQ2 ORDER]]].
  eapply f2b_trans_step; eauto. apply star_refl.
  subst. exploit REC; eauto. eapply star_safe; eauto. apply star_one; auto.
  intros TRANS; inv TRANS.
  eapply f2b_trans_final; eauto. eapply star_left; eauto.
  eapply f2b_trans_step; eauto. eapply star_left; eauto.
Qed.

Lemma fsim_simulation_not_E0:
  forall s1 t s1', Step (loud_sem p1) s1 t s1' -> t <> E0 ->
  forall i s2, FS i s1 s2 ->
  exists i', exists s2', SPlus (loud_sem p2) s2 t s2' /\ FS i' s1' s2'.
Proof.
  intros. exploit (fsim_simulation FS); eauto. intros [i' [s2' [A B]]].
  exists i'; exists s2'; split; auto.
  destruct A. auto. destruct H2. exploit star_inv; eauto. intros [[EQ1 EQ2] | P]; auto.
  congruence.
Qed.

(** Exploiting determinacy *)

Remark silent_or_not_silent:
  forall t, t = E0 \/ t <> E0.
Proof.
  intros; unfold E0; destruct t; auto; right; congruence.
Qed.

Remark not_silent_length:
  forall t1 t2, (length (t1 ** t2) <= 1)%nat -> t1 = E0 \/ t2 = E0.
Proof.
  unfold Eapp, E0; intros. rewrite app_length in H.
  destruct t1; destruct t2; auto. simpl in H. omegaContradiction.
Qed.

Lemma f2b_determinacy_inv:
  forall s2 t' s2' t'' s2'',
  Step (loud_sem p2) s2 t' s2' -> Step (loud_sem p2) s2 t'' s2'' ->
  (t' = E0 /\ t'' = E0 /\ s2' = s2'')
  \/ (t' <> E0 /\ t'' <> E0 /\ match_traces (* (symbolenv L1) *) t' t'').
Proof.
  intros.
  assert (match_traces (* (symbolenv L2) *) t' t'').
    eapply sd_determ_1; eauto.
  destruct (silent_or_not_silent t').
  subst. inv H1.
  left; intuition. eapply sd_determ_2; eauto.
  destruct (silent_or_not_silent t'').
  subst. inv H1. elim H2; auto.
  right; intuition.
Qed.

Lemma f2b_determinacy_star:
  forall s s1, Star (loud_sem p2) s E0 s1 ->
  forall t s2 s3,
  Step (loud_sem p2) s1 t s2 -> t <> E0 ->
  Star (loud_sem p2) s t s3 ->
  Star (loud_sem p2) s1 t s3.
Proof.
  intros s0 s01 ST0. pattern s0, s01. eapply star_E0_ind; eauto.
  intros. inv H3. congruence.
  exploit f2b_determinacy_inv. eexact H. eexact H4.
  intros [[EQ1 [EQ2 EQ3]] | [NEQ1 [NEQ2 MT]]].
  subst. simpl in *. eauto.
  congruence.
Qed.

(** Orders *)

Inductive f2b_index : Type :=
  | F2BI_before (n: nat)
  | F2BI_after (n: nat).

Inductive f2b_order: f2b_index -> f2b_index -> Prop :=
  | f2b_order_before: forall n n',
      (n' < n)%nat ->
      f2b_order (F2BI_before n') (F2BI_before n)
  | f2b_order_after: forall n n',
      (n' < n)%nat ->
      f2b_order (F2BI_after n') (F2BI_after n)
  | f2b_order_switch: forall n n',
      f2b_order (F2BI_before n') (F2BI_after n).

Lemma wf_f2b_order:
  well_founded f2b_order.
Proof.
  assert (ACC1: forall n, Acc f2b_order (F2BI_before n)).
    intros n0; pattern n0; apply lt_wf_ind; intros.
    constructor; intros. inv H0. auto.
  assert (ACC2: forall n, Acc f2b_order (F2BI_after n)).
    intros n0; pattern n0; apply lt_wf_ind; intros.
    constructor; intros. inv H0. auto. auto.
  red; intros. destruct a; auto.
Qed.

Lemma trans_f2b_order:
  transitive _ f2b_order.
Proof.
  unfold transitive. intros x y z HXY HYZ.
  inv HXY; inv HYZ.
  - constructor. omega.
  - constructor.
  - constructor. omega.
  - constructor.
Qed.

(** Constructing the backward simulation *)

Inductive f2b_match_states: f2b_index -> state -> state -> Prop :=
  | f2b_match_at: forall i s1 s2,
      FS i s1 s2 ->
      f2b_match_states (F2BI_after O) s1 s2
  | f2b_match_before: forall s1 t s1' s2b s2 n s2a i,
      Step (loud_sem p1) s1 t s1' ->  t <> E0 ->
      Star (loud_sem p2) s2b E0 s2 ->
      starN (step (loud_sem p2)) (globalenv (loud_sem p2)) n s2 t s2a ->
      FS i s1 s2b ->
      f2b_match_states (F2BI_before n) s1 s2
  | f2b_match_after: forall n s2 s2a s1 i,
      starN (step (loud_sem p2)) (globalenv (loud_sem p2)) (S n) s2 E0 s2a ->
      FS i s1 s2a ->
      f2b_match_states (F2BI_after (S n)) s1 s2.

Remark f2b_match_after':
  forall n s2 s2a s1 i,
  starN (step (loud_sem p2)) (globalenv (loud_sem p2)) n s2 E0 s2a ->
  FS i s1 s2a ->
  f2b_match_states (F2BI_after n) s1 s2.
Proof.
  intros. inv H.
  econstructor; eauto.
  econstructor; eauto. econstructor; eauto.
Qed.

(** Backward simulation of L2 steps *)

Lemma f2b_simulation_step:
  forall s2 t s2', Step (loud_sem p2) s2 t s2' ->
  forall i s1, f2b_match_states i s1 s2 -> safe (loud_sem p1) s1 ->
  exists i', exists s1',
    (SPlus (loud_sem p1) s1 t s1' \/ (Star (loud_sem p1) s1 t s1' /\ f2b_order i' i))
     /\ f2b_match_states i' s1' s2'.
Proof.
  intros s2 t s2' STEP2 i s1 MATCH SAFE.
  inv MATCH.
(* 1. At matching states *)
  exploit f2b_progress; eauto. intros TRANS; inv TRANS.
  (* 1.1  L1 can reach final state and L2 is at final state: impossible! *)
  exploit (sd_final_nostep p2_determinate); eauto. contradiction.
  (* 1.2  L1 can make 0 or several steps; L2 can make 1 or several matching steps. *)
  inv H2.
  exploit f2b_determinacy_inv. eexact H5. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  (* 1.2.1  L2 makes a silent transition *)
  destruct (silent_or_not_silent t2).
  (* 1.2.1.1  L1 makes a silent transition too: perform transition now and go to "after" state *)
  subst. simpl in *. destruct (star_starN H6) as [n STEPS2].
  exists (F2BI_after n); exists s1''; split.
  left. eapply plus_right; eauto.
  eapply f2b_match_after'; eauto.
  (* 1.2.1.2 L1 makes a non-silent transition: keep it for later and go to "before" state *)
  subst. simpl in *. destruct (star_starN H6) as [n STEPS2].
  exists (F2BI_before n); exists s1'; split.
  right; split. auto. constructor.
  econstructor. eauto. auto. apply star_one; eauto. eauto. eauto.
  (* 1.2.2 L2 makes a non-silent transition, and so does L1 *)
  exploit not_silent_length. eapply (sr_traces p1_receptive); eauto. intros [EQ | EQ].
  congruence.
  subst t2. rewrite E0_right in H1.
  (* Use receptiveness to equate the traces *)
  exploit (sr_receptive p1_receptive); eauto. intros [s1''' STEP1].
  exploit fsim_simulation_not_E0. eexact STEP1. auto. eauto.
  intros [i''' [s2''' [P Q]]]. inv P.
  (* Exploit determinacy *)
  exploit not_silent_length. eapply (sr_traces p1_receptive); eauto. intros [EQ | EQ].
  subst t0. simpl in *. exploit sd_determ_1. eauto. eexact STEP2. eexact H2.
  intros. elim NOT2. inv H8. auto.
  subst t2. rewrite E0_right in *.
  assert (s4 = s2'). eapply sd_determ_2; eauto. subst s4.
  (* Perform transition now and go to "after" state *)
  destruct (star_starN H7) as [n STEPS2]. exists (F2BI_after n); exists s1'''; split.
  left. eapply plus_right; eauto.
  eapply f2b_match_after'; eauto.

(* 2. Before *)
  inv H2. congruence.
  exploit f2b_determinacy_inv. eexact H4. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  (* 2.1 L2 makes a silent transition: remain in "before" state *)
  subst. simpl in *. exists (F2BI_before n0); exists s1; split.
  right; split. apply star_refl. constructor. omega.
  econstructor; eauto. eapply star_right; eauto.
  (* 2.2 L2 make a non-silent transition *)
  exploit not_silent_length. eapply (sr_traces p1_receptive); eauto. intros [EQ | EQ].
  congruence.
  subst. rewrite E0_right in *.
  (* Use receptiveness to equate the traces *)
  exploit (sr_receptive p1_receptive); eauto. intros [s1''' STEP1].
  exploit fsim_simulation_not_E0. eexact STEP1. auto. eauto.
  intros [i''' [s2''' [P Q]]].
  (* Exploit determinacy *)
  exploit f2b_determinacy_star. eauto. eexact STEP2. auto. apply plus_star; eauto.
  intro R. inv R. congruence.
  exploit not_silent_length. eapply (sr_traces p1_receptive); eauto. intros [EQ | EQ].
  subst. simpl in *. exploit sd_determ_1. eauto. eexact STEP2. eexact H2.
  intros. elim NOT2. inv H7; auto.
  subst. rewrite E0_right in *.
  assert (s3 = s2'). eapply sd_determ_2; eauto. subst s3.
  (* Perform transition now and go to "after" state *)
  destruct (star_starN H6) as [n STEPS2]. exists (F2BI_after n); exists s1'''; split.
  left. apply plus_one; auto.
  eapply f2b_match_after'; eauto.

(* 3. After *)
  inv H. exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  exploit f2b_determinacy_inv. eexact H2. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  subst. exists (F2BI_after n); exists s1; split.
  right; split. apply star_refl. constructor; omega.
  eapply f2b_match_after'; eauto.
  congruence.
Qed.

(** The backward simulation *)

Lemma forward_to_backward_simulation: backward_loud_simulation p1 p2.
Proof.
  apply Backward_loud_simulation with (bsiml_order := f2b_order) (bsiml_match_states := f2b_match_states).
  apply wf_f2b_order.
  (* transitivity *)
  apply trans_f2b_order.
  (* reflexivity *)
  { unfold reflexive_forge. intros s stack r1 s1 ms FORGE.
    specialize (fsim_match_states_refl FS). intros H. unfold reflexive_forge in H.
    specialize (H s stack r1 s1 ms FORGE). destruct H as [r2 [s2 [FORGE2 [i MATCH]]]].
    exists r2. exists s2. split; auto. exists (F2BI_after 0). eapply f2b_match_at. eauto. }    
  (* { unfold reflexive. intros. exists (F2BI_after 0).  *)
  (*   assert (reflexive (fsim_match_states FS)) by apply (fsim_match_states_refl). *)
  (*   specialize (H s). destruct H. eapply f2b_match_at. eauto. } *)
(* final states *)
  intros. inv H.
  exploit f2b_progress; eauto. intros TRANS; inv TRANS.
  assert (r0 = r) by (eapply (sd_final_determ p2_determinate); eauto). subst r0.
  exists s1'; auto.
  inv H4. exploit (sd_final_nostep p2_determinate); eauto. contradiction.
  inv H5. congruence. exploit (sd_final_nostep p2_determinate); eauto. contradiction.
  inv H2. exploit (sd_final_nostep p2_determinate); eauto. contradiction.
(* progress *)
  intros. inv H.
  exploit f2b_progress; eauto. intros TRANS; inv TRANS.
  left; exists r; auto.
  inv H3. right; econstructor; econstructor; eauto.
  inv H4. congruence. right; econstructor; econstructor; eauto.
  inv H1. right; econstructor; econstructor; eauto.
(* simulation *)
  exact f2b_simulation_step.
Qed.

End FORWARD_TO_BACKWARD.


(* This theorem allows proving internal simulation using a forward loud simulation *)
(* This is used for passes that do not alter the way framestates behave *)
Theorem fwd_loud:
  forall psrc popt,
    forward_internal_loud_simulation psrc popt ->
    backward_internal_simulation psrc popt.
Proof.
  intros psrc popt FWD. apply bwd_loud.
  apply forward_to_backward_simulation.
  - auto.
  - apply loud_receptive.
  - apply loud_determinacy.
Qed.

(** * Alernate internal backward definition  *)
(* Where the order and match_states relation are made parameters *)
(* This helps writing the external simulation invariant *)

Record backward_internal_simulation' (p1 p2: program)
       (idxt: Type)
       (order: idxt -> idxt -> Prop)
       (match_states: idxt -> specIR.state -> specIR.state -> Prop)
  : Type :=
  Backward_internal_simulation' {
    order_wf: well_founded order;
    order_trans: transitive _ order;  
    match_states_refl: reflexive_forge p1 p2 match_states;
    match_final_states:
      forall i s1 s2 r,
      match_states i s1 s2 -> safe (specir_sem p1) s1 -> final_state p2 s2 r ->
      exists s1', Star (specir_sem p1) s1 E0 s1' /\ final_state p1 s1' r;
    progress:
      forall i s1 s2,
      match_states i s1 s2 -> safe (specir_sem p1) s1 ->
      (exists r, final_state p2 s2 r) \/
      (exists t, exists s2', Step (specir_sem p2) s2 t s2');
    simulation:
      forall s2 t s2', Step (specir_sem p2) s2 t s2' ->
      forall i s1, match_states i s1 s2 -> safe (specir_sem p1) s1 ->
      exists i', exists s1',
         (SPlus (specir_sem p1) s1 t s1' \/ (Star (specir_sem p1) s1 t s1' /\ order i' i))
      /\ match_states i' s1' s2';
  }.

Lemma bsim_simulation'':
  forall p1 p2 idx (ord:idx->idx->Prop) ms (S: backward_internal_simulation' p1 p2 ord ms),
  forall i s2 t s2', Step (specir_sem p2) s2 t s2' ->
  forall s1, ms i s1 s2 -> safe (specir_sem p1) s1 ->
  (exists i', exists s1', SPlus (specir_sem p1) s1 t s1' /\ ms i' s1' s2')
  \/ (exists i', ord i' i /\ t = E0 /\ ms i' s1 s2').
Proof.
  intros. exploit simulation; eauto.
  intros [i' [s1' [A B]]]. intuition.
  left; exists i'; exists s1'; auto.
  inv H3.
  right; exists i'; auto.
  left; exists i'; exists s1'; split; auto. econstructor; eauto.
Qed.


(* Equivalence between the two definition *)
Theorem backward_eq:
  forall p1 p2,
    backward_internal_simulation p1 p2 ->
    exists idxt (order:idxt->idxt->Prop) ms, backward_internal_simulation' p1 p2 order ms.
Proof.
  intros p1 p2 X. exists (bsim_index X). exists (bsim_order X). exists (bsim_match_states X).
  apply Backward_internal_simulation'; destruct X; auto.
Qed.


Theorem eq_backward:
  forall p1 p2,
  forall idxt (order:idxt->idxt->Prop) ms, backward_internal_simulation' p1 p2 order ms ->
                                 backward_internal_simulation p1 p2.
Proof.
  intros p1 p2 idxt order ms H.
  apply Backward_internal_simulation with (bsim_order:=order) (bsim_match_states:=ms);
    destruct H; auto.
Qed.
  
(** * Backward simulation reflexivity  *)
(* This is used at the very beginning of the JIT proof, to show that there is an internal simulation between the initial program and itself *)
Definition refl_type := unit.
Inductive refl_order: unit -> unit -> Prop := .
Inductive refl_match_states: refl_type -> state -> state -> Prop :=
| match_same: forall s, refl_match_states tt s s.

Theorem wf_refl: well_founded refl_order.
Proof.
  unfold well_founded. intros. destruct a. constructor. intros. inv H.
Qed.

Theorem refl_refl: reflexive refl_match_states.
Proof.
  unfold reflexive. intros. exists tt. constructor.
Qed.

Theorem trans_refl: transitive _ refl_order.
Proof.
  unfold transitive. intros. inv H.
Qed.

Lemma backward_refl:
  forall p,
    backward_internal_simulation' p p refl_order refl_match_states.
Proof.
  intros p. apply Backward_internal_simulation'.
  - apply wf_refl.
  - apply trans_refl.
  - unfold reflexive_forge. intros s stack r1 s1 ms H. exists r1. exists s1. split; auto.
    apply refl_refl.
  - intros i s1 s2 r H H0 H1. inv H. exists s2. split. apply star_refl. auto.
  - intros i s1 s2 H H0. inv H. unfold safe in H0. apply H0. apply star_refl.
  - intros s2 t s2' H i s1 H0 H1. inv H0. exists tt. exists s2'. split.
    left. apply plus_one. auto. constructor.
Qed.

(* non-explicit version *)
Lemma backward_internal_reflexivity:
  forall p, backward_internal_simulation p p.
Proof.
  intros p. eapply eq_backward. eapply backward_refl.
Qed.

(** * Exploiting Sequences  *)

(* Exploiting silent stars *)
Lemma bsim_E0_star':
  forall (p1 p2: program) idxt (ord:idxt->idxt->Prop) ms
    (S: backward_internal_simulation' p1 p2 ord ms),
  forall s2 s2', Star (specir_sem p2) s2 E0 s2' ->
  forall i s1, ms i s1 s2 -> safe (specir_sem p1) s1 ->
  exists i', exists s1', Star (specir_sem p1) s1 E0 s1' /\ ms i' s1' s2'.
Proof.
  intros p1 p2 idxt ord ms S.
  intros s20 s20' STAR0. pattern s20, s20'. eapply star_E0_ind; eauto.
(* base case *)
  intros. exists i; exists s1; split; auto. apply star_refl.
(* inductive case *)
  intros. exploit simulation; eauto. intros [i' [s1' [A B]]].
  assert (Star (specir_sem p1) s0 E0 s1'). intuition. apply plus_star; auto.
  exploit H0. eauto. eapply star_safe; eauto. intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto. eapply star_trans; eauto.
Qed.

(* Exploiting silent plus *)
(* We use the transitivity of the order to make this possible *)
(* This shows that on a PLUS we can have a simulation diagram without changing orders *)
Lemma bsim_E0_plus':
  forall (p1 p2:program) idxt (ord:idxt->idxt->Prop) ms
    (S: backward_internal_simulation' p1 p2 ord ms),
  forall s2 t s2', SPlus (specir_sem p2) s2 t s2' -> t = E0 ->
  forall i s1, ms i s1 s2 -> safe (specir_sem p1) s1 ->
     (exists i', exists s1', SPlus (specir_sem p1) s1 E0 s1' /\ ms i' s1' s2')
  \/ (exists i', ord i' i /\ ms i' s1 s2').
Proof.
  intros p1 p2 idxt ord ms S.
  induction 1 using plus_ind2; intros; subst t.
(* base case *)
  exploit bsim_simulation''; eauto. intros [[i' [s1' [A B]]] | [i' [A [B C]]]].
  left; exists i'; exists s1'; auto.
  right; exists i'; intuition.
(* inductive case *)
  exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  exploit bsim_simulation''; eauto.
  intros [[i' [s1' [A B]]] | [i' [A [B C]]]].
  exploit bsim_E0_star'. eauto. apply plus_star; eauto. eauto. 
  eapply star_safe; eauto. apply plus_star; eauto.
  intros [i'' [s1'' [P Q]]].
  left; exists i''; exists s1''; intuition. eapply plus_star_trans; eauto.
  exploit IHplus; eauto. intros [P | [i'' [P Q]]].
  left; auto.
  right; exists i''; intuition. assert (OT: transitive _ ord) by apply (order_trans S).
  unfold transitive in OT. eapply OT; eauto.
Qed.

Lemma star_E0:
  forall p s1 s2,
    Star (specir_sem p) s1 E0 s2 ->
    SPlus (specir_sem p) s1 E0 s2 \/ s1 = s2.
Proof.
  intros. inv H.
  right. auto. left. econstructor; eauto.
Qed.

Lemma exploit_starstep:
  forall (p1 p2:program) idxt (ord:idxt->idxt->Prop) ms
    (S: backward_internal_simulation' p1 p2 ord ms),
  forall s2 t s2' s2'', Star (specir_sem p2) s2 E0 s2' ->
                   Step (specir_sem p2) s2' t s2'' ->
  forall i s1, ms i s1 s2 -> safe (specir_sem p1) s1 ->
          exists i', exists s1', (SPlus (specir_sem p1) s1 t s1' \/ (Star (specir_sem p1) s1 t s1' /\ ord i' i) ) /\
                       ms i' s1' s2''.
Proof.
  intros p1 p2 idxt ord ms S s2 t s2' s2'' STAR STEP i s1 MATCH SAFE.
  apply star_E0 in STAR. destruct STAR as [PLUS | EQ].
  - specialize (bsim_E0_plus' S PLUS eq_refl i MATCH SAFE).
    intros [[i' [s1' [PLUSSRC MATCH']]]|[i' [ORD MATCH']]].
    + assert (SAFE': safe (specir_sem p1) s1').
      { eapply star_safe; eauto. apply plus_star. auto. }
      specialize ((simulation S) s2' t s2'' STEP i' s1' MATCH' SAFE').
      intros [i'' [s1'' [[PLUS' | [STAR ORD]] MATCH'']]].
      * exists i''. exists s1''. split; auto. left. eapply plus_trans; eauto.
      * exists i''. exists s1''. split; auto. left. eapply plus_star_trans; eauto.
    + specialize ((simulation S) s2' t s2'' STEP i' s1 MATCH' SAFE).
      intros [i'' [s1'' [[PLUS' | [STAR ORD']] MATCH'']]].
      * exists i''. exists s1''. split; auto.
      * exists i''. exists s1''. split; auto. right. split; auto.
        assert (TRANS: transitive _ ord) by apply (order_trans S). unfold transitive in TRANS.
        eapply TRANS; eauto.
  - subst.
    specialize ((simulation S) s2' t s2'' STEP i s1 MATCH SAFE).
    intros [i' [s1' [[PLUS | [STAR ORD]] MATCH']]].
    + exists i'. exists s1'. split; auto.
    + exists i'. exists s1'. split; auto.
Qed.

(** * Composing simulations explicitely  *)
Lemma bsim_E0_star'':
  forall p1 p2 i (ord:i->i->Prop) ms
    (SIM: backward_internal_simulation' p1 p2 ord ms),
  forall s2 s2', Star (specir_sem p2) s2 E0 s2' ->
  forall i s1, ms i s1 s2 -> safe (specir_sem p1) s1 ->
  exists i', exists s1', Star (specir_sem p1) s1 E0 s1' /\ ms i' s1' s2'.
Proof.
  intros p1 p2 idx ord ms SIM.
  intros s20 s20' STAR0. pattern s20, s20'. eapply star_E0_ind; eauto.
(* base case *)
  intros. exists i; exists s1; split; auto. apply star_refl.
(* inductive case *)
  intros. exploit simulation; eauto. intros [i' [s1' [A B]]].
  assert (Star (specir_sem p1) s0 E0 s1'). intuition. apply plus_star; auto.
  exploit H0. eauto. eapply star_safe; eauto. intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto. eapply star_trans; eauto.
Qed.

Lemma bsim_E0_plus'':
  forall p1 p2 i (ord:i->i->Prop) ms
    (SIM: backward_internal_simulation' p1 p2 ord ms),
  forall s2 t s2', SPlus (specir_sem p2) s2 t s2' -> t = E0 ->
  forall i s1, ms i s1 s2 -> safe (specir_sem p1) s1 ->
     (exists i', exists s1', SPlus (specir_sem p1) s1 E0 s1' /\ ms i' s1' s2')
  \/ (exists i', clos_trans _ (ord) i' i /\ ms i' s1 s2').
Proof.
  intros p1 p2 idx ord ms SIM.
  induction 1 using plus_ind2; intros; subst t.
(* base case *)
  exploit bsim_simulation''; eauto. intros [[i' [s1' [A B]]] | [i' [A [B C]]]].
  left; exists i'; exists s1'; auto.
  right; exists i'; intuition.
(* inductive case *)
  exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  exploit bsim_simulation''; eauto. intros [[i' [s1' [A B]]] | [i' [A [B C]]]].
  exploit bsim_E0_star''. apply SIM. apply plus_star; eauto. eauto. eapply star_safe; eauto. apply plus_star; auto.
  intros [i'' [s1'' [P Q]]].
  left; exists i''; exists s1''; intuition. eapply plus_star_trans; eauto.
  exploit IHplus; eauto. intros [P | [i'' [P Q]]].
  left; auto.
  right; exists i''; intuition. eapply t_trans; eauto. apply t_step; auto.
Qed.


Section COMPOSE_INTERNAL_BACKWARD_SIMULATIONS_EXPLICIT.

Variable p1: program.
Variable p2: program.
Variable p3: program.
Hypothesis p3_single_events: single_events (specir_sem p3).
Variable i12: Type.
Variable i23: Type.
Variable ord12: i12 -> i12 -> Prop.
Variable ord23: i23 -> i23 -> Prop.
Variable ms12: i12 -> state -> state -> Prop.
Variable ms23: i23 -> state -> state -> Prop.
Variable S12: backward_internal_simulation' p1 p2 ord12 ms12.
Variable S23: backward_internal_simulation' p2 p3 ord23 ms23.


Let bb_index: Type := (i12 * i23)%type.

Let bb_order: bb_index -> bb_index -> Prop :=
  lex_ord (clos_trans _ ord12) (ord23).

Inductive bb_ms: bb_index -> state -> state -> Prop :=
  | bb_later: forall i1 i2 s1 s3 s2x s2y,
      ms12 i1 s1 s2x -> Star (specir_sem p2) s2x E0 s2y -> ms23 i2 s2y s3 ->
      bb_ms (i1, i2) s1 s3.

Lemma bb_match_at':
  forall i1 i2 s1 s2 s3,
  ms12 i1 s1 s2 -> ms23 i2 s2 s3 ->
  bb_ms (i1, i2) s1 s3.
Proof.
  intros. econstructor; eauto. apply star_refl.
Qed.

Lemma bsim_safe':
  forall p1 p2 i (ord:i->i->Prop) ms
    (SIM: backward_internal_simulation' p1 p2 ord ms),
  forall i s1 s2,
  ms i s1 s2 -> safe (specir_sem p1) s1 -> safe (specir_sem p2) s2.
Proof.
  intros; red; intros.
  exploit bsim_E0_star''; eauto. intros [i' [s1' [A B]]].
  eapply progress; eauto. eapply star_safe; eauto.
Qed.


Lemma bb_simulation_base':
  forall s3 t s3', Step (specir_sem p3) s3 t s3' ->
  forall i1 s1 i2 s2, ms12 i1 s1 s2 -> ms23 i2 s2 s3 -> safe (specir_sem p1) s1 ->
  exists i', exists s1',
    (SPlus (specir_sem p1) s1 t s1' \/ (Star (specir_sem p1) s1 t s1' /\ bb_order i' (i1, i2)))
    /\ bb_ms i' s1' s3'.
Proof.
  intros.
  exploit (bsim_simulation'' S23); eauto. eapply bsim_safe'; eauto. 
  intros [ [i2' [s2' [PLUS2 MATCH2]]] | [i2' [ORD2 [EQ MATCH2]]]].
  (* 1 L2 makes one or several transitions *)
  assert (EITHER: t = E0 \/ (length t = 1)%nat).
  exploit p3_single_events; eauto.
    destruct t; auto. destruct t; auto. simpl. intros. omegaContradiction.
  destruct EITHER.
  (* 1.1 these are silent transitions *)
  subst t. exploit bsim_E0_plus''. apply S12. eauto. auto. eauto. auto.
  intros [ [i1' [s1' [PLUS1 MATCH1]]] | [i1' [ORD1 MATCH1]]].
  (* 1.1.1 L1 makes one or several transitions *)
  exists (i1', i2'); exists s1'; split. auto. eapply bb_match_at'; eauto.
  (* 1.1.2 L1 makes no transitions *)
  exists (i1', i2'); exists s1; split.
  right; split. apply star_refl. left; auto.
  eapply bb_match_at'; eauto.
  (* 1.2 non-silent transitions *)
  exploit star_non_E0_split. apply plus_star; eauto. auto.
  intros [s2x [s2y [P [Q R]]]].
  exploit bsim_E0_star''. apply S12. eexact P. eauto. auto. intros [i1' [s1x [X Y]]].
  exploit bsim_simulation''. apply S12. eexact Q. eauto. eapply star_safe; eauto.
  intros [[i1'' [s1y [U V]]] | [i1'' [U [V W]]]]; try (subst t; discriminate).
  exists (i1'', i2'); exists s1y; split.
  left. eapply star_plus_trans; eauto. eapply bb_later; eauto.
  (* 2. L2 makes no transitions *)
  subst. exists (i1, i2'); exists s1; split.
  right; split. apply star_refl. right; auto.
  eapply bb_match_at'; eauto.
Qed.

Lemma bb_simulation':
  forall s3 t s3', Step (specir_sem p3) s3 t s3' ->
  forall i s1, bb_ms i s1 s3 -> safe (specir_sem p1) s1 ->
  exists i', exists s1',
    (SPlus (specir_sem p1) s1 t s1' \/ (Star (specir_sem p1) s1 t s1' /\ bb_order i' i))
    /\ bb_ms i' s1' s3'.
Proof.
  intros. inv H0.
  exploit star_inv; eauto. intros [[EQ1 EQ2] | PLUS].
  (* 1. match at *)
  subst. eapply bb_simulation_base'; eauto.
  (* 2. match later *)
  exploit bsim_E0_plus''. apply S12. eauto. auto. eauto. auto.
  intros [[i1' [s1' [A B]]] | [i1' [A B]]].
  (* 2.1 one or several silent transitions *)
  exploit bb_simulation_base'. apply H.  eexact B. eauto.
    eapply star_safe; eauto. eapply plus_star; eauto.
  intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto.
  left. eapply plus_star_trans; eauto.
  destruct C as [P | [P Q]]. apply plus_star; eauto. eauto.
  traceEq.
  (* 2.2 no silent transition *)
  exploit bb_simulation_base'. apply H.  eexact B. eauto. auto.
  intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto.
  intuition. right; intuition.
  inv H6. left. eapply t_trans; eauto. left; auto.
Qed.


Theorem compose_backward_simulation':
  backward_internal_simulation' p1 p3 (bb_order) (bb_ms).
Proof.
  apply Backward_internal_simulation'. 
(* well founded *)
  unfold bb_order. apply wf_lex_ord. apply wf_clos_trans. apply (order_wf S12). apply (order_wf S23).
  (* transitivity *)
  { unfold bb_order. apply transitive_lex_ord.
    - apply clos_trans_trans.
    - apply (order_trans S23). }  
  (* reflexivity *)
  { unfold reflexive_forge. intros s stack r1 s1 ms FORGE1.
    specialize (match_states_refl S12). intros H. unfold reflexive_forge in H.
    specialize (H s stack r1 s1 ms FORGE1). destruct H as [r2 [s2 [FORGE2 [i2 MATCH1]]]].
    specialize (match_states_refl S23). intros H. unfold reflexive_forge in H.
    specialize (H s stack r2 s2 ms FORGE2). destruct H as [r3 [s3 [FORGE3 [i3 MATCH2]]]].
    exists r3. exists s3. split; auto. exists (i2, i3). eapply bb_match_at'; eauto. }
(* match final states *)
  intros i s1 s3 r MS SAFE FIN. inv MS.
  exploit (match_final_states S23 ); eauto.
    eapply star_safe; eauto. eapply bsim_safe'; eauto. 
  intros [s2' [A B]].
  exploit bsim_E0_star''. apply S12. eapply star_trans. eexact H0. eexact A. auto. eauto. auto.
  intros [i1' [s1' [C D]]].
  exploit (match_final_states S12); eauto. eapply star_safe; eauto.
  intros [s1'' [P Q]].
  exists s1''; split; auto. eapply star_trans; eauto.
(* progress *)
  intros i s1 s3 MS SAFE. inv MS.
  eapply (progress S23). eauto. eapply star_safe; eauto. eapply bsim_safe'; eauto.
  (* simulation *)
  exact bb_simulation'.
Qed.

End COMPOSE_INTERNAL_BACKWARD_SIMULATIONS_EXPLICIT.
