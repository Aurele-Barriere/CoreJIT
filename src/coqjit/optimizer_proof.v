(* Correctness proof of the middle-end JIT dynamic optimizer *)
(* The final proof is an internal backward simulation *)
(* It is obtained via composing the backward simulations of each pass *)

Require Export optimizer.
Require Export framestate_insertion_proof.
Require Export const_prop_proof.
Require Export lowering_proof.
Require Export inlining_proof.
Require Export assume_insertion_proof.
Require Export assume_insertion_delay_proof.
Require Export internal_simulations.

(* Optimizations are "safe" if they return the original program instead of a crash *)
(* Here we exploit the safety to show that we always return a simulated program *)
Lemma safe_backward:
  forall (p:program) (opt:program -> res program)
    (OPT_OK: forall p', opt p = OK p' -> backward_internal_simulation p p'),
    backward_internal_simulation p (safe_res opt p).
Proof.
  intros p opt OPT_OK.
  unfold safe_res. destruct (opt p) eqn:OPT.
  - specialize (OPT_OK p0 eq_refl). auto.
  - apply backward_internal_reflexivity.
Qed.

Lemma safe_constprop:
  forall p fid,
    backward_internal_simulation p (safe_constant_propagation p fid).
Proof.
  intros p fid. unfold safe_constant_propagation. apply safe_backward. intros p' H.
  eapply constprop_correct; eauto.
Qed.

Lemma safe_assume:
  forall p fid le fs_lbl,
    backward_internal_simulation p (safe_insert_assume p fid le fs_lbl).
Proof.
  intros p fid le fs_lbl. unfold safe_insert_assume. apply safe_backward. intros p' H.
  eapply assume_insertion_correct. eauto.
Qed.

Lemma safe_assume_delay:
  forall p fid le fs_lbl,
    backward_internal_simulation p (safe_insert_assume_delay p fid le fs_lbl).
Proof.
  intros p fid le fs_lbl. unfold safe_insert_assume_delay. apply safe_backward. intros p' H.
  eapply assume_delay_correct. eauto.
Qed.

Lemma safe_inline:
  forall p fid call_lbl,
    backward_internal_simulation p (safe_optimize_inline fid call_lbl p).
  intros p fid call_lbl. unfold safe_optimize_inline. apply safe_backward. intros p' H.
  eapply inlining_correct. eauto.
Qed.

Lemma safe_framestate:
  forall p fid lbllist,
    backward_internal_simulation p (safe_insert_framestate p fid lbllist).
Proof.
  intros p fid lbllist. unfold safe_insert_framestate. apply safe_backward. intros p' H.
  eapply framestate_insertion_correct. eauto.
Qed.

Lemma safe_framestate_list:
  forall p fsl,
    backward_internal_simulation p (process_fs_list p fsl).
Proof.
  intros. generalize dependent p. induction fsl; simpl; intros.
  - apply  backward_internal_reflexivity.
  - destruct a. eapply compose_backward_simulation. apply specir_single_events.
    eapply safe_framestate. eapply IHfsl.
Qed.

(* Each optimization pass preserves an internal backward simulation *)
Lemma opt_list_backward:
  forall lopt p,
    backward_internal_simulation p (process_optim_list p lopt).
Proof.
  intros lopt. induction lopt; intros.
  - simpl. apply backward_internal_reflexivity.
  - simpl. destruct a as [fid optw]. destruct optw.
    + eapply compose_backward_simulation. apply specir_single_events.
      eapply safe_assume. eapply IHlopt.
    + eapply compose_backward_simulation. apply specir_single_events.
      eapply safe_assume_delay. eapply IHlopt.
    + eapply compose_backward_simulation. apply specir_single_events.
      eapply safe_constprop. eapply IHlopt.
    + eapply compose_backward_simulation. apply specir_single_events.
      eapply safe_inline. eapply IHlopt.
    + eapply compose_backward_simulation. apply specir_single_events.
      eapply lowering_correct; eauto. eapply IHlopt.
Qed.

(* The entire optimization process returns a simulated program *)
Lemma safe_optimize_correct:
  forall p ps newp,
    safe_optimize ps p = newp ->
    backward_internal_simulation p newp.
Proof.
  intros p ps newp SAFEOPT. unfold safe_optimize in SAFEOPT. rewrite <- SAFEOPT. apply safe_backward.
  intros p' OPT. clear SAFEOPT.
  unfold optimize in OPT. repeat do_ok. inv HDO.
  eapply compose_backward_simulation. apply specir_single_events.
  2: { eapply lowering_correct; eauto. }
  eapply compose_backward_simulation. apply specir_single_events.
  apply safe_framestate_list.
  apply opt_list_backward.
Qed. 
