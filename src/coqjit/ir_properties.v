(* Properties of the SpecIR language *)

Require Export common.
Require Export values.
Require Export specIR.
Require Import Coq.MSets.MSetPositive.
Require Export def_regs.

(** * Internal Determinism of Lowered Steps *)

Theorem eval_op_determ:
  forall o rm v1 v2,
    eval_op o rm v1 ->
    eval_op o rm v2 ->
    v1 = v2.
Proof.
  intros o rm v1 v2 H H0.
  inversion H; inversion H0; subst.
  inv H4. auto.
  inv H4. inv H4.
  inv H4. rewrite GETRM0 in GETRM. inv GETRM. auto.
Qed.

Ltac op_determ:=
  match goal with
  | [H: eval_op ?o ?rm ?r1,
     H1: eval_op ?o ?rm ?r2 |- _ ] =>
    apply eval_op_determ with (v1:=r2) in H; subst; auto
  end.

Theorem eval_binop_values_determ:
  forall b v1 v2 r1 r2,
    eval_binop_values b v1 v2 r1 ->
    eval_binop_values b v1 v2 r2 ->
    r1 = r2.
Proof.
  intros. inversion H; inversion H0;subst; auto; inv H5; inv H6; inv H7; auto.
Qed.

Ltac binop_values_determ:=
  match goal with
  | [H: eval_binop_values ?b ?v1 ?v2 ?res1,
     H1: eval_binop_values ?b ?v1 ?v2 ?res2 |- _ ] =>
    apply eval_binop_values_determ with (r1:=res2) in H; subst; auto
  end.

Theorem eval_unop_value_determ:
  forall u v r1 r2,
    eval_unop_value u v r1 ->
    eval_unop_value u v r2 ->
    r1 = r2.
Proof.
  intros. inversion H; inversion H0; subst; auto; inv H4; inv H5; auto.
Qed.

Ltac unop_value_determ:=
  match goal with
  | [H: eval_unop_value ?u ?v ?res1,
     H1: eval_unop_value ?u ?v ?res2 |- _ ] =>
    apply eval_unop_value_determ with (r1:=res2) in H; subst; auto
  end.

Theorem eval_binop_determ:
  forall b o1 o2 v1 v2 rm,
    eval_binop b o1 o2 rm v1 ->
    eval_binop b o1 o2 rm v2 ->
    v1 = v2.
Proof.
  intros. inversion H; inversion H0. subst.
  op_determ. op_determ. binop_values_determ.
Qed.

Ltac binop_determ:=
  match goal with
  | [H: eval_binop ?b ?o1 ?o2 ?rm ?res1,
     H1: eval_binop ?b ?o1 ?o2 ?rm ?res2 |- _ ] =>
    apply eval_binop_determ with (v1:=res2) in H; subst; auto
  end.

Theorem eval_unop_determ:
  forall u o v1 v2 rm,
    eval_unop u o rm v1 ->
    eval_unop u o rm v2 ->
    v1 = v2.
Proof.
  intros. inversion H; inversion H0; subst.
  op_determ. unop_value_determ.
Qed.

Ltac unop_determ:=
  match goal with
  | [H: eval_unop ?u ?o ?rm ?res1,
     H1: eval_unop ?u ?o ?rm ?res2 |- _ ] =>
    apply eval_unop_determ with (v1:=res2) in H; subst; auto
  end.

Theorem eval_expr_determ:
  forall expr v1 v2 rm,
    eval_expr expr rm v1 ->
    eval_expr expr rm v2 ->
    v1 = v2.
Proof.
  intros. inversion H; inversion H0; try (inv H5); try (inv H6); try (inv H4).
  binop_determ. repeat unop_determ.
Qed.

Ltac expr_determ:=
  match goal with
  | [H: eval_expr ?e ?rm ?res1,
     H1: eval_expr ?e ?rm ?res2 |- _ ] =>
    apply eval_expr_determ with (v1:=res2) in H; subst; auto
  end.

Theorem eval_list_determ:
  forall l rm v1 v2,
    eval_list l rm v1 ->
    eval_list l rm v2 ->
    v1 = v2.
Proof.
  intros. generalize dependent v1. generalize dependent v2. induction l; intros.
  - inv H. inv H0. auto.
  - inversion H. inversion H0. subst.
    expr_determ.
    assert (lv=lv0). eapply IHl; eauto. subst. auto.
Qed.

Ltac list_determ:=
  match goal with
  | [H: eval_list ?l ?rm ?res1,
     H1: eval_list ?l ?rm ?res2 |- _ ] =>
    apply eval_list_determ with (v1:=res2) in H; subst; auto
  end.

Theorem eval_list_expr_determ:
  forall l rm v1 v2,
    eval_list_expr l rm v1 ->
    eval_list_expr l rm v2 ->
    v1 = v2.
Proof.
  intros. generalize dependent v1. generalize dependent v2. induction l; intros.
  - inv H. inv H0. auto.
  - inv H; inv H0; subst; auto.
    + expr_determ. inv EVAL. omega.
    + expr_determ. inv EVALH. omega.
Qed.

Ltac list_expr_determ:=
  match goal with
  | [H: eval_list_expr ?l ?rm ?res1,
     H1: eval_list_expr ?l ?rm ?res2 |- _ ] =>
    apply eval_list_expr_determ with (v1:=res2) in H; subst; auto
  end.

Theorem update_regmap_determ:
  forall vm rm rm1 rm2,
    update_regmap vm rm rm1 ->
    update_regmap vm rm rm2 ->
    rm1 = rm2.
Proof.
  intros. generalize dependent rm1. generalize dependent rm2.
  induction (vm); intros.
  - inv H. inv H0. auto.
  - inv H; inv H0. expr_determ.
    assert (rm'=rm'0). apply IHv; auto. subst. auto.
Qed.

Ltac regmap_determ:=
  match goal with
  | [H: update_regmap ?vm ?rm ?res1,
     H1: update_regmap ?vm ?rm ?res2 |- _ ] =>
    apply update_regmap_determ with (rm1:=res2) in H; subst; auto
  end.

Theorem update_movelist_determ:
  forall ml rm rm1 rm2,
    update_movelist ml rm rm1 ->
    update_movelist ml rm rm2 ->
    rm1 = rm2.
Proof.
  intros. generalize dependent rm1. generalize dependent rm2.
  unfold update_movelist.
  induction (ml); intros.
  - inv H. inv H0. auto.
  - inv H; inv H0. expr_determ.
    assert (rm'=rm'0). apply IHm; auto. subst. auto.
Qed.  

Ltac movelist_determ:=
  match goal with
  | [H: update_movelist ?vm ?rm ?res1,
     H1: update_movelist ?vm ?rm ?res2 |- _ ] =>
    apply update_movelist_determ with (rm1:=res2) in H; subst; auto
  end.

Theorem synthesize_frame_determ:
  forall p rm l s1 s2,
    synthesize_frame p rm l s1 ->
    synthesize_frame p rm l s2 ->
    s1 = s2.
Proof.
  intros. generalize dependent s1. generalize dependent s2. induction l; intros.
  - inv H. inv H0. auto.
  - inv H; inv H0; subst; auto.
    assert (s=s0). apply IHl; auto. subst.
    regmap_determ. match_some. auto.
Qed.

Ltac synth_determ:=
  match goal with
  | [H: synthesize_frame ?p ?rm ?l ?res1,
     H1: synthesize_frame ?p ?rm ?l ?res2 |- _ ] =>
    apply synthesize_frame_determ with (s1:=res2) in H; subst; auto
  end.

Ltac store_determ:=
  match goal with
  | [H1: Store_ ?ms ?ptr ?val = Some ?newms,
     H2: Store_ ?ms ?ptr ?val = Some ?newms' |- _ ] =>
    rewrite H2 in H1; inv H1
  end.

Ltac load_determ:=
  match goal with
  | [H1: Load_ ?ms ?ptr = Some ?val,
     H2: Load_ ?ms ?ptr = Some ?val' |- _ ] =>
    rewrite H2 in H1; inv H1
  end.


Theorem internal_determinism:
  forall p s s1 s2 t1 t2,
    lowered_step p s t1 s1 ->
    lowered_step p s t2 s2 ->
    s1 = s2 /\ t1 = t2.
Proof.
  intros. induction H; inversion H0; try match_some.
  - auto.
  - expr_determ.
  - movelist_determ.
  - expr_determ. 
  - repeat match_some. list_determ. match_some. auto. 
  - expr_determ.
  - expr_determ.
  - expr_determ.
  - auto.
  - expr_determ. expr_determ. store_determ. auto. 
  - expr_determ. load_determ. auto.
  - list_expr_determ.
  - list_expr_determ. inv ASSUME_TRUE.
  - list_expr_determ. inv ASSUME_FAILS.
  - synth_determ. match_some. regmap_determ.
Qed.

(** * Determinacy of lowered semantics  *)
Lemma lowered_single_events:
  forall p, single_events (lowered_sem p).
Proof.
  unfold single_events. intros.
  inv H; auto.
Qed.

Lemma lowered_trace_match:
  forall p s s1 s2 t1 t2,
    lowered_step p s t1 s1 ->
    lowered_step p s t2 s2 ->
    match_traces t1 t2.
Proof.
  intros. eapply internal_determinism in H; eauto.  exploit lowered_single_events; simpl; eauto.
  destruct H. intros. inv H1.
  destruct t1. constructor. destruct t1. constructor.
  simpl in H2. omega.
Qed.

Theorem lowered_determinacy:
  forall (p:program), determinate (lowered_sem p).
Proof.
  intros p. split; simpl; intros.
  - simpl in H, H0. split.
    + eapply lowered_trace_match in H0; eauto.
    + eapply internal_determinism in H; eauto. destruct H. auto.
  - apply lowered_single_events.
  - inv H. inv H0. rewrite FINDF0 in FINDF. inv FINDF. auto.
  - unfold nostep, not. intros. inv H0; inv H.
  - inv H. inv H0. auto.
Qed.

(** * Properties of helper functions  *)
(* max_pos returns something bigger than any index *)
Lemma max_pos'_correct:
    forall A vid v, forall vl:list (positive * A),
      In (vid,v) vl ->
      Pos.le vid (max_pos' vl).
Proof.
  intros.
  induction vl. inversion H.
  destruct a. simpl. inv H.
  - inversion H0. subst. apply Pos.le_max_l.
  - apply IHvl in H0. eapply Pos.le_trans. eauto. apply Pos.le_max_r.
Qed.

Lemma max_pos_correct:
  forall A vid v, forall tree:PTree.t A,
    tree ! vid = Some v ->
    Pos.le vid (max_pos tree).
Proof.
  intros. unfold max_pos.
  apply PTree.elements_correct in H.
  eapply max_pos'_correct. eauto.
Qed.

(* fresh_label returns an identifier associated with no instruction *)
Theorem fresh_label_correct':
  forall c fl,
    fresh_label' c = fl ->
    c ! fl = None.
Proof.
  intros. destruct (c # fl) eqn:HH; auto.
  apply max_pos_correct in HH.
  unfold fresh_label' in H. subst. unfold max_label in HH. exfalso.
  apply Pos2Nat.inj_le in HH. simpl in HH. rewrite Pos2Nat.inj_succ in HH.
  omega.
Qed.

Lemma fresh_label_fuel_correct:
  forall fuel c sug fl,
    fresh_label_fuel fuel sug c = fl ->
    c ! fl = None.
Proof.
  intros fuel. induction fuel; intros.
  - simpl in H. apply fresh_label_correct'. auto.
  - simpl in H. destruct (c#sug) eqn:COD.
    + apply IHfuel in H. auto.
    + subst. auto.
Qed.

Theorem fresh_label_correct:
  forall c fl sug,
    fresh_label sug c = fl ->
    c ! fl = None.
Proof.
  intros. unfold fresh_label in H. eapply fresh_label_fuel_correct. eauto.
Qed.

(** * Safety properties  *)
Lemma safe_step:
  forall p s v pc rm ms,
    safe (specir_sem p) (State s v pc rm ms) ->
    exists s', exists t, Step (specir_sem p) (State s v pc rm ms) t s'.
Proof.
  intros p s v pc rm ms H.
  unfold safe in H. specialize (H (State s v pc rm ms)).
  exploit H. apply star_refl.
  intros [[r FINAL]|[t [s'' STEP]]]. inv FINAL.
  exists s''. exists t. auto.
Qed.

Lemma star_final:
  forall p v s1 s2 t,
    Star (specir_sem p) s1 t s2 -> final_state p s1 v ->  final_state p s2 v.
Proof.
  intros p v s1 s2 t STAR. induction STAR; intros; auto.
  inv H1. inv H. inv STEP.
Qed.

Lemma safe_final:
  forall p v ms,
    safe (specir_sem p) (Final v ms).
Proof.
  intros p v ms. unfold safe. intros s' STAR.
  eapply star_final in STAR. 2: econstructor; eauto. inv STAR. left.
  exists v. constructor.
Qed.

(** * Properties of set_version  *)
(* Set_version does not modify base versions *)
Lemma base_version_unchanged:
  forall p fid f v,
    find_base_version fid p = find_base_version fid (set_version p f v).
Proof.
  unfold find_base_version, find_function, find_function_list. intros.
  unfold set_version, set_version_funlist.
  poseq_destr f fid.
  - destruct ((prog_funlist p)!fid) eqn:FINDF; simpl.
    + rewrite PTree.gss. unfold set_version_function. simpl. auto.
    + rewrite FINDF. auto.
  - destruct ((prog_funlist p)!fid) eqn:FINDF; simpl.
    + destruct ((prog_funlist p)!f) eqn:FINDF'; simpl.
      * rewrite PTree.gso; auto. rewrite FINDF. auto.
      * rewrite FINDF. auto.
    + destruct ((prog_funlist p)!f) eqn:FINDF'; simpl.
      * rewrite PTree.gso; auto. rewrite FINDF. auto.
      * rewrite FINDF. auto.
Qed.    

(* Only the base versions are used to synthesize stackframes *)
Lemma synth_frame_unchanged:
  forall p rm sl s f v,
    synthesize_frame p rm sl s <-> synthesize_frame (set_version p f v) rm sl s.
Proof.
  intros. generalize dependent s. induction sl; intros s; split; intros SYNTH; inv SYNTH; constructor; auto.
  - rewrite <- base_version_unchanged; auto.
  - apply IHsl. auto.
  - erewrite base_version_unchanged; eauto.
  - apply IHsl; auto.
Qed.

(* Finding a function that has not been modified *)
Lemma find_function_unchanged:
  forall p fid fid' v ,
    fid <> fid' ->
    find_function fid p = find_function fid (set_version p fid' v).
Proof.
  unfold find_function, find_function_list. intros p fid fid' v DIFF.
  unfold set_version, set_version_funlist. simpl.
  destruct ((prog_funlist p)!fid) eqn:FINDF; destruct ((prog_funlist p)!fid') eqn:FINDF'.
  - rewrite PTree.gso; auto.
  - rewrite FINDF; auto.
  - rewrite PTree.gso; auto.
  - rewrite FINDF; auto.
Qed.

(* Current version of a function that has not been modified *)
Lemma find_currver_unchanged:
  forall fid fidoptim p vopt,
    fid <> fidoptim ->
    find_currver fid p = find_currver fid (set_version p fidoptim vopt).
Proof.
  intros fid fidoptim p vopt H. apply find_function_unchanged with (p:=p) (v:=vopt) in H.
  unfold find_currver. rewrite <- H. auto.
Qed.

(* Finding the modified function *)
Lemma find_function_same:
  forall p fid v f,
    find_function fid p = Some f ->
    find_function fid (set_version p fid v) = Some (set_version_function v f).
Proof.
  unfold find_function, find_function_list. intros p fid v f FINDF.
  unfold set_version, set_version_funlist, set_version_function. simpl. rewrite FINDF.
  rewrite PTree.gss. auto.
Qed.

(* Current version of the modified function *)
Lemma current_version_same:
  forall f vopt,
    current_version (set_version_function vopt f) = vopt.
Proof.
  intros. unfold current_version. unfold set_version_function. simpl. auto.
Qed.

(* Current version of the modified function *)
Lemma find_currver_same:
  forall f p vopt v,
    find_currver f p = Some v -> 
    find_currver f (set_version p f vopt) = Some vopt.
Proof.
  unfold find_currver. intros f p vopt v H.
  destruct (find_function f p) eqn:FINDF; inv H.
  eapply find_function_same with (v:=vopt) in FINDF. rewrite FINDF.
  rewrite current_version_same. auto.
Qed.

(* set_version does not change the parameters *)
Lemma same_params:
  forall p fid v f f',
    find_function fid p = Some f ->
    find_function fid (set_version p fid v) = Some f' ->
    (fn_params f) = (fn_params f').
Proof.
  unfold find_function, find_function_list, set_version, set_version_funlist. simpl.
  intros p fid v f f' H H0. rewrite H in H0. rewrite PTree.gss in H0. inv H0.
  unfold set_version_function. simpl. auto.
Qed.

(** * Single events  *)
Lemma specir_single_events:
  forall p, single_events (specir_sem p).
Proof.
  unfold single_events. intros.
  inv H; auto. inv STEP; auto.
Qed.

(** * Additional properties  *)
(* All steps require code *)
Lemma step_code:
  forall p s v pc rm ms news t,
    Step (specir_sem p) (State s v pc rm ms) t news ->
    exists i, (ver_code v) ! pc = Some i.
Proof.
  intros. inv H.
  - inv STEP; eauto.
  - inv DEOPT_COND. eauto.
  - inv DEOPT_COND. eauto.
Qed.

Lemma safe_code:
  forall p s v pc rm ms,
    safe (specir_sem p) (State s v pc rm ms) ->
    exists i, (ver_code v) ! pc = Some i.
Proof.
  intros. apply safe_step in H as [s' [t STEP]].
  eapply step_code; eauto.
Qed.

(** * Regmap equivalence  *)
(* We define an equivalence over Regmaps here, weaker than Coq equality *)
Definition regmap_eq (rm1 rm2:reg_map): Prop :=
  forall r:reg, rm1 # r = rm2 # r.

Lemma regmap_eq_refl:
  forall rm, regmap_eq rm rm.
Proof. intros. unfold regmap_eq. intros. auto. Qed.

Lemma regmap_eq_sym:
  forall rm1 rm2, regmap_eq rm1 rm2 -> regmap_eq rm2 rm1.
Proof. unfold regmap_eq. intros. symmetry. apply H. Qed.

Lemma regmap_eq_trans:
  forall rm1 rm2 rm3,
    regmap_eq rm1 rm2 ->
    regmap_eq rm2 rm3 ->
    regmap_eq rm1 rm3.
Proof. unfold regmap_eq. intros. rewrite <- H0. apply H. Qed.

Lemma regmap_eq_insert:
  forall rm1 rm2 r v,
    regmap_eq rm1 rm2 ->
    regmap_eq (rm1#r<-v) (rm2#r<-v).
Proof.
  unfold regmap_eq. intros. poseq_destr r r0.
  - rewrite PTree.gss. rewrite PTree.gss. auto.
  - rewrite PTree.gso; auto. rewrite PTree.gso; auto.
Qed.

Lemma regmap_eq_comm:
  forall rm1 rm2 r1 v1 r2 v2,
    regmap_eq rm1 rm2 ->
    reg_neq r1 r2 = true ->
    regmap_eq ((rm1#r1<-v1) # r2 <- v2) ((rm2#r2<-v2) # r1 <- v1).
Proof.
  unfold regmap_eq. intros. poseq_destr r r1.
  - rewrite PTree.gso.
    + rewrite PTree.gss. rewrite PTree.gss. auto.
    + unfold reg_neq in H0. apply negb_true_iff in H0. apply POrderedType.Positive_as_OT.eqb_neq. auto.
  - poseq_destr r r2.
    + rewrite PTree.gss. rewrite PTree.gso.
      * rewrite PTree.gss. auto.
      * auto.
    + repeat rewrite PTree.gso; auto.
Qed.

Lemma regmap_eq_defined:
  forall rm1 rm2 rs,
    defined rm1 rs ->
    regmap_eq rm1 rm2 ->
    defined rm2 rs.
Proof.
  unfold regmap_eq, defined. intros rm1 rm2 rs H H0.
  destruct rs as [|rs|]; auto. intros. specialize (H0 r). rewrite <- H0. auto.
Qed.

Lemma eval_op_eq:
  forall rm1 rm2 o v,
    regmap_eq rm1 rm2 ->
    eval_op o rm1 v ->
    eval_op o rm2 v.
Proof.
  unfold regmap_eq. intros. inv H0; constructor. rewrite <- H. auto.
Qed.

Lemma eval_expr_eq:
  forall rm1 rm2 e v,
    regmap_eq rm1 rm2 ->
    eval_expr e rm1 v ->
    eval_expr e rm2 v.
Proof.
  unfold regmap_eq. intros. inv H0.
  - inv EVAL. eapply eval_op_eq in EVALL; eauto. eapply eval_op_eq in EVALR; eauto.
    constructor; auto. econstructor; eauto.
  - inv EVAL. eapply eval_op_eq in EVAL0; eauto.
    constructor; auto. econstructor; eauto.
Qed.

Lemma eval_list_expr_eq:
  forall rm1 rm2 le b,
    regmap_eq rm1 rm2 ->
    eval_list_expr le rm1 b ->
    eval_list_expr le rm2 b.
Proof.
  unfold regmap_eq. intros. generalize dependent b. induction le; intros.
  - inv H0. constructor.
  - inv H0.
    + eapply eval_expr_eq in EVAL; eauto. constructor. auto.
    + eapply eval_expr_eq in EVALH; eauto. apply IHle in EVALL. econstructor; eauto.
Qed.

Lemma eval_list_eq:
  forall rm1 rm2 le lv,
    regmap_eq rm1 rm2 ->
    eval_list le rm1 lv ->
    eval_list le rm2 lv.
Proof.
  unfold regmap_eq. intros. generalize dependent lv. induction le; intros.
  - inv H0. constructor.
  - inv H0. apply IHle in EVALL. eapply eval_expr_eq in EVALH; eauto. constructor; auto.
Qed.

Lemma update_movelist_eq:
  forall rm1 rm2 rm2u ml,
    regmap_eq rm1 rm2 ->
    update_movelist ml rm2 rm2u ->
    exists rm1u,
      update_movelist ml rm1 rm1u /\
      regmap_eq rm1u rm2u.
Proof.
  unfold update_movelist. intros. generalize dependent rm2u. induction ml; intros.
  - inv H0. exists rm1. split; auto. constructor.
  - inv H0. apply regmap_eq_sym in H. eapply eval_expr_eq in EVAL; eauto.
    apply IHml in UPDATE as [rm1u [UPDATE EQ]].
    exists (rm1u#r<-v). split. constructor; auto. unfold regmap_eq in *. intros.
    poseq_destr r r0.
    + rewrite PTree.gss. rewrite PTree.gss. auto.
    + rewrite PTree.gso; auto. rewrite PTree.gso; auto.
Qed.

Lemma update_regmap_eq:
  forall rm1 rm2 newrm vm,
    regmap_eq rm1 rm2 ->
    update_regmap vm rm2 newrm ->
    update_regmap vm rm1 newrm.
Proof.
  intros. generalize dependent newrm. induction vm; intros.
  - inv H0. constructor.
  - inv H0. apply regmap_eq_sym in H. eapply eval_expr_eq in EVAL; eauto.
    apply IHvm in UPDATE. constructor; auto.
Qed.

Lemma synthesize_frame_eq:
  forall rm1 rm2 p sl stack,
    regmap_eq rm1 rm2 ->
    synthesize_frame p rm2 sl stack ->
    synthesize_frame p rm1 sl stack.
Proof.
  intros. generalize dependent stack. induction sl; intros.
  - inv H0. constructor.
  - inv H0. eapply update_regmap_eq in UPDATE; eauto. constructor; auto.
Qed.
