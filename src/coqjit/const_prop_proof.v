(* Proof of correctness of constant propagation *)

Require Export List.
Require Export Coqlib.
Require Export Maps.
Require Export common.
Require Export ir_properties.
Require Export internal_simulations.
Require Export interpreter_proof.
Require Export specIR.
Require Export interpreter.
Require Export const_prop.

(** * Abstract Values and equivalence *)
(* Matching a value with an abstract value *)
Definition match_abs_value (v:value) (av:abs_value): Prop :=
  match av with
  | FlatValue.Top => True
  | FlatValue.Bot => False
  | FlatValue.Inj v1 => v = v1
  end.

Definition match_value (ov:option value) (av:abs_value) : Prop :=
  match ov with
  | None => match av with
           | FlatValue.Top => True
           | _ => False
           end
  | Some v => match_abs_value v av
  end.

(* If an abstraction matches a value, a bigger abstraction also does *)
Lemma match_abs_value_increasing:
  forall v abs1 abs2,
    FlatValue.ge abs1 abs2 ->
    match_abs_value v abs2 ->
    match_abs_value v abs1.
Proof.
  intros. destruct abs1; destruct abs2; inv H0; inv H; simpl; auto.
Qed.

Lemma match_value_increasing:
  forall v abs1 abs2,
    FlatValue.ge abs1 abs2 ->
    match_value v abs2 ->
    match_value v abs1.
Proof.
  intros. destruct abs1; destruct abs2; destruct v; try inv H0; try inv H; simpl; auto.
Qed.

Lemma match_val_lub_left:
  forall v absl absr,
    match_abs_value v absl ->
    match_abs_value v (FlatValue.lub absl absr).
Proof.
  intros. destruct absl; inv H; destruct absr; simpl; auto.
  destruct (ValueEq.eq t t0); simpl; auto.
Qed.

Lemma match_val_lub_right:
  forall v absl absr,
    match_abs_value v absr ->
    match_abs_value v (FlatValue.lub absl absr).
Proof.
  intros. destruct absr; inv H; destruct absl; simpl; auto.
  destruct (ValueEq.eq t0 t); simpl; auto.
Qed.

(** * Abstract regmaps properties *)
(* A regmap matches an approximation if all registers do *)
Definition match_regmap (rm:reg_map) (arm:abs_regmap): Prop :=
  forall r, match_value (rm!r) (MapFlatValue.get r arm).

Lemma match_regmap_increasing:
  forall rm arm1 arm2,
    MapFlatValue.ge arm1 arm2 ->
    match_regmap rm arm2 ->
    match_regmap rm arm1.
Proof.
  unfold match_regmap. intros.
  assert (HM: match_value rm # r (MapFlatValue.get r arm2)) by apply H0.
  eapply match_value_increasing; eauto.
Qed.

(* Updating a regmap with a good approximation yields a good approximation *)
Lemma match_regmap_update:
  forall rm arm v av r,
    match_value (Some v) av ->
    match_regmap rm arm ->
    match_regmap (rm # r <- v) (regmap_set r av arm).
Proof.
  intros. unfold match_regmap. intros.
  rewrite MapFlatValue.gsspec; auto.
  destruct (peq r0 r).
  - subst r. rewrite PTree.gss. auto.
  - rewrite PTree.gso; auto.
  - red. intros. specialize (H0 xH). subst arm. simpl in H0. destruct rm. inv H0.  unfold match_value in H0. simpl in H0.
    destruct o; inv H0.
  - unfold FlatValue.eq. red. intros. subst av. inv H.
Qed.

Lemma match_regmap_not_bot:
  forall rm arm,
    match_regmap rm arm ->
    arm <> MapFlatValue.Bot.
Proof.
  intros. red. intros. unfold match_regmap in H. specialize (H xH). subst arm. 
  destruct (rm # 1) eqn:HGET. simpl in H. auto. simpl in H. auto.
Qed.


Lemma match_regmap_generate_true:
  forall rm arm e v,
    match_regmap rm arm ->
    specIR.eval_expr e rm (Vint v) ->
    Zne v 0 ->
    match_regmap rm (generate_true arm e).
Proof.
  intros rm arm e v MATCHRM EVAL ZNE. unfold generate_true.
  destruct e.
  - destruct b; auto.           (* Binexpr *)
    destruct o; destruct o0; auto.
    + inv EVAL. inv EVAL0. inv EVALL. inv EVALR.
      assert (v1 = v2).
      { inv EVALV; f_equal.
        destruct (v0 =? v3) eqn:HEQ. apply Z.eqb_eq in HEQ. auto. inv H. omega. }
        subst. unfold match_regmap. intros. poseq_destr r0 r.
      * rewrite MapFlatValue.gsspec; auto. rewrite peq_true.
           rewrite GETRM. constructor. eapply match_regmap_not_bot; eauto. unfold not; intros. inv H.
      * rewrite MapFlatValue.gsspec; auto. rewrite peq_false; auto.
           eapply match_regmap_not_bot; eauto. unfold not; intros. inv H.
    + inv EVAL. inv EVAL0. inv EVALL. inv EVALR.
      assert (v1 = v2).
      { inv EVALV; f_equal.
        destruct (v0 =? v3) eqn:HEQ. apply Z.eqb_eq in HEQ. auto. inv H. omega. }
      subst. unfold match_regmap. intros. poseq_destr r0 r.
      * rewrite MapFlatValue.gsspec; auto. rewrite peq_true.
        rewrite GETRM. constructor. eapply match_regmap_not_bot; eauto. unfold not; intros. inv H.
      * rewrite MapFlatValue.gsspec; auto. rewrite peq_false; auto.
        eapply match_regmap_not_bot; eauto. unfold not; intros. inv H.
  - destruct u; auto.           (* Unexpr *)
    destruct o; auto. inv EVAL. inv EVAL0. inv EVALV.
    assert (v1 = 0).
    { inv EVAL. unfold int_neg in ZNE. destruct v1; auto; omega. }
    subst. unfold match_regmap. intros. poseq_destr r0 r.
    + inv EVAL. rewrite GETRM.
      rewrite MapFlatValue.gsspec; auto. rewrite peq_true. constructor.
      eapply match_regmap_not_bot; eauto. unfold not; intros. inv H.
    + rewrite MapFlatValue.gsspec; auto. rewrite peq_false; auto.
      eapply match_regmap_not_bot; eauto. unfold not; intros. inv H.
Qed.


Lemma match_regmap_assert:
  forall rm arm le,
    match_regmap rm arm ->
    specIR.eval_list_expr le rm true ->
    match_regmap rm (generate_true_list arm le).
Proof.
  intros. generalize dependent arm. induction le; auto.
  simpl. intros. inv H0.
  eapply IHle; auto.
  eapply match_regmap_generate_true; eauto.
Qed.  

(** * Preservation of evaluation  *)
(* Replacing with a good approximations evaluates to the same result *)
Lemma eval_op_abs_correct:
  forall o rm arm v,
    specIR.eval_op o rm v ->
    match_regmap rm arm ->
    match_value (Some v) (eval_op_abs o arm).
Proof.
  intros. destruct o; inv H; simpl; auto.
  unfold match_abs_value. specialize (H0 r). rewrite GETRM in H0.
  unfold eval_reg_abs.
  destruct (MapFlatValue.get r arm); inv H0; auto.
Qed.


(* If an abstract regmap is correct, then the real value is matched with the abstract evaluation *)
Lemma eval_binop_abs_correct:
  forall b o1 o2 rm v arm,
    specIR.eval_binop b o1 o2 rm v ->
    match_regmap rm arm ->
    match_abs_value v (eval_binop_abs b o1 o2 arm).
Proof.
  intros b o1 o2 rm v arm EVALB MATCHRM.
  unfold match_regmap in MATCHRM. inv EVALB.
  destruct o1; destruct o2; inv EVALL; inv EVALR; try apply MATCHRM in H1; try apply MATCHRM in H4.
  - unfold eval_binop_abs. simpl. unfold eval_reg_abs.
    assert (match_value (Some v1) (MapFlatValue.get r arm)).
    { specialize (MATCHRM r). rewrite GETRM in MATCHRM. auto. }
    assert (match_value (Some v2) (MapFlatValue.get r0 arm)).
    { specialize (MATCHRM r0). rewrite GETRM0 in MATCHRM. auto. }
    destruct (MapFlatValue.get r arm); inv H; destruct (MapFlatValue.get r0 arm); inv H0; simpl; auto.
    rewrite eval_binop_values_correct in EVALV. rewrite EVALV. constructor.
  - unfold eval_binop_abs. simpl.
    unfold eval_reg_abs.
    assert (match_value (Some v1) (MapFlatValue.get r arm)).
    { specialize (MATCHRM r). rewrite GETRM in MATCHRM. auto. }
    destruct (MapFlatValue.get r arm); inv H; simpl; auto.
    rewrite eval_binop_values_correct in EVALV. rewrite EVALV. constructor. 
  - unfold eval_binop_abs. simpl.
    assert (match_value (Some v2) (MapFlatValue.get r arm)).
    { specialize (MATCHRM r). rewrite GETRM in MATCHRM. auto. }
    unfold eval_reg_abs. destruct (MapFlatValue.get r arm); inv H; simpl; auto.
    rewrite eval_binop_values_correct in EVALV. rewrite EVALV. constructor.
  - inv EVALV; simpl; auto.
Qed.

Lemma eval_unop_abs_correct:
  forall u o rm v arm,
    specIR.eval_unop u o rm v ->
    match_regmap rm arm ->
    match_abs_value v (eval_unop_abs u o arm).
Proof.
  intros u o rm v arm EVAL MATCHRM.  unfold match_regmap in MATCHRM. inv EVAL.
  destruct o; inv EVAL0.
  - unfold eval_unop_abs. simpl. unfold eval_reg_abs.
    assert (match_value (Some v0) (MapFlatValue.get r arm)).
    { specialize (MATCHRM r). rewrite GETRM in MATCHRM. auto. }
    destruct (MapFlatValue.get r arm); inv GETRM; simpl; auto.
    inv H. inv EVALV; simpl; auto.
  - unfold eval_unop_abs. simpl. inv EVALV; simpl; auto.
Qed.

Lemma eval_expr_abs_correct:
  forall e rm v arm,
    specIR.eval_expr e rm v ->
    match_regmap rm arm ->
    match_abs_value v (eval_expr_abs e arm).
Proof.
  intros. inv H.
  - simpl. eapply eval_binop_abs_correct; eauto.
  - simpl. eapply eval_unop_abs_correct; eauto.
Qed.

(* Updating with a movelist in both concrete and abstract regmap *)
Lemma match_regmap_update_movelist:
  forall ml rm arm newrm,
    match_regmap rm arm ->
    specIR.update_movelist ml rm newrm ->
    match_regmap newrm (list_transf ml arm).
Proof.
  intros vm. induction vm; intros.
  - unfold list_transf. simpl. inv H0. auto.
  - unfold list_transf. simpl. destruct a as [r ex]. inv H0.
    apply match_regmap_update.
    + simpl. eapply eval_expr_abs_correct; eauto.
    + eapply IHvm; eauto.
Qed.

(** * Correctness of replacing  *)
(* Replacing operands does not affect the evaluation *)
Lemma replace_binop_correct:
  forall b o1 o2 ro1 ro2 v rm arm,
    specIR.eval_binop b o1 o2 rm v ->
    match_regmap rm arm ->
    replace_op arm o1 = ro1 ->
    replace_op arm o2 = ro2 ->
    specIR.eval_binop b ro1 ro2 rm v.
Proof.
  intros b o1 o2 ro1 ro2 v rm arm EVALB MATCHRM REPLACE1 REPLACE2.
  destruct o1; destruct o2.
  - inv REPLACE1. unfold replace_op. simpl. unfold eval_reg_abs. unfold match_regmap in MATCHRM. inv EVALB.
    assert (MR: match_value (Some v1) (MapFlatValue.get r arm)).
    { specialize (MATCHRM r). inv EVALL. rewrite GETRM in MATCHRM. auto. }
    assert (MR0: match_value (Some v2) (MapFlatValue.get r0 arm)).
    { specialize (MATCHRM r0). inv EVALR. rewrite GETRM in MATCHRM. auto. }
    inv EVALL. inv EVALR.
    destruct (MapFlatValue.get r arm) eqn:HR;
      destruct (MapFlatValue.get r0 arm) eqn:HR0; auto; inv MR; inv MR0; econstructor; eauto; constructor; auto.
  - inv REPLACE2. unfold replace_op. simpl. unfold eval_reg_abs. unfold match_regmap in MATCHRM. inv EVALB.
    assert (MR: match_value (Some v1) (MapFlatValue.get r arm)).
    { specialize (MATCHRM r). inv EVALL. rewrite GETRM in MATCHRM. auto. }
    inv EVALL. inv EVALR.
    destruct (MapFlatValue.get r arm) eqn:HR; auto; inv MR; econstructor; eauto; constructor; auto.
  - inv REPLACE1. unfold replace_op. simpl. unfold eval_reg_abs. unfold match_regmap in MATCHRM. inv EVALB.
    assert (MR: match_value (Some v2) (MapFlatValue.get r arm)).
    { specialize (MATCHRM r). inv EVALR. rewrite GETRM in MATCHRM. auto. }
    inv EVALL. inv EVALR.
    destruct (MapFlatValue.get r arm) eqn:HR; auto; inv MR; econstructor; eauto; constructor; auto.
  - inv REPLACE1. unfold replace_op. simpl. auto.
Qed.

Lemma replace_unop_correct:
  forall u o ro v rm arm,
    specIR.eval_unop u o rm v ->
    match_regmap rm arm ->
    replace_op arm o = ro ->
    specIR.eval_unop u ro rm v.
Proof.
  intros u o ro v rm arm EVAL MATCHRM REPLACE. destruct o.
  - inv EVAL. inv EVAL0.
    assert (MR: match_value (Some v0) (MapFlatValue.get r arm)).
    { specialize (MATCHRM r). rewrite GETRM in MATCHRM. auto. }
    unfold replace_op. unfold eval_op_abs, eval_reg_abs.
    destruct (MapFlatValue.get r arm) eqn:HR; inv MR.
    + econstructor; eauto. constructor.
    + econstructor; eauto. constructor. auto.
  - inv REPLACE. inv EVAL. unfold replace_op. simpl.
    inv EVAL0. inv EVALV; econstructor; try constructor; auto.
Qed.

Lemma replace_op_correct:
  forall o ro v rm arm,
    specIR.eval_op o rm v ->
    match_regmap rm arm ->
    replace_op arm o = ro ->
    specIR.eval_op ro rm v.
Proof.
  intros. destruct o.
  - inv H.
    assert (MR: match_value (Some v) (MapFlatValue.get r arm)).
    { specialize (H0 r). rewrite GETRM in H0. auto. }
    unfold replace_op, eval_op_abs, eval_reg_abs.
    destruct (MapFlatValue.get r arm); inv MR; constructor. auto.
  - inv H. unfold replace_op. simpl. constructor.
Qed.

Theorem replace_expr_correct:
  forall e re v rm arm,
    specIR.eval_expr e rm v ->
    match_regmap rm arm ->
    transf_expr (replace_op arm) e = re ->
    specIR.eval_expr re rm v.
Proof.
  intros. destruct e.
  - inv H. inv EVAL. eapply replace_op_correct in EVALL; eauto.
    eapply replace_op_correct in EVALR; eauto. simpl.
    constructor. econstructor; eauto.
  - inv H. inv EVAL. eapply replace_op_correct in EVAL0; eauto.
    simpl. constructor. econstructor; eauto.
Qed.

Theorem replace_expr_list_correct:
  forall le rle v rm arm,
    specIR.eval_list_expr le rm v ->
    match_regmap rm arm ->
    transf_expr_list (replace_op arm) le = rle ->
    specIR.eval_list_expr rle rm v.
Proof.
  intros. generalize dependent rle. induction le; intros.
  - inv H. simpl. constructor.
  - inv H.
    + simpl. apply eval_cons_false. eapply replace_expr_correct; eauto.
    + simpl. eapply eval_cons_true; eauto. eapply replace_expr_correct; eauto.
Qed.

Theorem replace_expr_evalist_correct:
  forall le v rm arm,
    specIR.eval_list le rm v ->
    match_regmap rm arm ->
    specIR.eval_list (map (transf_expr (replace_op arm)) le) rm v.
Proof.
  intros. generalize dependent v. induction le; intros.
  - inv H. simpl. constructor.
  - inv H. simpl. constructor.
    + eapply replace_expr_correct; eauto.
    + apply IHle. auto.
Qed.

Theorem transf_vm_correct:
  forall vm rm newrm arm,
    specIR.update_regmap vm rm newrm ->
    match_regmap rm arm ->
    specIR.update_regmap (transf_vm (transf_expr (replace_op arm)) vm) rm newrm.
Proof.
  intros. induction H.
  - constructor.
  - simpl. constructor.
    eapply replace_expr_correct; eauto.
    apply IHupdate_regmap. auto.
Qed.

Theorem transf_ml_correct':
  forall ml rm newrm arm rmeval,
    specIR.update_movelist' ml rmeval rm newrm ->
    match_regmap rmeval arm ->
    specIR.update_movelist' (transf_ml (transf_expr (replace_op arm)) ml) rmeval rm newrm.
Proof.
  intros. induction H.
  - constructor.
  - simpl. constructor.
    eapply replace_expr_correct; eauto.
    apply IHupdate_movelist'. auto.
Qed.

Theorem transf_ml_correct:
  forall ml rm newrm arm,
    specIR.update_movelist ml rm newrm ->
    match_regmap rm arm ->
    specIR.update_movelist (transf_vm (transf_expr (replace_op arm)) ml) rm newrm.
Proof.
  intros. unfold specIR.update_movelist in *.
  apply transf_ml_correct'; auto.
Qed.
    
(* Same operands evaluate to the same result *)
Lemma op_eqb_same:
  forall o1 o2 rm v,
    op_eqb o1 o2 = true ->
    (specIR.eval_op o1 rm v <->
    specIR.eval_op o2 rm v).
Proof.
  intros. split; intros.
  - inv H0; inv H; destruct o2; inv H1.
    + destruct v; destruct v0; inv H0. apply Z.eqb_eq in H1. subst. constructor.
    + apply Pos.eqb_eq in H0. subst. constructor. auto.
  - inv H0; inv H; destruct o1; inv H1.
    + destruct v; destruct v0; inv H0. apply Z.eqb_eq in H1. subst. constructor.
    + apply Pos.eqb_eq in H0. subst. constructor. auto.
Qed.

Lemma Zgtb_irrefl:
  forall n,
    (n >? n) = false.
Proof.
  intros. rewrite Z.gtb_ltb. rewrite Z.ltb_irrefl. auto.
Qed.

Lemma Zgeb_refl:
  forall n,
    (n >=? n) = true.
Proof.
  intros. rewrite Z.geb_leb. rewrite Z.leb_refl. auto.
Qed.

Ltac ok_str:=
  repeat (econstructor; eauto).

(** * Correctness of strength reduction  *)
(* Strength reduction does not change evaluation *)
Theorem strength_reduction_correct:
  forall e rm v,
    specIR.eval_expr e rm v -> specIR.eval_expr (strength_reduction e) rm v.
Proof.
  intros. inv H.
  - inv EVAL. inv EVALV; simpl.
    + destruct o1; destruct o2; inv EVALL; inv EVALR; ok_str.
      * destruct v3; ok_str. rewrite Z.add_0_r. ok_str.
      * destruct v0; ok_str.
      * destruct v0; destruct v3; try rewrite Z.add_0_l; try rewrite Z.add_0_r; ok_str.
    + destruct o1; destruct o2; inv EVALL; inv EVALR; ok_str.
      * destruct (reg_eqb r r0) eqn:HEQ. apply Pos.eqb_eq in HEQ. subst. simpl.
        rewrite Pos.eqb_refl. rewrite GETRM0 in GETRM. inv GETRM. rewrite Z.sub_diag. ok_str.
        simpl. rewrite HEQ. ok_str.
      * destruct v3; ok_str. rewrite Z.sub_0_r; ok_str.
      * destruct v0; ok_str.
      * destruct v0; destruct v3; try rewrite Z.sub_0_r; try rewrite Z.sub_0_l; ok_str.
        ** destruct (Pos.eqb p p0) eqn:HEQ; simpl; rewrite HEQ; ok_str.
           apply Pos.eqb_eq in HEQ. subst. rewrite Z.pos_sub_diag. ok_str.
        ** destruct (Pos.eqb p p0) eqn:HEQ; simpl; rewrite HEQ; ok_str.
           apply Pos.eqb_eq in HEQ. subst. rewrite Z.pos_sub_diag. ok_str.
    + destruct o1; destruct o2; inv EVALL; inv EVALR; ok_str.
      * destruct v3; ok_str. rewrite Z.mul_0_r. ok_str. destruct p; ok_str.
        rewrite Z.mul_1_r. ok_str.
      * destruct v0; ok_str. destruct p; ok_str. rewrite Z.mul_1_l. ok_str.
      * destruct v0; destruct v3; ok_str.
        destruct p; ok_str. destruct p; destruct p0; try rewrite Z.mul_1_r; ok_str.
        destruct p; ok_str. destruct p; ok_str; destruct p0; ok_str; rewrite Z.mul_1_r; ok_str.
    + destruct o1; destruct o2; inv EVALL; inv EVALR; ok_str.
      * destruct (reg_eqb r r0) eqn:HEQ. apply Pos.eqb_eq in HEQ. subst. simpl.
        rewrite Pos.eqb_refl. rewrite GETRM0 in GETRM. inv GETRM. rewrite Zgtb_irrefl. ok_str.
        simpl. rewrite HEQ. ok_str.
      * destruct (Z.eqb v0 v3) eqn:HEQ. apply Z.eqb_eq in HEQ. subst. simpl.
        rewrite Z.eqb_refl. rewrite Zgtb_irrefl. ok_str.
        simpl. rewrite HEQ. ok_str.
    + destruct o1; destruct o2; inv EVALL; inv EVALR; ok_str.
      * destruct (reg_eqb r r0) eqn:HEQ. apply Pos.eqb_eq in HEQ. subst. simpl.
        rewrite Pos.eqb_refl. rewrite GETRM0 in GETRM. inv GETRM. rewrite Z.ltb_irrefl. ok_str.
        simpl. rewrite HEQ. ok_str.
      * destruct (Z.eqb v0 v3) eqn:HEQ. apply Z.eqb_eq in HEQ. subst. simpl.
        rewrite Z.eqb_refl. rewrite Z.ltb_irrefl. ok_str.
        simpl. rewrite HEQ. ok_str.
    + destruct o1; destruct o2; inv EVALL; inv EVALR; ok_str.
      * destruct (reg_eqb r r0) eqn:HEQ. apply Pos.eqb_eq in HEQ. subst. simpl.
        rewrite Pos.eqb_refl. rewrite GETRM0 in GETRM. inv GETRM. rewrite Zgeb_refl. ok_str.
        simpl. rewrite HEQ. ok_str.
      * destruct (Z.eqb v0 v3) eqn:HEQ. apply Z.eqb_eq in HEQ. subst. simpl.
        rewrite Z.eqb_refl. rewrite Zgeb_refl. ok_str.
        simpl. rewrite HEQ. ok_str.
    + destruct o1; destruct o2; inv EVALL; inv EVALR; ok_str.
      * destruct (reg_eqb r r0) eqn:HEQ. apply Pos.eqb_eq in HEQ. subst. simpl.
        rewrite Pos.eqb_refl. rewrite GETRM0 in GETRM. inv GETRM. rewrite Z.leb_refl. ok_str.
        simpl. rewrite HEQ. ok_str.
      * destruct (Z.eqb v0 v3) eqn:HEQ. apply Z.eqb_eq in HEQ. subst. simpl.
        rewrite Z.eqb_refl. rewrite Z.leb_refl. ok_str.
        simpl. rewrite HEQ. ok_str.
    + destruct o1; destruct o2; inv EVALL; inv EVALR; ok_str.
      * destruct (reg_eqb r r0) eqn:HEQ. apply Pos.eqb_eq in HEQ. subst. simpl.
        rewrite Pos.eqb_refl. rewrite GETRM0 in GETRM. inv GETRM. rewrite Z.eqb_refl. ok_str.
        simpl. rewrite HEQ. ok_str.
      * destruct (Z.eqb v0 v3) eqn:HEQ. apply Z.eqb_eq in HEQ. subst. simpl.
        rewrite Z.eqb_refl. ok_str.
        simpl op_eqb. rewrite HEQ at 1. rewrite <- HEQ. ok_str.        
  - inv EVAL. inv EVALV; inv EVAL0; ok_str.
Qed.

Theorem strength_reduction_list_correct:
  forall le rm v,
    specIR.eval_list_expr le rm v ->
    specIR.eval_list_expr (map strength_reduction le) rm v.
Proof.
  intros. induction le; simpl; auto. inv H.
  - apply eval_cons_false. apply strength_reduction_correct. auto.
  - eapply eval_cons_true; eauto. apply strength_reduction_correct. auto.
Qed.

Theorem strength_reduction_evalist_correct:
  forall le rm v,
    specIR.eval_list le rm v ->
    specIR.eval_list (map strength_reduction le) rm v.
Proof.
  intros. generalize dependent v. induction le; intros; simpl; auto. inv H.
  constructor. apply strength_reduction_correct. auto.
  apply IHle. auto.
Qed.

Theorem strength_reduction_transf_vm_correct:
  forall vm rm newrm,
    specIR.update_regmap vm rm newrm ->
    specIR.update_regmap (transf_vm strength_reduction vm) rm newrm.
Proof.
  intros. induction H.
  - simpl. constructor.
  - simpl. constructor.
    apply strength_reduction_correct. auto.
    apply IHupdate_regmap.
Qed.

Theorem strength_reduction_transf_ml_correct':
  forall ml rm newrm rmeval,
    specIR.update_movelist' ml rmeval rm newrm ->
    specIR.update_movelist' (transf_vm strength_reduction ml) rmeval rm newrm.
Proof.
  intros. induction H.
  - simpl. constructor.
  - simpl. constructor.
    apply strength_reduction_correct. auto.
    apply IHupdate_movelist'.
Qed.

Theorem strength_reduction_transf_ml_correct:
  forall ml rm newrm,
    specIR.update_movelist ml rm newrm ->
    specIR.update_movelist (transf_vm strength_reduction ml) rm newrm.
Proof.
  intros. unfold specIR.update_movelist in *.
  apply strength_reduction_transf_ml_correct'. auto.
Qed.

Ltac strength_simpl:=
  match goal with
  | [ H: specIR.eval_op (Cst ?v) ?rm ?r |- _ ] => inv H
  | [ H: specIR.eval_unop ?u ?o ?rm ?v |- _ ] => inv H
  | [ H: specIR.eval_unop_value ?u ?o ?v |- _ ] => inv H
  | [ H: specIR.eval_binop ?b ?o1 ?o2 ?rm ?v |- _ ] => inv H
  | [ H: specIR.eval_binop_values ?b ?o1 ?o2 ?v |- _ ] => inv H
  | [ H: specIR.eval_expr ?e ?rm ?v |- _ ] => inv H
  end.

Ltac op_determ' :=
  match goal with
  | H:specIR.eval_op ?o ?rm ?r1, H1:specIR.eval_op ?o ?rm ?r2
    |- _ => apply eval_op_determ with (v1 := r2) in H; inv H; subst; auto
  end.

Ltac str:=
  repeat strength_simpl; repeat op_determ'; repeat match_some; try omega; auto.

Lemma reg_eqb_true:
  forall r r0,
    reg_eqb r r0 = true -> r = r0.
Proof.
  intros. unfold reg_eqb in H. poseq_destr r r0. auto. inv H.
Qed.
  
(* Because of behavior improving, we need the source to evaluate *)
Theorem correct_strength_reduction:
  forall e rm v1 v2,
    specIR.eval_expr e rm v1 ->
    specIR.eval_expr (strength_reduction e) rm v2 ->
    v1 = v2.
Proof.
  intros e rm v1 v2 EVAL1 EVAL2.  
  inv EVAL1; inv EVAL.
  - destruct binop; inv EVALV.
    + inv EVAL2.
      * destruct o1; destruct o2; try destruct v; inv H0; inv EVAL; try solve[str].
        ** destruct z; inv H1; inv EVALV; str.
        ** destruct z; inv H1; inv EVALV; str.
        ** destruct z; destruct v0; try destruct z; inv H1; str.
      * destruct o1; destruct o2; try destruct v; try destruct z; inv H0;
          inv EVAL; str; try destruct v5; try inv H1; inv EVAL0; auto.
        rewrite Z.add_0_r. auto.        
    + inv EVAL2.
      * destruct o1; destruct o2; inv H0; inv EVAL; try solve[str].
        ** destruct v0. destruct v1. destruct v2.
           destruct (reg_eqb r r0); inv H1. inv EVALV.
           inv EVALL. inv EVALL0. match_some. inv EVALR. inv EVALR0. match_some. auto.
        ** destruct v; inv H1. destruct z; inv H0; str.
        ** destruct v; inv H1. destruct z; inv H0; str.
        ** destruct v; inv H1. destruct v0. inv EVALR. inv EVALL.
           destruct v4; destruct v5; inv H0; try solve [str]; poseq_destr p p0; inv H1; str.
      * destruct o1; destruct o2.
        ** destruct (op_eqb (Reg r) (Reg r0)) eqn:HEQ; inv H0. inv HEQ. apply reg_eqb_true in H0. subst.
           inv EVALL. inv EVALR. str. rewrite Z.sub_diag. auto.
        ** destruct v. destruct z; inv H0. str. rewrite Z.sub_0_r. auto.
        ** destruct v. destruct z; inv H0. str.
        ** destruct v. destruct z; inv H0; destruct v0; destruct z; inv H1; try solve[str].
           poseq_destr p p0; inv H0; str. rewrite Z.sub_diag. auto.
           poseq_destr p p0; inv H0; str. rewrite Z.sub_diag. auto.
    + inv EVAL2.
      * destruct o1; destruct o2; simpl in H0.
        ** destruct (reg_eqb r r0); inv H0; inv EVAL; str.
        ** destruct v. destruct z; inv H0. destruct p; inv H1; str. str.
        ** destruct v. destruct z; inv H0. destruct p; inv H1; str. str.
        ** destruct v; destruct v0; try destruct z; try destruct z0; inv H0; try solve[str];
             destruct p; try destruct p0; inv H1; str.
      * destruct o1; destruct o2; inv H0.
        ** destruct v; inv H1. destruct z; inv H0. inv EVAL. str. rewrite Z.mul_0_r. auto.
           destruct p; inv H1. inv EVAL. str. rewrite Z.mul_1_r. auto.
        ** destruct v; inv H1. destruct z; inv H0; inv EVAL. str.
           destruct p; inv H1. str. rewrite Z.mul_1_l. auto.
        ** destruct v; destruct v0; try destruct z; try destruct z0; try destruct p; try destruct p0; inv H1; inv EVAL; str; rewrite Z.mul_1_r; auto.
    + inv EVAL2.
      * destruct (op_eqb o1 o2) eqn:HEQ; inv H0. inv EVAL. str.
      * destruct (op_eqb o1 o2) eqn:HEQ; inv H0. inv EVAL. str. rewrite op_eqb_same in EVALL; eauto.
        str. rewrite Zgtb_irrefl. auto.
    + inv EVAL2.
      * destruct (op_eqb o1 o2) eqn:HEQ; inv H0. inv EVAL. str.
      * destruct (op_eqb o1 o2) eqn:HEQ; inv H0. inv EVAL. str. rewrite op_eqb_same in EVALL; eauto.
        str. rewrite Z.ltb_irrefl. auto.
    + inv EVAL2.
      * destruct (op_eqb o1 o2) eqn:HEQ; inv H0. inv EVAL. str.
      * destruct (op_eqb o1 o2) eqn:HEQ; inv H0. inv EVAL. str. rewrite op_eqb_same in EVALL; eauto.
        str. rewrite Zgeb_refl. auto.
    + inv EVAL2.
      * destruct (op_eqb o1 o2) eqn:HEQ; inv H0. inv EVAL. str.
      * destruct (op_eqb o1 o2) eqn:HEQ; inv H0. inv EVAL. str. rewrite op_eqb_same in EVALL; eauto.
        str. rewrite Z.leb_refl. auto.
    + inv EVAL2.
      * destruct (op_eqb o1 o2) eqn:HEQ; inv H0. inv EVAL. str.
      * destruct (op_eqb o1 o2) eqn:HEQ; inv H0. inv EVAL. str. rewrite op_eqb_same in EVALL; eauto.
        str. rewrite Z.eqb_refl. auto.
  - inv EVAL2. inv EVAL. op_determ'. unop_value_determ.
Qed.

(** * Correctness of simplifying expressions  *)
(* simp_expr does not change the result of an evaluation *)
Lemma simpl_expr_correct:
  forall rm e v,
    specIR.eval_expr e rm v <-> specIR.eval_expr (simpl_expr e) rm v.
Proof.
  intros rm e v. split; intros.
  - inv H; inv EVAL.
    + destruct o1 eqn:HO1; destruct o2 eqn:HO2; simpl; inv HO1; try inv HO3; try constructor; try econstructor; eauto.
      inv EVALR. inv EVALL. 
      apply eval_binop_values_correct in EVALV. rewrite EVALV. constructor. econstructor; econstructor; eauto.
    + destruct o eqn:HO; simpl; try constructor; try econstructor; eauto.
      apply eval_unop_value_correct in EVALV. inv EVAL0. rewrite EVALV.
      constructor. econstructor; econstructor; eauto.
  - inv H; inv H1.
    + destruct e; inv H0; destruct o; inv H1; constructor; inv EVAL.
      * econstructor; eauto.
      * destruct o0; inv H0. econstructor; eauto. destruct (eval_binop_values b v0 v3); inv H1.
        inv EVALL. inv EVALR. econstructor; try econstructor; eauto.
      * destruct (eval_unop_value u v0); inv H0.
    + destruct e; inv H0; destruct o0; inv H1; try destruct o1; try inv H0; constructor.
      * inv EVAL. destruct (eval_binop_values b v0 v1) eqn:H; inv H1. inv EVAL0.
        econstructor; try econstructor; eauto. apply eval_binop_values_correct. inv EVALV. auto.
      * inv EVAL. econstructor; eauto.
      * inv EVAL. destruct (eval_unop_value u v0) eqn:H; inv H1; inv EVAL0.
        inv EVALV. apply eval_unop_value_correct in H. econstructor; try econstructor; eauto.
        econstructor; eauto. econstructor.
Qed.

(** * Correctness of the analysis  *)
(* The iterative analysis is correct *)
Lemma analyze_successor:
  forall v pc i pc' abs params,
    kildall_constprop_analysis (ver_code v) params (ver_entry v) = Some abs ->
    (ver_code v)#pc = Some i ->
    In pc' (instr_succ i) ->
    MapFlatValue.ge (absstate_get pc' abs) (constprop_transf (ver_code v) pc (absstate_get pc abs)).
Proof.
  intros. unfold kildall_constprop_analysis in H.
  eapply const_prop.DS.fixpoint_solution; eauto.
  intros.
  unfold constprop_transf.
  assert (@PTree.get (list positive) pc (PTree.map1 instr_succ (ver_code v)) = Some (instr_succ i)).
  { rewrite PTree.gmap1. unfold option_map. rewrite H0. auto. }
  unfold successors_list. rewrite H2.
  simpl. auto.
Qed.

Theorem analyze_correct:
  forall v pc i pc' abs params rm,
    kildall_constprop_analysis (ver_code v) params (ver_entry v) = Some abs ->
    (ver_code v)#pc = Some i ->
    In pc' (instr_succ i) ->
    match_regmap rm (constprop_transf (ver_code v) pc (absstate_get pc abs)) ->
    match_regmap rm (absstate_get pc' abs).
Proof.
  intros. eapply analyze_successor in H; eauto.
  eapply match_regmap_increasing; eauto.
Qed.

Theorem analyze_init':
  forall rm params valist,
    specIR.init_regs valist params = Some rm ->
    match_regmap rm (init_arm_params params).
Proof.
  intros. replace (init_arm_params params) with (MapFlatValue.top) by (destruct params; simpl; auto).
  unfold match_regmap. intros r. simpl. rewrite PTree.gempty. unfold match_value. simpl.
  destruct (rm # r); auto.
Qed.  
  
Theorem analyze_init:
  forall rm v params abs valist,
    kildall_constprop_analysis (ver_code v) params (ver_entry v) = Some abs ->
    specIR.init_regs valist params = Some rm ->
    match_regmap rm (absstate_get (ver_entry v) abs).
Proof.
  unfold kildall_constprop_analysis. intros rm v params abs valist FIX INIT.
  assert (A: MapFlatValue.ge (absstate_get (ver_entry v) abs) (init_arm_params params)).
  { eapply const_prop.DS.fixpoint_entry; eauto. left. auto. }
  eapply match_regmap_increasing; eauto.
  eapply analyze_init'; eauto.
Qed.
  
(** *  Matching stacks and properties *)
(* identical stackframes except that the unoptimized version MAY be replaced with the optimized one *)
Inductive match_stackframe (v:version) (params:list reg): stackframe -> stackframe -> Prop :=
| frame_same:
    forall sf, (match_stackframe v params) sf sf
| frame_opt:
    forall r vopt lbl rm abs,
      constant_propagation_version v params = OK vopt ->
      kildall_constprop_analysis (ver_code v) params (ver_entry v) = Some abs ->
      (forall val, match_regmap (rm # r <- val) (absstate_get lbl abs)) ->
      (match_stackframe v params) (Stackframe r v lbl rm) (Stackframe r vopt lbl rm).

(* Generalizing match_stackframe to the entire stack *)
Inductive match_stack (v:version) (params:list reg): stack -> stack -> Prop :=
| match_nil:
    (match_stack v params) nil nil
| match_cons:
    forall s s' sf sf'
      (MS: (match_stack v params) s s')
      (MSF: (match_stackframe v params) sf sf'),
      (match_stack v params) (sf::s) (sf'::s').

(* Creating synth frames in the new program yields matching results *)
Lemma match_synth_frames:
  forall p rm sl synth fidoptim func currver vopt synthopt,
    specIR.synthesize_frame p rm sl synth ->
    find_function fidoptim p = Some func ->
    current_version func = currver ->
    constant_propagation_version currver (fn_params func) = OK vopt ->
    specIR.synthesize_frame (set_version p fidoptim vopt) rm sl synthopt ->
    (match_stack currver (fn_params func)) synth synthopt.
Proof.
  intros p rm sl synth fidoptim func currver vopt synthopt SYNTH FINDF CURRVER CSTPROP SYNTHOPT.
  generalize dependent synthopt.
  induction SYNTH; intros. inv SYNTHOPT. constructor.
  inv SYNTHOPT. constructor.
  - apply IHSYNTH; auto.
  - eapply update_regmap_determ in UPDATE; eauto. subst.
    erewrite <- base_version_unchanged in FINDV0; eauto. rewrite FINDV in FINDV0. inv FINDV0. constructor.
Qed.

Lemma match_stack_same:
  forall s v params,
    match_stack v params s s.
Proof.
  intros s v params. induction s.
  - constructor.
  - constructor. auto. constructor.
Qed.

Lemma match_synth:
  forall p rm sl synth fidoptim func currver vopt,
    specIR.synthesize_frame p rm sl synth ->
    find_function fidoptim p = Some func ->
    current_version func = currver ->
    constant_propagation_version currver (fn_params func) = OK vopt ->
    exists synthopt, specIR.synthesize_frame (set_version p fidoptim vopt) rm sl synthopt /\
                (match_stack currver (fn_params func)) synth synthopt.
Proof.
  intros. exists synth. erewrite synth_frame_unchanged in H. split. eauto.
  apply match_stack_same.
Qed.

(* Adding the same synthesized frames to the stack preserves match_stack *)
Lemma match_app:
  forall synth s s' v params,
    (match_stack v params) s s' ->
    (match_stack v params) (synth++s) (synth++s').
Proof.
  intros. induction synth.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. apply match_cons. auto. constructor.
Qed.

Lemma app_match:
  forall synth synthopt s s' v params,
    (match_stack v params) s s' ->
    (match_stack v params) synth synthopt ->
    (match_stack v params) (synth++s) (synthopt++s').
Proof.
  intros. induction H0.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. apply match_cons; auto.
Qed.

(** * Match states relation  *)
(* This proof is a lockstep forward internal loud simulation.
   Each step of the source is matched with a step of the optimized program.
   No index is needed for the match_states invariant.

<<
                 
       st1 --------------- st2
        |                   |
       t|                   |t
        |                   |
        v                   v
       st1'--------------- st2'
                 
>>
*)

(* The mixed lockstep simulation relation *)
Inductive match_states (p:program) (v:version) (params:list reg) : unit -> specIR.state -> specIR.state -> Prop :=
| lock_match:
    forall s s' vopt pc rm ms abs
      (CST_PROP: constant_propagation_version v params = OK vopt)
      (ANALYSIS: kildall_constprop_analysis (ver_code v) params (ver_entry v) = Some abs)
      (MATCHSTACK: (match_stack v params) s s')
      (MATCHRM: match_regmap rm (absstate_get pc abs)),
      (match_states p v params) tt (State s v pc rm ms) (State s' vopt pc rm ms)
| lock_refl_state:
    forall s s' l rm ms v'
      (MATCHSTACK: (match_stack v params) s s'),
      (match_states p v params) tt (State s v' l rm ms) (State s' v' l rm ms)
| lock_refl_final:
    forall retval ms,
      (match_states p v params) tt (Final retval ms) (Final retval ms).

Lemma lock_refl:
  forall s p v params,
    (match_states p v params) tt s s.
Proof.
  intros. destruct s.
  eapply lock_refl_state. apply match_stack_same.
  constructor.
Qed.

(** * Code preservation *)
(* Code is preserved by the optimization *)
Lemma code_preserved:
  forall v params vopt i pc abs,
    constant_propagation_version v params = OK vopt ->
    kildall_constprop_analysis (ver_code v) params (ver_entry v) = Some abs ->
    (ver_code v) # pc = Some i ->
    (ver_code vopt) # pc = Some (transf_instr abs pc i).
Proof.
  intros. unfold constant_propagation_version in H. repeat do_ok. inv H0. simpl.
  rewrite PTree.gmap. unfold option_map. rewrite H1. auto.
Qed.

Ltac code_preserved:=
  match goal with
  | [ H: (ver_code ?v)#?pc = Some ?i |- _ ] => eapply code_preserved in H; eauto; try unfold transf_instr in H
  end.

(** * Order and index of the simulation  *)
Inductive order : unit -> unit -> Prop := .

Lemma wfounded:
  well_founded order.
Proof.
  unfold well_founded. intros. destruct a. constructor. intros. inv H.
Qed.  

(** * Preservation of deopt conditions  *)
Lemma deopt_cond_preserved_refl:
  forall s v pc rm ms s' p fidoptim vopt next synth newver la newrm params v',
    deopt_conditions p (State s v' pc rm ms) next synth newver la newrm ->
    match_stack v params s s' ->
    deopt_conditions (set_version p fidoptim vopt) (State s' v' pc rm ms) next synth newver la newrm.
Proof.
  intros s v pc rm ms s' p fidoptim vopt next synth newver la newrm params v' COND MS. inv COND.    
  eapply synth_frame_unchanged with (f:=fidoptim) (v:=vopt) in SYNTH.
  econstructor; eauto.
  erewrite <- base_version_unchanged. auto.
Qed.

Lemma deopt_cond_preserved_match:
  forall p s v pc rm ms next synth newver la newrm s' vopt abs params fidoptim,
    deopt_conditions p (State s v pc rm ms) next synth newver la newrm ->
    constant_propagation_version v params = OK vopt ->
    kildall_constprop_analysis (ver_code v) params (ver_entry v) = Some abs ->
    match_regmap rm (absstate_get pc abs) ->
    deopt_conditions (set_version p fidoptim vopt) (State s' vopt pc rm ms) next synth newver la newrm.
Proof.
  intros p s v pc rm ms next synth newver la newrm s' vopt abs params fidoptim COND CONSPROP KILDALL MRM.
  inv COND. eapply synth_frame_unchanged with (f:=fidoptim) (v:=vopt) in SYNTH.
  econstructor.
  - code_preserved. simpl in CODE. eauto.
  - rewrite <- base_version_unchanged. auto.
  - eapply strength_reduction_transf_vm_correct.
    eapply transf_vm_correct; eauto.
  - eauto.
Qed.

Lemma deopt_cond_preserved:
  forall p v fidoptim vopt params s s' next synth newver la newrm i
    (COND: deopt_conditions p s next synth newver la newrm)
    (CONSTPROP: constant_propagation_version v params = OK vopt)
    (MATCH: (match_states p v params) i s s'),
    deopt_conditions (set_version p fidoptim vopt) s' next synth newver la newrm.
Proof.
  intros p v fidoptim vopt params s s' next synth newver la newrm i COND CONSTPROP MATCH.
  inv MATCH.
  - rewrite CST_PROP in CONSTPROP. inv CONSTPROP. eapply deopt_cond_preserved_match; eauto.
  - eapply deopt_cond_preserved_refl; eauto.
  - inv COND.
Qed.

(** * Lowered forward diagram  *)
Lemma lowered_fwd:
  forall s1 s2 p t s1' fidoptim f vopt
    (MATCH: (match_states p (current_version f) (fn_params f) tt) s1 s2)
    (CST : constant_propagation_version (current_version f) (fn_params f) = OK vopt)
    (FINDF : find_function fidoptim p = Some f)
    (STEP: lowered_step p s1 t s1'),
  exists s2', lowered_step (set_version p fidoptim vopt) s2 t s2' /\ (match_states p (current_version f) (fn_params f) tt) s1' s2'.
Proof.
  intros s1 s2 p t s1' fidoptim f vopt MATCH CST FINDF STEP.
  assert (CSTV: constant_propagation_version (current_version f) (fn_params f) = OK vopt) by auto.
  unfold constant_propagation_version in CST. repeat do_ok. rename HDO0 into KILDALL.
  inv MATCH.
  -                             (* match *)
    (* In that case we relate the execution of the optimized version to the execution of the source *)
    rewrite KILDALL in ANALYSIS. inv ANALYSIS.
    inv STEP.
    + exists (State s' vopt next rm ms). split. (* Nop *)
      * eapply exec_Nop; eauto. code_preserved. simpl in CODE. eauto.
      * eapply lock_match; eauto. eapply analyze_correct; eauto. simpl; auto.
        unfold constprop_transf. rewrite CODE. auto.
    + exists (State s' vopt next (rm # reg <- v) ms). split. (* Op *)
      * code_preserved.
        assert (R: exists expr', replace_ops (absstate_get pc abs) (Op expr reg next) = Op expr' reg next /\ specIR.eval_expr expr' rm v).
        { eapply replace_expr_correct in EVAL; eauto.
          exists (transf_expr (replace_op (absstate_get pc abs)) expr). simpl. split; auto. }
        destruct R as [expr' [REPLACE EVAL']]. rewrite REPLACE in CODE. eapply exec_Op. simpl in CODE.
        eapply CODE. apply strength_reduction_correct. apply simpl_expr_correct in EVAL'. auto.
      * econstructor; eauto. eapply analyze_correct; eauto. simpl; auto.
        unfold constprop_transf. rewrite CODE. apply match_regmap_update; auto.
        eapply eval_expr_abs_correct; eauto.
    + exists (State s' vopt next newrm ms). split. (* MoveList *)
      * code_preserved.
        assert (R: exists vm', replace_ops (absstate_get pc abs) (Move ml next) = Move vm' next /\ specIR.update_movelist vm' rm newrm).
        { eapply transf_ml_correct in UPDATE; eauto.
          exists (transf_ml (transf_expr (replace_op (absstate_get pc abs))) ml). simpl. split; auto. }
        destruct R as [vm' [REPLACE EVAL']]. rewrite REPLACE in CODE. eapply exec_Move. simpl in CODE. eapply CODE.
        apply strength_reduction_transf_ml_correct. auto.
      * econstructor; eauto. eapply analyze_correct; eauto. simpl; auto.
        unfold constprop_transf. rewrite CODE.
        eapply match_regmap_update_movelist; eauto.
    + exists (State s' vopt (pc_cond v iftrue iffalse) rm ms). split. (* Cond *)
      * code_preserved.
        assert (R: exists expr', replace_ops (absstate_get pc abs) (Cond expr iftrue iffalse) = Cond expr' iftrue iffalse /\ specIR.eval_expr expr' rm v).
        { eapply replace_expr_correct in EVAL; eauto.
          exists (transf_expr (replace_op (absstate_get pc abs)) expr). simpl. split; auto. }
        destruct R as [expr' [REPLACE EVAL']]. rewrite REPLACE in CODE. simpl in CODE.
        { destruct (simpl_expr expr') as [binexpr|[ | | ]] eqn:SIMPL.
          - eapply exec_Cond; eauto. rewrite <- SIMPL; auto. apply strength_reduction_correct.
            rewrite <- simpl_expr_correct. auto.
          - eapply exec_Cond; eauto. rewrite <- SIMPL; auto. apply strength_reduction_correct.
            rewrite <- simpl_expr_correct. auto.
          - eapply exec_Cond; eauto. rewrite <- SIMPL; auto. apply strength_reduction_correct.
            rewrite <- simpl_expr_correct; auto.
          - destruct o.
            + eapply exec_Cond; eauto. rewrite <- SIMPL. apply strength_reduction_correct.
              rewrite <- simpl_expr_correct. auto.
            + destruct v0. destruct z.
              * simpl in CODE. apply simpl_expr_correct in EVAL'. rewrite SIMPL in EVAL'.
                inv EVAL'. inv EVAL0. inv EVALV. inv EVAL1. eapply exec_Nop; eauto.
              * simpl in CODE. apply simpl_expr_correct in EVAL'. rewrite SIMPL in EVAL'.
                inv EVAL'. inv EVAL0. inv EVALV. inv EVAL1. eapply exec_Nop; eauto.
              * simpl in CODE. apply simpl_expr_correct in EVAL'. rewrite SIMPL in EVAL'.
                inv EVAL'. inv EVAL0. inv EVALV. inv EVAL1. eapply exec_Nop; eauto. }
      * econstructor; eauto. eapply analyze_correct; eauto. simpl; auto.
        destruct v; simpl; destruct z; auto. 
        unfold constprop_transf. rewrite CODE. auto.
    + { poseq_destr fid fidoptim. (* Call *)
        - (* calling the optimized function *)
          exists (State (Stackframe retreg vopt next rm :: s') vopt (ver_entry vopt) newrm ms).
          rewrite FINDF0 in FINDF. inv FINDF.
          split.
          + code_preserved. simpl in CODE.
            eapply exec_Call. apply CODE.
            eapply find_function_same; eauto.
            rewrite CSTV in CST_PROP. inv CST_PROP.
            apply current_version_same.
            eapply strength_reduction_evalist_correct; eauto.
            eapply replace_expr_evalist_correct; eauto.
            simpl. auto.
          + assert (H0: ver_entry vopt = ver_entry (current_version f)).
            { rewrite CSTV in CST_PROP. inv CST_PROP. simpl. auto. } rewrite H0. 
            eapply lock_match; eauto. constructor; auto.
            econstructor; eauto.
            intros. eapply analyze_correct; eauto; simpl; auto.
            unfold constprop_transf. rewrite CODE.
            eapply match_regmap_update; eauto. constructor.
            eapply analyze_init; eauto.            
        - (* calling another function *)
          exists (State (Stackframe retreg vopt next rm :: s') (current_version func) (ver_entry (current_version func)) newrm ms). split.
          + code_preserved. simpl in CODE.
            eapply exec_Call; eauto. erewrite <- find_function_unchanged; eauto.
            apply strength_reduction_evalist_correct.
            apply replace_expr_evalist_correct; auto.
          + econstructor; eauto; constructor; auto. econstructor; eauto.
            intros. eapply analyze_correct; eauto; simpl; auto.
            unfold constprop_transf. rewrite CODE.
            eapply match_regmap_update; eauto. constructor. }
    + destruct s' as [|sf s0']. inv MATCHSTACK. (* Return *)
      assert (R: exists retex', (replace_ops (absstate_get pc abs) (IReturn retex)) = IReturn retex' /\ specIR.eval_expr retex' rm retval).
      { eapply replace_expr_correct in EVAL; eauto.
        exists (transf_expr (replace_op (absstate_get pc abs)) retex). split; auto. }
      destruct R as [retex' [REPLACE EVAL']]. inv MATCHSTACK. inv MSF.
      * { exists (State s0' fprev next (rmprev # retreg <- retval) ms). split.
          * code_preserved.
            rewrite REPLACE in CODE. simpl in CODE.
            eapply exec_Return; eauto. eapply strength_reduction_correct; eauto.
          * constructor; auto. }
      * { exists (State s0' vopt0 next (rmprev # retreg <- retval) ms). split.
          * code_preserved. rewrite KILDALL in H5. inv H5.
            rewrite REPLACE in CODE. simpl in CODE.
            rewrite CST_PROP in H4. inv H4.
            eapply exec_Return; eauto. eapply strength_reduction_correct; eauto.
          * eapply lock_match; eauto. }
    + exists (Final retval ms). split. 
      code_preserved. inv MATCHSTACK.
      assert (R: exists retex', (replace_ops (absstate_get pc abs) (IReturn rex)) = IReturn retex' /\ specIR.eval_expr retex' rm retval).
      { eapply replace_expr_correct in EVAL; eauto.
        exists (transf_expr (replace_op (absstate_get pc abs)) rex). split; auto. }
      destruct R as [retex' [REPLACE EVAL']]. rewrite REPLACE in CODE. simpl in CODE.
      eapply exec_Return_Final; eauto. eapply strength_reduction_correct; eauto.
      constructor.
    + exists (State s' vopt next rm ms). split. (* Printexpr *)
      * code_preserved.
        assert (R: exists expr', replace_ops (absstate_get pc abs) (Printexpr expr next) = Printexpr expr' next /\ specIR.eval_expr expr' rm printval).
        { eapply replace_expr_correct in EVAL; eauto.
          exists (transf_expr (replace_op (absstate_get pc abs)) expr). simpl. split; auto. }
        destruct R as [expr' [REPLACE EVAL']].
        rewrite REPLACE in CODE. simpl in CODE. eapply exec_Printexpr; eauto.
        apply strength_reduction_correct. auto.
      * econstructor; eauto.
        eapply analyze_correct; eauto.
        simpl; auto. unfold constprop_transf. rewrite CODE. auto.
    + exists (State s' vopt next rm ms). split. (* Printstring *)
      * constructor; auto. code_preserved.
      * eapply lock_match; eauto. eapply analyze_correct; eauto. simpl; auto.
        unfold constprop_transf. rewrite CODE. auto.
    + exists (State s' vopt next rm newms). split. (* Store *)
      * assert (R: exists expr1', exists expr2', (replace_ops (absstate_get pc abs) (Store expr1 expr2 next)) = Store expr1' expr2' next /\ specIR.eval_expr expr1' rm val /\ specIR.eval_expr expr2' rm  addr).
        { eapply replace_expr_correct in EVAL_ST; eauto. eapply replace_expr_correct in EVAL_AD; eauto.
          exists (transf_expr (replace_op (absstate_get pc abs)) expr1).
          exists (transf_expr (replace_op (absstate_get pc abs)) expr2).
          split; auto. }
        destruct R as [expr1' [expr2' [REPLACE [EVAL1 EVAL2]]]].
        code_preserved. rewrite REPLACE in CODE. simpl in CODE.
        eapply exec_Store; eauto; eapply strength_reduction_correct; eauto.
      * econstructor; eauto. eapply analyze_correct; eauto. simpl; auto.
        unfold constprop_transf. rewrite CODE. auto.      
    + exists (State s' vopt next (rm # reg <- val) ms). split. (* Load *)
      * code_preserved.
        assert (R: exists expr', (replace_ops (absstate_get pc abs) (Load expr reg next)) = Load expr' reg next /\ specIR.eval_expr expr' rm addr).
        { eapply replace_expr_correct in EVAL; eauto.
          exists (transf_expr (replace_op (absstate_get pc abs)) expr). simpl; auto. }
        destruct R as [expr' [REPLACE EVAL']]. rewrite REPLACE in CODE; simpl in CODE.
        eapply exec_Load; eauto. eapply strength_reduction_correct; eauto.
      * econstructor; eauto. eapply analyze_correct; eauto; simpl; auto.
        unfold constprop_transf. rewrite CODE.
        apply match_regmap_update; auto. constructor.
    + exists (State s' vopt next rm ms). split. (* Assume holds *)
      * code_preserved.
        assert (R: exists le', (replace_ops (absstate_get pc abs) (Assume le tgt vm sl next)) = Assume le' tgt (transf_vm (transf_expr (replace_op (absstate_get pc abs))) vm) sl next /\ specIR.eval_list_expr le' rm true).
        { eapply replace_expr_list_correct in ASSUME_TRUE; eauto.
          exists (transf_expr_list (replace_op (absstate_get pc abs)) le). destruct tgt. simpl; auto. }
        destruct R as [le' [REPLACE EVAL]]. rewrite REPLACE in CODE. simpl in CODE.
        { destruct le' as [| e' le']; simpl in CODE.
          - eapply exec_Nop; eauto. destruct tgt. simpl in CODE. eauto.
          - destruct tgt. eapply exec_Assume_holds; eauto.
            apply strength_reduction_list_correct in EVAL. simpl in EVAL. auto. }
      * econstructor; eauto. eapply analyze_correct; eauto. simpl; auto.
        unfold constprop_transf. rewrite CODE. destruct tgt. apply match_regmap_assert; auto.
    + eapply match_synth in SYNTH; try eapply CONST_PROP; eauto. (* Assume fails *)
      destruct SYNTH as [synthopt [SYN MATCH]].
      exists (State (synthopt ++ s') newver la newrm ms). split.
      * assert (R: exists le', (replace_ops (absstate_get pc abs) (Assume le (fa,la) vm sl next)) = Assume le' (fa,la) (transf_vm (transf_expr (replace_op (absstate_get pc abs))) vm) sl next /\ specIR.eval_list_expr le' rm false).
        { eapply replace_expr_list_correct in ASSUME_FAILS; eauto.
          exists (transf_expr_list (replace_op (absstate_get pc abs)) le). simpl; split; auto. }
        destruct R as [le' [REPLACE EVAL]]. code_preserved. rewrite REPLACE in CODE. simpl in CODE.
        destruct le' as [|e' le']. inv EVAL.
        eapply exec_Assume_fails; eauto.
        ** apply strength_reduction_list_correct in EVAL. simpl in EVAL. auto.
        ** rewrite <- base_version_unchanged. auto.
        ** apply strength_reduction_transf_vm_correct.
           apply transf_vm_correct. auto. auto.
        ** rewrite CSTV in CST_PROP. inv CST_PROP. auto.
      * econstructor; eauto. apply app_match; auto.      
      
  -                             (* refl *)
    (* Here, both programs are in the same state (except parts of the stackframe) *)
    inv STEP.
    + exists (State s' v' next rm ms). split. eapply exec_Nop; eauto. constructor; auto.
    + exists (State s' v' next (rm # reg <- v) ms). split. eapply exec_Op; eauto. constructor; auto.
    + exists (State s' v' next newrm ms). split. eapply exec_Move; eauto. constructor; auto.
    + exists (State s' v' (pc_cond v iftrue iffalse) rm ms). split. eapply exec_Cond; eauto. constructor; auto.
    + {
        poseq_destr fid fidoptim.
        - (* calling the optimized function *)
          set (vopt := {| ver_code := PTree.map (transf_instr a) (ver_code (current_version f)); ver_entry := ver_entry (current_version f) |}).
          rewrite FINDF0 in FINDF. inv FINDF.
          exists (State (Stackframe retreg v' next rm::s') vopt (ver_entry (current_version f)) newrm ms). split.
          + assert (ver_entry vopt = ver_entry (current_version f)).
            { unfold vopt. simpl. auto. } rewrite <- H.
            eapply exec_Call. apply CODE.
            eapply find_function_same; eauto.
            apply current_version_same.
            apply EVALL. simpl. auto.
          + eapply lock_match; eauto. constructor; auto.
            constructor; auto. eapply analyze_init; eauto.
        - (* calling another function *)
          exists (State (Stackframe retreg v' next rm ::s') (current_version func) (ver_entry (current_version func)) newrm ms).
          split.
          + eapply exec_Call; eauto. erewrite <- find_function_unchanged; eauto.
          + constructor; auto. constructor; auto. constructor. }
    + destruct s' as [|sf' s']; inv MATCHSTACK. inv MSF.
      * exists (State s' fprev next (rmprev # retreg <- retval) ms). split. 
        eapply exec_Return; eauto. constructor; auto.
      * exists (State s' vopt next (rmprev # retreg <- retval) ms). split.
        eapply exec_Return; eauto. eapply lock_match; eauto.
    + exists (Final retval ms). split. inv MATCHSTACK. eapply exec_Return_Final; eauto. constructor. 
    + exists (State s' v' next rm ms). split. eapply exec_Printexpr; eauto. constructor; auto.
    + exists (State s' v' next rm ms). split. eapply exec_Printstring; auto. constructor; auto.
    + exists (State s' v' next rm newms). split. eapply exec_Store; eauto. constructor; auto.
    + exists (State s' v' next (rm # reg <- val) ms). split. eapply exec_Load; eauto. constructor; auto.
    + exists (State s' v' next rm ms). split. eapply exec_Assume_holds; eauto. constructor; auto.
    + eapply match_synth in SYNTH; eauto.
      * destruct SYNTH as [synthopt [SYN MATCH]].
        exists (State (synthopt ++ s') newver la newrm ms). split. 
        eapply exec_Assume_fails with (synth:=synthopt); eauto.
        rewrite <- base_version_unchanged. auto.
        constructor; auto. apply app_match; auto.
  - inv STEP.                   (* final *)
Qed.

(** * Loud Forward simulation  *)
Lemma loud_fwd:
  forall s1 s2 p t s1' fidoptim f vopt
    (MATCH: (match_states p (current_version f) (fn_params f) tt) s1 s2)
    (CST : constant_propagation_version (current_version f) (fn_params f) = OK vopt)
    (FINDF : find_function fidoptim p = Some f)
    (STEP: loud_step p s1 t s1'),
  exists s2', loud_step (set_version p fidoptim vopt) s2 t s2' /\ (match_states p (current_version f) (fn_params f) tt) s1' s2'.
Proof.
  intros s1 s2 p t s1' fidoptim f vopt MATCH CST FINDF STEP.
  assert (CSTV: constant_propagation_version (current_version f) (fn_params f) = OK vopt) by auto.
  unfold constant_propagation_version in CST. repeat do_ok. rename HDO0 into KILDALL.
  inv STEP.
  - eapply lowered_fwd in STEP0 as [s2' [STEP MATCH']]; eauto.
    exists s2'. split; auto. constructor; eauto.
  -                             (* Framestate Go_on *)
    eapply deopt_cond_preserved with (fidoptim:=fidoptim) in DEOPT_COND as COND_OPT; eauto.
    inv MATCH.
    +                           (* match *)
      rewrite ANALYSIS in KILDALL. inv KILDALL.
      exists (State s' vopt next rm ms). rewrite CST_PROP in CSTV. inv CSTV. split.
      * eapply loud_exec_Framestate_go_on; eauto.
      * inv DEOPT_COND. eapply lock_match; eauto. eapply analyze_correct; eauto.
        simpl. left. auto. unfold constprop_transf. rewrite CODE. auto.
    +                           (* refl *)
      exists (State s' f0 next rm ms). split.
      * eapply loud_exec_Framestate_go_on; eauto.
      * eapply lock_refl_state; eauto.
  -                             (* Framestate_Deopt *)
    eapply deopt_cond_preserved with (fidoptim:=fidoptim) in DEOPT_COND as COND_OPT; eauto.
    inv MATCH.
    +                           (* match *)
      rewrite ANALYSIS in KILDALL. inv KILDALL.
      exists (State (synth++s') newver la newrm ms). rewrite CST_PROP in CSTV. inv CSTV. split.
      * eapply loud_exec_Framestate_deopt; eauto.
      * inv DEOPT_COND. eapply lock_refl_state; eauto. apply match_app. auto.
    +                           (* refl *)
      exists (State (synth++s') newver la newrm ms). split.
      * eapply loud_exec_Framestate_deopt; eauto.
      * eapply lock_refl_state; auto. apply match_app. auto.
Qed.
 

(** * Backward Simulation *)
Theorem constprop_correct:
  forall p fidoptim newp,
    constant_propagation fidoptim p = OK (newp) ->
    backward_internal_simulation p newp.
Proof.
  intros p fidoptim newp CST. apply fwd_loud.
  unfold constant_propagation in CST. repeat do_ok. rename HDO1 into FINDF. rename HDO0 into CST.
  apply Forward_internal_loud_simulation with (fsim_index:=unit) (fsim_order:=order) (fsim_match_states:=match_states p (current_version f) (fn_params f)).
  - apply wfounded.
  - assert (CSTV: constant_propagation_version (current_version f) (fn_params f) = OK v) by auto.
    unfold constant_propagation_version in CST. repeat do_ok. rename HDO0 into KILDALL.
    unfold reflexive_forge. intros synchro stack r1 s1 ms FORGE.
    destruct synchro; simpl in FORGE; repeat do_ok; simpl.
    + poseq_destr f0 fidoptim.  (* is the called function the optimized one? *)
      * erewrite find_function_same; eauto. simpl. rewrite HDO0. simpl. repeat (esplit; eauto).
        simpl. rewrite current_version_same. rewrite FINDF in HDO1. inv HDO1.
        eapply lock_match; eauto. apply match_stack_same. eapply analyze_init; eauto.
        apply init_regs_correct in HDO0. eauto.
      * erewrite <- find_function_unchanged; eauto. rewrite HDO1. simpl. rewrite HDO0. simpl.
        repeat (esplit; eauto). constructor. apply match_stack_same.
    + destruct stack; try destruct s; inv FORGE.
      * repeat (esplit; eauto). constructor.
      * repeat (esplit; eauto). simpl. constructor. apply match_stack_same.
    + destruct d. repeat do_ok. simpl. rewrite <- base_version_unchanged. rewrite HDO0. simpl.
      repeat (esplit; eauto). simpl. constructor. apply match_stack_same.
    + inv FORGE. exists r1. exists s1. split; auto. exists tt. destruct r1; constructor. apply match_stack_same.
  - intros i s1 s2 r H H0. inv H0. inv H. constructor.
  - intros s1 t s1' STEP i s2 MATCH. exists tt. destruct i.
    eapply loud_fwd in STEP as [s2' [STEP' MATCH']]; eauto.
    exists s2'. split.
    + left. apply plus_one. auto.
    + apply MATCH'.
Qed.
