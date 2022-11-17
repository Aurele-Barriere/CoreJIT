(* Correctness of the Inlining pass *)
(* A pass of the dynamic optimizer *)

Require Export specIR.
Require Export ir_properties.
Require Export internal_simulations.
Require Import Coq.MSets.MSetPositive.
Require Export inlining.

(* Expressions used in instructions *)
Definition expr_in_instr (i:instruction): list expr :=
  match i with
  | Nop oh l => nil
  | Op e r l => e::nil
  | Move vm next => List.map snd vm
  | Call f le r l => le
  | IReturn e => e::nil
  | Cond e l1 l2 => e::nil
  | Store e1 e2 l => e1::e2::nil
  | Load e r l => e::nil
  | Printexpr e l => e::nil
  | Printstring s l => nil
  | Assume le tgt vm sl l => le  (* vm and sl will be tied to their environment differently *)
  | Framestate tgt vm sl l => nil
  | Fail s => nil
  end.


(** * Fold Max Properties  *)
(* Fold max is used to get the shift we apply to the callee environment *)
Lemma fold_max_init:
  forall P l f s,
    (s <= fold_left (fun (a : positive) (p : P) => Pos.max a (f p)) l s)%positive.
Proof.
  intros. generalize dependent s. induction l; intros.
  - simpl. apply Pos.le_refl.
  - simpl. specialize (IHl (Pos.max s (f a))).
    eapply Pos.le_trans. apply Pos.le_max_l. eauto.
Qed.

Lemma fold_max_init_2:
  forall P l f s1 s2,
    (s1 <= s2)%positive ->
    (fold_left (fun (a : positive) (p : P) => Pos.max a (f p)) l s1 <= fold_left (fun (a : positive) (p : P) => Pos.max a (f p)) l s2)%positive.
Proof.
  intros. generalize dependent s1. generalize dependent s2. induction l; intros.
  - simpl. auto.
  - simpl. apply IHl.
    apply Pos.max_le_compat_r. auto.
Qed.

Lemma fold_max:
  forall P l f x,
    In x l ->
    (f x <= fold_left (fun (a : positive) (p : P) => Pos.max a (f p)) l xH)%positive.
Proof.
  intros. induction l; inv H.
  - simpl. eapply Pos.le_trans. apply Pos.le_max_r. apply fold_max_init.
  - apply IHl in H0. simpl.
    eapply Pos.le_trans. eauto. apply fold_max_init_2. apply Pos.le_max_l.
Qed.

(* More general theorem *)
Lemma fold_max_cons:
  forall P l f x s,
    fold_left (fun (a : positive) (p : P) => Pos.max a (f p)) (x::l) s =
    Pos.max (f x) (fold_left (fun (a : positive) (p : P) => Pos.max a (f p)) l s).
Proof.
  intros. simpl. generalize dependent s. induction l; intros.
  - simpl. apply Pos.max_comm.
  - simpl.
    replace (Pos.max (Pos.max s (f x)) (f a)) with (Pos.max (Pos.max s (f a)) (f x)).
    apply IHl. rewrite <- Pos.max_assoc. rewrite Pos.max_comm with (n:=f a). rewrite Pos.max_assoc. auto.
Qed.



(** * Regmap Relation: Callee environment  *)
(* When executing the inlined part, the regmap should correspond to the original one used, but shifted *)
(* The optimized regmap can still be more defined *)
Definition shift_rm (sr:shift) (rm srm:reg_map) : Prop :=
  forall (r:reg) (v:value), rm # r = Some v ->
                       srm # (shift_reg sr r) = Some v.

Lemma shift_rm_insert:
  forall sr rm srm r v,
    shift_rm sr rm srm ->
    shift_rm sr (rm # r <- v) (srm # (shift_reg sr r) <- v).
Proof.
  intros sr rm srm r v H. unfold shift_rm in *. intros r'.
  poseq_destr r r'.
  - repeat rewrite PTree.gss. auto.
  - rewrite PTree.gso; auto. rewrite PTree.gso. apply H.
    unfold shift_reg. intros H1. apply Pos.add_reg_r in H1. auto.
Qed.

Lemma shift_rm_empty:
  forall sr rm,
    shift_rm sr empty_regmap rm.
Proof.
  intros. unfold shift_rm. intros. rewrite PTree.gempty in H. inv H.
Qed.

(** * Regmap Relation: Caller environment  *)
(* A register belongs to the caller environment if its lesser than the shift of registers *)
Definition caller_reg (sr:shift) (r:reg) : Prop := Pos.le r sr.

(* The 2 regmap agree on the caller registers *)
Definition rm_agree (sr:shift) (rm rm_opt:reg_map) : Prop :=
  forall r:reg, caller_reg sr r -> rm # r = rm_opt # r.

(* The same regmap always agree on the caller registers *)
Lemma rm_agree_refl:
  forall sr rm,
    rm_agree sr rm rm.
Proof.
  intros sr rm. unfold rm_agree. intros r H. auto.
Qed.

Lemma rm_agree_sym:
  forall sr rm1 rm2,
    rm_agree sr rm1 rm2 ->
    rm_agree sr rm2 rm1.
Proof.
  unfold rm_agree. intros sr rm1 rm2 H r CALLER. symmetry. apply H. auto.
Qed.

Lemma rm_agree_trans:
  forall sr rm1 rm2 rm3,
    rm_agree sr rm1 rm2 ->
    rm_agree sr rm2 rm3 ->
    rm_agree sr rm1 rm3.
Proof.
  unfold rm_agree. intros. rewrite H; auto.
Qed.

(* updating the rm on both sides *)
Lemma rm_agree_insert:
  forall sr rm rm_opt reg v,
    rm_agree sr rm rm_opt ->
    rm_agree sr (rm # reg <- v) (rm_opt # reg <- v).
Proof.
  intros. unfold rm_agree in *.
  intros r. poseq_destr r reg.
  - rewrite PTree.gss. rewrite PTree.gss. intros. auto.
  - rewrite PTree.gso; auto. rewrite PTree.gso; auto.
Qed.

(* A shifted reg does not belong to the caller environment *)
Lemma shift_not_caller:
  forall r sr,
    caller_reg sr (shift_reg sr r) -> False.
Proof.
  intros. unfold shift_reg in H. unfold caller_reg in H.
  rewrite Pos.add_comm in H.
  assert ((sr < sr + r)%positive) by apply Pos.lt_add_r.
  apply Pos.lt_nle in H0. apply H0 in H. auto.
Qed.

(* updating the callee part of the regmap does not change the caller part *)
Lemma rm_agree_shift_insert:
  forall sr rm rm_opt reg v,
    rm_agree sr rm rm_opt ->
    rm_agree sr rm (rm_opt # (shift_reg sr reg) <- v).
Proof.
  intros sr rm rm_opt reg v AGREE. unfold rm_agree in *. intros r CALLER.
  rewrite PTree.gso. apply AGREE. auto.
  poseq_destr r (shift_reg sr reg); auto.
  apply shift_not_caller in CALLER. exfalso. apply CALLER.
Qed.

(** * Labels of the caller environment  *)
(* A label belongs to the caller environment if its lesser than the shift of labels *)
Definition caller_lbl (sl:shift) (l:label) : Prop := Pos.le l sl.

(* If a label corresponds to some instruction in the caller code, it is a caller label *)
Lemma is_caller_lbl:
  forall code_caller sl l i,
    sl = max_lbl_code (code_caller) ->
    (code_caller) # l = Some i ->
    caller_lbl sl l.
Proof.
  intros caller sl l i SL CODE.
  unfold max_lbl_code, max_label in SL.
  apply max_pos_correct in CODE. rewrite <- SL in CODE. unfold caller_lbl. auto.
Qed.

(** * Instructions of the caller environment  *)
(* An operand that only uses caller registers *)
Definition caller_op (sr:shift) (o:op) : Prop :=
  match o with
  | Cst v => True
  | Reg r => caller_reg sr r
  end.

(* An expression that only uses caller registers *)
Definition caller_expr (sr:shift) (e:expr) : Prop :=
  match e with
  | Binexpr b o1 o2 => caller_op sr o1 /\ caller_op sr o2
  | Unexpr u o => caller_op sr o
  end.

Inductive caller_list_expr (sr:shift) : (list expr) -> Prop :=
| caller_nil: caller_list_expr sr nil
| caller_cons: forall e l',
    caller_expr sr e ->
    caller_list_expr sr l' ->
    caller_list_expr sr (e::l').

Inductive caller_movelist (sr:shift): movelist -> Prop :=
| caller_mlnil : caller_movelist sr nil
| caller_mlcons: forall e r l',
    caller_expr sr e ->
    caller_reg sr r ->
    caller_movelist sr l' ->
    caller_movelist sr ((r,e)::l').

Inductive caller_varmap (sr:shift): varmap -> Prop :=
| caller_vmnil : caller_varmap sr nil
| caller_vmcons: forall r e l',
    caller_expr sr e ->
    caller_varmap sr l' ->
    caller_varmap sr ((r,e)::l').
(* The register to reconstruct is not part of this environment *)

Definition caller_synth_frame (sr:shift) (sy:synth_frame):  Prop :=
  caller_varmap sr (snd sy).
(* Synthesized Return register is not part of this environment *)

Inductive caller_synth_list (sr:shift) : list synth_frame -> Prop :=
| caller_synil: caller_synth_list sr nil
| caller_sycons: forall sy l,
    caller_synth_frame sr sy ->
    caller_synth_list sr l ->
    caller_synth_list sr (sy::l).


(* Forward direction *)
(* In the caller environment, under regmap agreement, expressions evaluate to the same value *)
Lemma agree_expr:
  forall rm rm_opt sr e v,
    rm_agree sr rm rm_opt ->
    caller_expr sr e ->
    eval_expr e rm v ->
    eval_expr e rm_opt v.
Proof.
  intros rm rm_opt sr e v AGREE CALLER EVAL.
  inv EVAL.
  - inv EVAL0.
    inv EVALL; inv EVALR; constructor; (econstructor; eauto); constructor; auto; inv CALLER; simpl in H0; simpl in H;
      try apply AGREE in H0; try apply AGREE in H; try rewrite <- H0; try rewrite <- H; auto.
  - inv EVAL0. inv EVAL; constructor; (econstructor; eauto); constructor; auto.
    simpl in CALLER. apply AGREE in CALLER. rewrite <- CALLER. auto.
Qed.

(* Lists of expressions also evaluate to the same values *)
Lemma agree_list_expr:
  forall rm rm_opt sr l b,
    rm_agree sr rm rm_opt ->
    caller_list_expr sr l ->
    eval_list_expr l rm b ->
    eval_list_expr l rm_opt b.
Proof.
  intros rm rm_opt sr l b AGREE CALLER EVALL.
  induction CALLER.
  - inv EVALL. constructor.
  - inv EVALL.
    + constructor. eapply agree_expr; eauto.
    + econstructor; eauto. eapply agree_expr; eauto.
Qed.

(* Same for eval_list *)
Lemma agree_list:
  forall rm rm_opt sr l valist,
    rm_agree sr rm rm_opt ->
    caller_list_expr sr l ->
    eval_list l rm valist ->
    eval_list l rm_opt valist.
Proof.
  intros rm rm_opt sr l valist AGREE CALLER EVALL. generalize dependent valist.
  induction CALLER; intros.
  - inv EVALL. constructor.
  - inv EVALL.
    constructor. eapply agree_expr; eauto. apply IHCALLER. auto.
Qed.

Lemma agree_movelist:
  forall rm rm_opt sr ml newrm,
    rm_agree sr rm rm_opt ->
    caller_movelist sr ml ->
    update_movelist ml rm newrm ->
    exists newrm_opt,
      update_movelist ml rm_opt newrm_opt /\
      rm_agree sr newrm newrm_opt.
Proof.
  unfold update_movelist. intros. generalize dependent newrm. induction ml; intros.
  - inv H1. exists rm_opt. split; auto. constructor.
  - inv H1. inv H0. apply IHml in UPDATE as [newrmopt [UPDATE AGREE]]; auto.
    exists (newrmopt # r <- v). split.
    + constructor; auto. eapply agree_expr; eauto.
    + apply rm_agree_insert. auto.
Qed.

(* True for the suffix of a list *)
Lemma agree_list_sub:
  forall rm rm_opt sr prel l valist,
    rm_agree sr rm rm_opt ->
    caller_list_expr sr (prel ++ l) ->
    eval_list l rm valist ->
    eval_list l rm_opt valist.
Proof.
  intros rm rm_opt sr prel l valist AGREE CALLER EVALL.
  induction prel; simpl in CALLER.
  - eapply agree_list; eauto.
  - inv CALLER. apply IHprel. auto.
Qed.

(* updating the rm with a varmap on both sides *)
Lemma rm_agree_regmap:
  forall sr rm rm_opt vm newrm,
    rm_agree sr rm rm_opt ->
    update_regmap vm rm newrm ->
    caller_varmap sr vm ->
    update_regmap vm rm_opt newrm.
Proof.
  intros sr rm rm_opt vm. induction vm; intros.
  - inv H0. constructor.
  - inv H0. inv H1. apply IHvm in UPDATE; auto.
    constructor; auto. eapply agree_expr; eauto.
Qed.

Lemma rm_agree_synth:
  forall sr rm rm_opt syl stk p,
    rm_agree sr rm rm_opt ->
    synthesize_frame p rm syl stk ->
    caller_synth_list sr syl ->
    synthesize_frame p rm_opt syl stk.
Proof.
  intros. generalize dependent stk. induction syl; intros.
  - inv H0. constructor.
  - inv H1. inv H0. apply IHsyl in SYNTH; auto.
    constructor; auto. eapply rm_agree_regmap; eauto.
Qed.

(* Backward direction *)
(* In the caller environment, under regmap agreement, expressions evaluate to the same value *)
Lemma agree_opb:
  forall rm rm_opt sr o v,
    rm_agree sr rm rm_opt ->
    caller_op sr o ->
    eval_op o rm_opt v ->
    eval_op o rm v.
Proof.
  intros rm rm_opt sr o v H H0 H1. inv H1; try constructor.
  unfold caller_op in H0. unfold rm_agree in H. apply H in H0. rewrite H0. auto.
Qed.

Lemma agree_exprb:
  forall rm rm_opt sr e v,
    rm_agree sr rm rm_opt ->
    caller_expr sr e ->
    eval_expr e rm_opt v ->
    eval_expr e rm v.
Proof.
  intros rm rm_opt sr e v AGREE CALLER EVAL.
  inv EVAL.
  - inv CALLER. inv EVAL0. eapply agree_opb in EVALL; eauto. eapply agree_opb in EVALR; eauto.
    constructor. econstructor; eauto.
  - simpl in CALLER. inv EVAL0. eapply agree_opb in EVAL; eauto. constructor.
    econstructor; eauto.
Qed.

(* Lists of expressions also evaluate to the same values *)
Lemma agree_list_exprb:
  forall rm rm_opt sr l b,
    rm_agree sr rm rm_opt ->
    caller_list_expr sr l ->
    eval_list_expr l rm_opt b ->
    eval_list_expr l rm b.
Proof.
  intros rm rm_opt sr l b AGREE CALLER EVALL.
  induction CALLER.
  - inv EVALL. constructor.
  - inv EVALL.
    + constructor. eapply agree_exprb; eauto.
    + econstructor; eauto. eapply agree_exprb; eauto.
Qed.

(* Same for eval_list *)
Lemma agree_listb:
  forall rm rm_opt sr l valist,
    rm_agree sr rm rm_opt ->
    caller_list_expr sr l ->
    eval_list l rm_opt valist ->
    eval_list l rm valist.
Proof.
  intros rm rm_opt sr l valist AGREE CALLER EVALL. generalize dependent valist.
  induction CALLER; intros.
  - inv EVALL. constructor.
  - inv EVALL.
    constructor. eapply agree_exprb; eauto. apply IHCALLER. auto.
Qed.

Lemma agree_movelistb:
  forall ml rm rm_opt newrmopt sr,
    rm_agree sr rm rm_opt ->
    caller_movelist sr ml ->
    update_movelist ml rm_opt newrmopt ->
    exists newrm,
      update_movelist ml rm newrm /\
      rm_agree sr newrm newrmopt.
Proof.
  intros. generalize dependent newrmopt. induction ml; intros.
  - inv H1. exists rm. split. constructor. auto.
  - inv H1. inv H0. eapply IHml in H6; eauto. destruct H6 as [newrm [UPDATE' AGREE]].
    exists (newrm # r <- v). split.
    + constructor. eapply agree_exprb; eauto. apply UPDATE'.
    + apply rm_agree_insert. auto.
Qed.

Lemma agree_regmapb:
  forall vm rm rm_opt newrm sr,
    rm_agree sr rm rm_opt ->
    caller_varmap sr vm ->
    update_regmap vm rm_opt newrm ->
    update_regmap vm rm newrm.
Proof.
  intros. generalize dependent newrm. induction vm; intros.
  - inv H1. constructor.
  - inv H1. inv H0. eapply IHvm in H5; eauto. constructor; auto.
    eapply agree_exprb; eauto.
Qed.

Lemma agree_synthb:
  forall sl rm rm_opt sr p stack,
    rm_agree sr rm rm_opt ->
    caller_synth_list sr sl ->
    synthesize_frame p rm_opt sl stack ->
    synthesize_frame p rm sl stack.
Proof.
  intros. generalize dependent stack. induction sl; intros.
  - inv H1. constructor.
  - inv H1. inv H0. eapply IHsl in H4; eauto. constructor; auto.
    eapply agree_regmapb; eauto.
Qed.

(* Finding caller expressions *)
Lemma caller_expr_max:
  forall e sr,
    (max_reg_expr e <= sr)%positive ->
    caller_expr sr e.
Proof.
  intros. destruct e; unfold caller_expr, caller_op, caller_reg. simpl in H. split.
  - destruct o; auto. simpl in H. apply Pos.max_lub_l in H. auto.
  - destruct o0; auto. simpl in H. apply Pos.max_lub_r in H. auto.
  - destruct o; auto.
Qed.

Lemma max_listexpr_cons:
  forall l a,
    (max_reg_listexpr l <= max_reg_listexpr (a :: l))%positive.
Proof.
  intros.
  induction l.
  - simpl. apply Pos.le_max_l.
  - unfold max_reg_listexpr. simpl. apply fold_max_init_2. repeat rewrite Pos.max_1_l.
    apply Pos.le_max_r.
Qed.

(* Finding caller list of expressions *)
Lemma caller_list_expr_max:
  forall l sr,
    (max_reg_listexpr l <= sr)%positive ->
    caller_list_expr sr l.
Proof.
  intros. induction l; constructor.
  - apply caller_expr_max. unfold max_reg_listexpr in *. simpl in H. eapply Pos.le_trans; eauto.
    eapply Pos.le_trans. 2: eapply fold_max_init. apply Pos.le_max_r.
  - apply IHl. eapply Pos.le_trans. eapply max_listexpr_cons. eauto.
Qed.

Lemma in_max_reg_listexpr:
  forall e l,
    In e l ->
    (max_reg_expr e <= max_reg_listexpr l)%positive.
Proof.
  intros. induction l; inv H.
  - unfold max_reg_listexpr. simpl. eapply Pos.le_trans. 2: apply fold_max_init. apply Pos.le_max_r.
  - apply IHl in H0. eapply Pos.le_trans. eauto. simpl. unfold max_reg_listexpr. apply max_listexpr_cons.
Qed.

Lemma max_reg_movelist_cons_1:
  forall reg e v,
    (reg <= max_reg_movelist ((reg, e) :: v))%positive.
Proof.
  intros. unfold max_reg_movelist.
  eapply Pos.le_trans. 2: eapply fold_max. 2: apply in_eq.
  simpl. apply Pos.le_max_l.
Qed.

Lemma max_reg_movelist_cons_2:
  forall reg e v,
    ((max_reg_expr e) <= max_reg_movelist ((reg, e) :: v))%positive.
Proof.
  intros. unfold max_reg_movelist.
  eapply Pos.le_trans. 2: eapply fold_max. 2: apply in_eq.
  simpl. apply Pos.le_max_r.
Qed.

Lemma max_reg_movelist_cons_3:
  forall reg e v,
    (max_reg_movelist v <= max_reg_movelist ((reg,e)::v))%positive.
Proof.
  intros. simpl. unfold max_reg_movelist. simpl. apply fold_max_init_2. apply Pos.le_max_l.
Qed.

Lemma max_reg_movelist_cons:
  forall reg e v,
    max_reg_movelist ((reg,e)::v) = Pos.max (Pos.max reg (max_reg_expr e)) (max_reg_movelist v).
Proof.
  intros. unfold max_reg_movelist. rewrite fold_max_cons. auto.
Qed.

Lemma max_reg_listexpr_cons:
  forall e v,
    max_reg_listexpr (e::v) = Pos.max (max_reg_expr e) (max_reg_listexpr v).
Proof.
  intros. unfold max_reg_listexpr. rewrite fold_max_cons. auto.
Qed.

Lemma max_reg_movelist_map:
  forall v,
    (max_reg_listexpr (map snd v) <= max_reg_movelist v)%positive.
Proof.
  intros. induction v. unfold max_reg_listexpr. unfold max_reg_movelist. simpl. apply Pos.le_refl.
  destruct a. rewrite max_reg_movelist_cons. simpl. rewrite max_reg_listexpr_cons.
  eapply Pos.le_trans. apply Pos.max_le_compat_r. apply Pos.le_max_r.
  apply Pos.max_le_compat_l. auto.
Qed.

(* Finding caller expressions in the code *)
Lemma in_max_reg:
  forall e i sr,
    In e (expr_in_instr i) ->
    (max_reg_instr i <= sr)%positive ->
    caller_expr sr e.
Proof.
  intros e i sr IN MAX. unfold max_reg_instr in MAX.
  destruct i; simpl in IN; try (solve [inv IN]). (* unfold caller_expr, caller_op, caller_reg. *)
  - destruct IN. 2:inv H. subst e0. apply Pos.max_lub_r in MAX. apply caller_expr_max; auto.
  - induction m. inv IN.
    destruct a as [reg expr]. simpl in IN. inv IN.
    + apply caller_expr_max. eapply Pos.le_trans; eauto. apply max_reg_movelist_cons_2.
    + apply IHm; auto. eapply Pos.le_trans; eauto.  apply max_reg_movelist_cons_3.
  - apply Pos.max_lub_r in MAX. apply in_max_reg_listexpr in IN.
    apply caller_expr_max. eapply Pos.le_trans; eauto.
  - destruct IN. 2:inv H. subst e0. apply caller_expr_max; auto.
  - destruct IN. 2:inv H. subst e0. apply caller_expr_max; auto.
  - destruct IN. subst e0. apply Pos.max_lub_l in MAX. apply caller_expr_max; auto.
    destruct H. subst e1. apply Pos.max_lub_r in MAX. apply caller_expr_max; auto. inv H.
  - destruct IN. 2:inv H. subst e0. apply Pos.max_lub_r in MAX. apply caller_expr_max; auto.
  - destruct IN. 2:inv H. subst e0. apply caller_expr_max; auto.
  - apply Pos.max_lub_l in MAX. apply Pos.max_lub_l in MAX. apply in_max_reg_listexpr in IN.
    apply caller_expr_max. eapply Pos.le_trans; eauto.
Qed.

(* Finding caller list of expressions in the code *)
Lemma list_in_max_reg:
  forall l i sr,
    l = (expr_in_instr i) ->
    (max_reg_instr i <= sr)%positive ->
    caller_list_expr sr l.
Proof.
  intros e i sr IN MAX. unfold max_reg_instr in MAX.
  destruct i; simpl in IN; try (solve [subst; constructor]). (* unfold caller_expr, caller_op, caller_reg. *)
  - subst. constructor. apply Pos.max_lub_r in MAX. apply caller_expr_max. auto. constructor.
  - apply caller_list_expr_max. subst. eapply Pos.le_trans. apply max_reg_movelist_map. auto.
  - subst. apply Pos.max_lub_r in MAX. apply caller_list_expr_max. auto.
  - subst. constructor. apply caller_expr_max. auto. constructor.
  - subst. constructor. apply caller_expr_max. auto. constructor.
  - subst. constructor. apply caller_expr_max. apply Pos.max_lub_l in MAX. auto.
    constructor. apply caller_expr_max. apply Pos.max_lub_r in MAX. auto. constructor.
  - subst. constructor. apply caller_expr_max. apply Pos.max_lub_r in MAX. auto. constructor.
  - subst. constructor. apply caller_expr_max. auto. constructor.
  - subst. apply Pos.max_lub_l in MAX. apply Pos.max_lub_l in MAX. apply caller_list_expr_max. auto.
Qed.

(* expressions used in the caller code are part of the caller environment *)
Lemma is_caller_expr:
  forall caller sr l i e,
    sr = max_reg_code (ver_code caller) ->
    (ver_code caller) # l = Some i ->
    In e (expr_in_instr i) ->
    caller_expr sr e.
Proof.
  intros caller sr l i e SR CODE INEXPR.
  unfold max_reg_code in SR. rewrite PTree.fold1_spec in SR. apply PTree.elements_correct in CODE.
  assert (((max_reg_instr i) <= sr)%positive).
  { rewrite SR. eapply Pos.le_trans. 2: eapply fold_max; eauto. simpl. apply Pos.le_refl. }
  eapply in_max_reg; eauto.
Qed.

(* same for expression lists *)
Lemma is_caller_list_expr:
  forall caller sr lbl i l,
    sr = max_reg_code (ver_code caller) ->
    (ver_code caller) # lbl = Some i ->
    l = (expr_in_instr i) ->
    caller_list_expr sr l.
Proof.
  intros caller sr lbl i l SR CODE IN.
  unfold max_reg_code in SR. rewrite PTree.fold1_spec in SR. apply PTree.elements_correct in CODE.
  assert (((max_reg_instr i) <= sr)%positive).
  { rewrite SR. eapply Pos.le_trans. 2: eapply fold_max; eauto. simpl. apply Pos.le_refl. }
  eapply list_in_max_reg; eauto.
Qed.

Lemma max_reg_ml_cons:
  forall r e ml,
    max_reg_movelist ((r,e)::ml) = Pos.max (Pos.max r (max_reg_expr e)) (max_reg_movelist ml).
Proof.
  intros. unfold max_reg_movelist. rewrite fold_max_cons. simpl. auto.
Qed.

Lemma is_caller_movelist':
  forall sr ml,
    (max_reg_movelist ml <= sr)%positive ->
    caller_movelist sr ml.
Proof.
  intros. induction ml. constructor.
  destruct a. rewrite max_reg_ml_cons in H.
  assert (max_reg_movelist ml <=sr)%positive.
  { eapply Pos.max_lub_r; eauto. }
  assert (r <=sr)%positive.
  { eapply Pos.max_lub_l; eauto. eapply Pos.max_lub_l; eauto. }
  assert (max_reg_expr e <=sr)%positive.
  { eapply Pos.max_lub_r; eauto. eapply Pos.max_lub_l; eauto. }
  apply IHml in H0. constructor; auto.
  apply caller_expr_max. auto.
Qed.

Lemma is_caller_movelist:
  forall caller sr lbl ml next,
    sr = max_reg_code (ver_code caller) ->
    (ver_code caller) # lbl = Some (Move ml next) ->
    caller_movelist sr ml.
Proof.
  intros caller sr lbl ml next SR CODE. unfold max_reg_code in SR.
  rewrite PTree.fold1_spec in SR. apply PTree.elements_correct in CODE.
  assert (((max_reg_instr (Move ml next)) <= sr)%positive).
  { rewrite SR. eapply Pos.le_trans. 2: eapply fold_max; eauto. simpl. apply Pos.le_refl. }
  simpl in H. apply is_caller_movelist'. auto.
Qed.

Lemma max_reg_vm_cons:
  forall r e vm,
    max_reg_varmap ((r,e)::vm) = Pos.max (max_reg_expr e) (max_reg_varmap vm).
Proof.
  intros. unfold max_reg_varmap. rewrite fold_max_cons. simpl. auto.
Qed.

Lemma is_caller_varmap':
  forall sr vm,
    (max_reg_varmap vm <= sr)%positive ->
    caller_varmap sr vm.
Proof.
  intros. induction vm. constructor.
  destruct a. rewrite max_reg_vm_cons in H.
  assert (max_reg_varmap vm <=sr)%positive.
  { eapply Pos.max_lub_r; eauto. }
  assert (max_reg_expr e <=sr)%positive.
  { eapply Pos.max_lub_l; eauto. }
  apply IHvm in H0. constructor; auto.
  apply caller_expr_max. auto.
Qed.

Lemma is_caller_varmap_fs:
  forall caller sr lbl tgt vm sl next,
    sr = max_reg_code (ver_code caller) ->
    (ver_code caller) # lbl = Some (Framestate tgt vm sl next) ->
    caller_varmap sr vm.
Proof.
  intros caller sr lbl tgt vm sl next SR CODE. unfold max_reg_code in SR.
  rewrite PTree.fold1_spec in SR. apply PTree.elements_correct in CODE.
  assert (((max_reg_instr (Framestate tgt vm sl next)) <= sr)%positive).
  { rewrite SR. eapply Pos.le_trans. 2: eapply fold_max; eauto. simpl. apply Pos.le_refl. }
  simpl in H. apply is_caller_varmap'. apply Pos.max_lub_l in H. auto.
Qed.

Lemma is_caller_varmap_assume:
  forall caller sr lbl guard tgt vm sl next,
    sr = max_reg_code (ver_code caller) ->
    (ver_code caller) # lbl = Some (Assume guard tgt vm sl next) ->
    caller_varmap sr vm.
Proof.
  intros caller sr lbl guard tgt vm sl next SR CODE. unfold max_reg_code in SR.
  rewrite PTree.fold1_spec in SR. apply PTree.elements_correct in CODE.
  assert (((max_reg_instr (Assume guard tgt vm sl next)) <= sr)%positive).
  { rewrite SR. eapply Pos.le_trans. 2: eapply fold_max; eauto. simpl. apply Pos.le_refl. }
  simpl in H. apply is_caller_varmap'. eapply Pos.max_lub_r. eapply Pos.max_lub_l. eauto.
Qed.

Lemma max_reg_synth_cons:
  forall tgtr (vm:varmap) syl vm,
    max_reg_synth_list ((tgtr,vm)::syl) = Pos.max (max_reg_varmap vm) (max_reg_synth_list syl).
Proof.
  intros. unfold max_reg_synth_list. rewrite fold_max_cons. simpl. auto.
Qed.

Lemma is_caller_synth_list':
  forall sr sl,
    (max_reg_synth_list sl <= sr)%positive ->
    caller_synth_list sr sl.
Proof.
  intros sr sl H. induction sl.
  - constructor.
  - destruct a as [tgtr vm]. rewrite max_reg_synth_cons in H; auto. constructor.
    + unfold caller_synth_frame. apply is_caller_varmap'. simpl. eapply Pos.max_lub_l. eauto.
    + apply IHsl. eapply Pos.max_lub_r. eauto.
Qed.

Lemma is_caller_synth_list_fs:
  forall caller sr lbl tgt vm sl next,
    sr = max_reg_code (ver_code caller) ->
    (ver_code caller) # lbl = Some (Framestate tgt vm sl next) ->
    caller_synth_list sr sl.
Proof.
  intros caller sr lbl tgt vm sl next SR CODE. unfold max_reg_code in SR.
  rewrite PTree.fold1_spec in SR. apply PTree.elements_correct in CODE.
  assert (((max_reg_instr (Framestate tgt vm sl next)) <= sr)%positive).
  { rewrite SR. eapply Pos.le_trans. 2: eapply fold_max; eauto. simpl. apply Pos.le_refl. }
  simpl in H. apply is_caller_synth_list'. eapply Pos.max_lub_r. eauto.
Qed.

Lemma is_caller_synth_list_assume:
  forall caller sr lbl guard tgt vm sl next,
    sr = max_reg_code (ver_code caller) ->
    (ver_code caller) # lbl = Some (Assume guard tgt vm sl next) ->
    caller_synth_list sr sl.
Proof.
  intros caller sr lbl guard tgt vm sl next SR CODE. unfold max_reg_code in SR.
  rewrite PTree.fold1_spec in SR. apply PTree.elements_correct in CODE.
  assert (((max_reg_instr (Assume guard tgt vm sl next)) <= sr)%positive).
  { rewrite SR. eapply Pos.le_trans. 2: eapply fold_max; eauto. simpl. apply Pos.le_refl. }
  simpl in H. apply is_caller_synth_list'. eapply Pos.max_lub_r. eauto.
Qed.


(** * Callee environment preservation: properties of shift_rm  *)
Lemma rm_agree_shift_insert_ml:
  forall sr rm rm_opt newrm_opt ml,
    rm_agree sr rm rm_opt ->
    update_movelist (shift_ml sr ml) rm_opt newrm_opt ->
    rm_agree sr rm newrm_opt.
Proof.
  unfold update_movelist. intros sr rm rm_opt newrm_opt ml H H0.
  generalize dependent newrm_opt. induction ml; intros.
  - inv H0. auto.
  - unfold shift_ml in H0. inv H0. apply IHml in UPDATE.
    apply rm_agree_shift_insert. auto.
Qed.

(* same expr evaluation *)
Lemma eval_expr_callee:
  forall rm e_rm v e sr,
    eval_expr e e_rm v ->
    shift_rm sr e_rm rm ->
    eval_expr (shift_expr sr e) rm v.
Proof.
  intros rm e_rm v e sr EVAL SHIFT.
  unfold shift_rm in SHIFT.
  induction EVAL.
  - inv EVAL; inv EVALL; inv EVALR; constructor; econstructor; try constructor; eauto;
      apply SHIFT; auto.
  - inv EVAL. inv EVAL0; constructor; econstructor; try constructor; eauto.
Qed.

(* same list expr evaluation *)
Lemma eval_list_expr_callee:
  forall rm e_rm b le sr,
    eval_list_expr le e_rm b ->
    shift_rm sr e_rm rm ->
    eval_list_expr (map (shift_expr sr) le) rm b.
Proof.
  intros rm e_rm b le sr H H0. induction le.
  - simpl. inv H. constructor.
  - inv H; simpl; econstructor; try eapply eval_expr_callee; eauto.
Qed.

(* same list evaluation *)
Lemma eval_list_callee:
  forall rm e_rm valist le sr,
    eval_list le e_rm valist ->
    shift_rm sr e_rm rm ->
    eval_list (map (shift_expr sr) le) rm valist.
Proof.
  intros rm e_rm valist le sr H H0. generalize dependent valist. induction le; intros.
  - simpl. inv H. constructor.
  - inv H; simpl; econstructor; try eapply eval_expr_callee; eauto.
Qed.

Lemma eval_movelist_callee:
  forall rm e_rm ml newrm sr,
    update_movelist ml e_rm newrm ->
    shift_rm sr e_rm rm ->
    exists newrmopt,
      update_movelist (shift_ml sr ml) rm newrmopt /\
      shift_rm sr newrm newrmopt.
Proof.
  unfold update_movelist. intros rm e_rm ml newrm sr H H0. generalize dependent newrm. induction ml; intros.
  - inv H. exists rm. split. constructor. auto.
  - inv H. apply IHml in UPDATE. destruct UPDATE as [newrmopt [UP SHIFT']].
    exists (newrmopt # (shift_reg sr r) <- v). split.
    + constructor; auto. eapply eval_expr_callee; eauto.
    + apply shift_rm_insert. auto.
Qed.

Lemma eval_deopt_callee:
  forall rm e_rm vm newrm sr,
    update_regmap vm e_rm newrm ->
    shift_rm sr e_rm rm ->
    update_regmap (shift_vm sr vm) rm  newrm.
Proof.
  intros. generalize dependent newrm. induction vm; intros.
  - inv H. simpl. constructor.
  - destruct a as [r e]. inv H. simpl. constructor; auto.
    eapply eval_expr_callee; eauto.
Qed.

Lemma synth_callee:
  forall rm e_rm sl synth sr p,
    synthesize_frame p e_rm sl synth ->
    shift_rm sr e_rm rm ->
    synthesize_frame p rm (shift_syl sr sl) synth.
Proof.
  intros. generalize dependent synth. induction sl; intros.
  - inv H. simpl. constructor.
  - destruct a as [[tgt r] vm]. inv H. apply IHsl in SYNTH. constructor; auto.
    eapply eval_deopt_callee; eauto.
Qed.

 (* Shifting labels of a condition *)
Lemma shift_pc_cond:
  forall v iftrue iffalse sl,
    shift_lbl sl (pc_cond v iftrue iffalse) = pc_cond v (shift_lbl sl iftrue) (shift_lbl sl iffalse).
Proof.
  intros v iftrue iffalse sl. destruct v. unfold pc_cond. destruct z; simpl; auto.
Qed.

(* Backward direction *)
Lemma shift_opb:
  forall rm e_rm v o sr vsrc,
    eval_op (shift_op sr o) rm v ->
    shift_rm sr e_rm rm ->
    eval_op o e_rm vsrc ->       (* comes from safety *)
    vsrc = v.
Proof.
  intros rm e_rm v o sr vsrc H H0 H1. unfold shift_rm in H0.
  destruct o; inv H; inv H1; auto.
  apply H0 in GETRM0. rewrite GETRM0 in GETRM. inv GETRM. auto.
Qed.

Lemma shift_exprb:
  forall rm e_rm v e sr vsrc,
    eval_expr (shift_expr sr e) rm v ->
    shift_rm sr e_rm rm ->
    eval_expr e e_rm vsrc ->
    vsrc = v.
Proof.
  intros rm e_rm v e sr vsrc H H0 H1. destruct e; inv H; inv H1.
  - inv EVAL. inv EVAL0. eapply shift_opb in EVALL0; eauto. eapply shift_opb in EVALR0; eauto.
    subst. eapply eval_binop_values_determ; eauto.
  - inv EVAL. inv EVAL0. eapply shift_opb in EVAL; eauto. subst.
    eapply eval_unop_value_determ; eauto.
Qed.

Lemma shift_listexprb:
  forall rm e_rm v le sr vsrc,
    eval_list_expr ((List.map (shift_expr sr)) le) rm v ->
    shift_rm sr e_rm rm ->
    eval_list_expr le e_rm vsrc ->
    vsrc = v.
Proof.
  intros. generalize dependent v. induction H1; intros.
  - inv H. auto.
  - inv H. auto. assert (Vint 0 = Vint v0) by (eapply shift_exprb; eauto). inv H. omega.
  - inv H.
    + assert (Vint v = Vint 0) by (eapply shift_exprb; eauto). inv H. omega.
    + assert (Vint v = Vint v1) by (eapply shift_exprb; eauto). inv H.
      apply IHeval_list_expr in EVALL; auto.
Qed.

Lemma shift_listb:
  forall rm e_rm lv le sr lvsrc,
    eval_list ((List.map (shift_expr sr)) le) rm lv ->
    shift_rm sr e_rm rm ->
    eval_list le e_rm lvsrc ->
    lvsrc = lv.
Proof.
  intros. generalize dependent lv. induction H1; intros.
  - inv H. auto.
  - inv H. assert (v=v0) by (eapply shift_exprb; eauto). subst.
    apply IHeval_list in EVALL; auto. subst. auto.
Qed.

Lemma shift_movelistb:
  forall ml rm e_rm newrm sr newrm_e,
    shift_rm sr e_rm rm ->
    update_movelist (shift_ml sr ml) rm newrm ->
    update_movelist ml e_rm newrm_e ->
    shift_rm sr newrm_e newrm.
Proof.
  unfold update_movelist. intros ml. induction ml; intros.
  - inv H1. inv H0. auto.
  - inv H1. unfold shift_ml in H0. inv H0.
    assert (v=v0) by (eapply shift_exprb; eauto). subst.
    eapply IHml in UPDATE0; eauto. apply shift_rm_insert. auto.
Qed.

Lemma shift_deoptb:
  forall sr vm rm_e rm_opt newrm_opt newrm_e,
    shift_rm sr rm_e rm_opt ->
    update_regmap (shift_vm sr vm) rm_opt newrm_opt ->
    update_regmap vm rm_e newrm_e ->
    newrm_e = newrm_opt.
Proof.
  intros. generalize dependent newrm_opt. generalize dependent newrm_e.
  induction vm; intros.
  - simpl in H0. inv H0. inv H1. auto.
  - inv H1. unfold shift_vm in H0. rewrite map_cons in H0. unfold shift_expr, shift_op in H0. inv H0.
    eapply IHvm in UPDATE; eauto. subst.
    assert (v=v0) by (eapply shift_exprb; eauto). subst. auto.
Qed.

Lemma shift_synthb:
  forall sr p sl rm_e rm_opt stk_opt stk_e,
    shift_rm sr rm_e rm_opt ->
    synthesize_frame p rm_opt (shift_syl sr sl) stk_opt ->
    synthesize_frame p rm_e sl stk_e ->
    stk_e = stk_opt.
Proof.
  intros. generalize dependent stk_opt. generalize dependent stk_e.
  induction sl; intros.
  - inv H1. simpl in H0. inv H0. auto.
  - inv H1. unfold shift_syl, shift_vm, shift_expr, shift_op in H0. inv H0.
    eapply IHsl in SYNTH0; eauto. subst.
    assert (update = update0) by (eapply shift_deoptb; eauto). subst.
    rewrite FINDV0 in FINDV. inv FINDV. auto.
Qed.

(** * Match stack Relation *)
(* The stacks can contain both the same versions: non-optimized code *)
(* Or the caller + callee current versions have been replaced with the new version with inlining *)
(* Or we deoptimized from the inlined code: our synthesized stackframe corresponds to *)
(* what you would get if the Framestate after the inlined Call deoptimizes *)
Definition srv (v:version) : shift :=
  max_reg_code (ver_code v).

Definition slv (v:version) : shift :=
  max_lbl_code (ver_code v).

Inductive match_stack (p:program) (caller:version) (callee:version) (call_lbl:label) (args:list expr) (retreg:reg) (next:label) (tgt:deopt_target) (vm:varmap) (sl:list synth_frame) (params:list reg) (abs:def_abs_state): stack -> stack -> Prop :=
| ms_nil: (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs) nil nil

(* Pushing the same stackframe, with an equivalent regmap *)
| ms_same: forall s1 s2 r v lbl rm rm'
    (MS: (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs) s1 s2)
    (EQ: (regmap_eq rm rm')),
    (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs) ((Stackframe r v lbl rm)::s1) ((Stackframe r v lbl rm')::s2)

(* Replacing stackframes for the caller and caller with a stackframe for the inlined version *)
(* Useful if a call happens in the middle of the inlined callee *)
| ms_callee: forall s1 s2 vopt rm_e rm_r rm_opt retreg_e retlbl_e
    (MS: (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs) s1 s2)
    (DEF: defined rm_r (def_absstate_get call_lbl abs)) 
    (OPT: inline_version caller callee call_lbl args retreg next tgt vm sl params = OK vopt)
    (SHIFT: shift_rm (srv caller) rm_e rm_opt)
    (AGREE: rm_agree (srv caller) rm_r rm_opt),
    (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs)
      ((Stackframe retreg_e callee retlbl_e rm_e)::(Stackframe retreg caller next rm_r)::s1)
      ((Stackframe (shift_reg (srv caller) retreg_e) vopt (shift_lbl (slv caller) retlbl_e) rm_opt)::s2)

(* Replacing a stackframe of the caller with a stackframe of the new inlined version *)
(* Useful if a call happens outside of the inlined part *)
| ms_caller: forall s1 s2 vopt rm_r rm_opt retreg_r retlbl_r
    (MS: (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs) s1 s2)
    (DEF: forall retval, defined (rm_r # retreg_r <- retval) (def_absstate_get retlbl_r abs))
    (OPT: inline_version caller callee call_lbl args retreg next tgt vm sl params = OK vopt)
    (AGREE: rm_agree (srv caller) rm_r rm_opt),
    (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs)
      ((Stackframe retreg_r caller retlbl_r rm_r)::s1)
      ((Stackframe retreg_r vopt retlbl_r rm_opt)::s2)

(* When deoptimization occurs in the inlined code, we synthesize a stackframe *)
(* This stackframe should match the extra stackframe of the callee, *)
(* after deoptimization from the Framestate after the inlined Call *)
(* Deopt has been done earlier on the opt side: synth frames are here update_regmap has been done *)
| ms_deopt: forall s1 s2 tgtver rm rmdeopt synth
    (MS: (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs) s1 s2)
    (UPDATE: forall retval, exists rmdeopt',
          update_regmap vm (rm#retreg<-retval) rmdeopt' /\ regmap_eq rmdeopt' (rmdeopt#retreg<-retval))
    (SYNTH: forall retval, synthesize_frame p (rm#retreg<-retval) sl synth)
    (FINDBASE: find_base_version (fst tgt) p = Some tgtver), (* should this be checked before optim? *)
    (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs)
      ((Stackframe retreg caller next rm)::s1)
      ((Stackframe retreg tgtver (snd tgt) rmdeopt)::synth ++ s2).

Lemma match_stack_same:
  forall p caller callee call_lbl args retreg next tgt vm sl params abs stk,
    (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs) stk stk.
Proof.
  intros. induction stk. constructor. destruct a. constructor; auto. apply regmap_eq_refl.
Qed.

Lemma match_app:
  forall p caller callee call_lbl args retreg next tgt vm sl params abs s s' synth,
    (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs) s s' ->
    (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs) (synth++s) (synth++s').
Proof.
  intros. induction synth.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. destruct a. constructor; auto. apply regmap_eq_refl.
Qed.

Lemma app_match:
  forall synth synthopt s sopt p caller callee call_lbl args retreg next tgt vm sl params abs,
    (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs) s sopt ->
    (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs) synth synthopt ->
    (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs) (synth++s) (synthopt++sopt).
Proof.
  intros. induction H0.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. apply ms_same; auto.
  - repeat rewrite <- app_comm_cons. apply ms_callee; auto.
  - repeat rewrite <- app_comm_cons. apply ms_caller; auto.
  - rewrite <- app_comm_cons. rewrite <- app_comm_cons. rewrite <- app_assoc. apply ms_deopt; auto.
Qed.


(** * Order  *)
(* Instructions are matched 1 to 1 *)
(* A Move instruction replaces the Call *)
(* An Op instruction replaces the Return *)
(* Upon returning after deoptimization though, while the opt program takes one Return step *)
(* The source program must take one Return Step and one Framestate_deopt Step *)
(* But the index does not change *)
Inductive order : unit -> unit -> Prop := .
Lemma wfounded:
  well_founded order.
Proof.
  unfold well_founded. intros. destruct a. constructor. intros. inv H.
Qed.

Lemma trans:
  Relation_Definitions.transitive _ order.
Proof.
  unfold Relation_Definitions.transitive. intros. inv H.
Qed.

(** * Match states relation  *)
(* This proof is a lockstep backward internal simulation.
   Each step of the optimized program is matched with a step of the source.
   No index is needed for the match_states invariant.
   Inlined deoptimization extra frames is represented in the match_stack invariant.

<<

       st1 --------------- st2
        |                   |
       t|                   |t
        |                   |
        v                   v
       st1'--------------- st2'

>>
*)

Inductive match_states (p:program) (caller:version) (callee:version) (call_lbl:label) (args:list expr) (retreg:reg) (next:label) (tgt:deopt_target) (vm:varmap) (sl:list synth_frame) (params:list reg) (abs:def_abs_state): unit -> state -> state -> Prop :=
(* Executing the same code *)
| refl_match: forall stk stk' v l rm rm' ms
    (MS: (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs) stk stk')
    (EQ : regmap_eq rm rm'),
    (match_states p caller callee call_lbl args retreg next tgt vm sl params abs) tt
      (State stk  v l rm ms)
      (State stk' v l rm' ms)

(* When the execution is at the caller part of the optimized version *)
| caller_match: forall stk stk' l ms rm_r rm_opt vopt
    (MS: (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs) stk stk')
    (DEF: defined rm_r (def_absstate_get l abs))
    (OPT: inline_version caller callee call_lbl args retreg next tgt vm sl params = OK vopt)
    (AGREE: rm_agree (srv caller) rm_r rm_opt),
    (match_states p caller callee call_lbl args retreg next tgt vm sl params abs) tt
      (State stk  caller l rm_r ms)
      (State stk' vopt l rm_opt ms)

(* When the execution is at the callee part of the optimized version *)
(* There is an extra stackframe in the source execution *)
| callee_match: forall stk stk' l ms rm_r rm_e rm_opt vopt
    (MS: (match_stack p caller callee call_lbl args retreg next tgt vm sl params abs) stk stk')
    (DEF: defined rm_r (def_absstate_get call_lbl abs))
    (OPT: inline_version caller callee call_lbl args retreg next tgt vm sl params = OK vopt)
    (AGREE: rm_agree (srv caller) rm_r rm_opt)
    (SHIFT: shift_rm (srv caller) rm_e rm_opt),
    (match_states p caller callee call_lbl args retreg next tgt vm sl params abs) tt
      (State ((Stackframe retreg caller next rm_r)::stk) callee l rm_e ms)
      (State stk' vopt (shift_lbl (slv caller) l) rm_opt ms)

(* End of the execution *)
| final_match: forall retval ms,
    (match_states p caller callee call_lbl args retreg next tgt vm sl params abs) tt (Final retval ms) (Final retval ms).

(** * Code Preservation Properties  *)
Lemma fold_left_gso:
  forall codelist (fl:label->label) (fi:instruction->instruction) caller l i,
    (forall l', l<>fl l') ->
    (fold_left (fun c lbli => PTree.set (fl (fst lbli)) (fi (snd lbli)) c) codelist caller) # l = Some i ->
    caller # l = Some i.
Proof.
  intros codelist. induction codelist; intros.
  - simpl in H0. auto.
  - simpl in H0. apply IHcodelist in H0; auto. rewrite PTree.gso in H0. auto. apply H.
Qed.

Lemma join_code_caller_preserved:
  forall callee caller retreg retlbl tgt vm sl l i,
    (join_code callee caller (max_reg_code caller) (max_lbl_code caller) retreg retlbl tgt vm sl) # l = Some i ->
    caller_lbl (max_lbl_code caller) l ->
    caller # l = Some i.
Proof.
  intros. eapply fold_left_gso; eauto.
  unfold shift_lbl. unfold caller_lbl in H0. intros.
  apply Plt_ne. rewrite Pos.add_comm.
  assert (((max_lbl_code caller) < (max_lbl_code caller) + l')%positive) by apply Pos.lt_add_r.
  eapply Pos.le_lt_trans; eauto.
Qed.

Lemma caller_code_preserved:
  forall caller callee call_lbl args retreg next tgt vm sl params vopt i l,
    inline_version caller callee call_lbl args retreg next tgt vm sl params = OK vopt ->
    l <> call_lbl ->
    caller_lbl (slv caller) l ->
    (ver_code vopt) # l = Some i ->
    (ver_code caller) # l = Some i.
Proof.
  intros caller callee call_lbl args retreg next tgt vm sl params vopt i l OPT NOCALL CALLERLBL CODE.
  unfold inline_version in OPT. repeat do_ok. inv HDO. simpl in CODE.
  unfold param_assign in HDO0. repeat do_ok. rewrite PTree.gso in CODE; auto.
  eapply join_code_caller_preserved; eauto.
Qed.

Lemma call_move_code:
  forall caller callee call_lbl args retreg next tgt vm sl params vopt,
    inline_version caller callee call_lbl args retreg next tgt vm sl params = OK vopt ->
    exists movelist,
      make_movelist args params (max_reg_code (ver_code caller)) = OK movelist /\
      (ver_code vopt) # call_lbl =
      Some (Move movelist (shift_lbl (max_lbl_code (ver_code caller)) (ver_entry callee))).
Proof.
  intros caller callee call_lbl args retreg next tgt vm sl params vopt H.
  unfold inline_version in H. repeat do_ok. unfold param_assign in HDO0. repeat do_ok. exists m.
  inv HDO. split; auto.
  simpl. rewrite PTree.gss. auto.
Qed.

Lemma no_code_shift:
  forall l caller,
    caller # (shift_lbl (max_lbl_code caller) l) = None.
Proof.
  intros. unfold max_lbl_code. unfold max_label.
  destruct (caller ! (shift_lbl (max_pos caller) l)) eqn:CODE; auto.
  apply max_pos_correct in CODE. unfold shift_lbl in CODE. apply Pos.le_nlt in CODE.
  exfalso. apply CODE. rewrite Pos.add_comm. apply Pos.lt_add_r.
Qed.

Lemma join_code_callee_preserved:
  forall callee caller retreg retlbl tgt vm sl l i,
    (join_code callee caller (max_reg_code caller) (max_lbl_code caller) retreg retlbl tgt vm sl)
      # (shift_lbl (max_lbl_code caller) l) = Some i ->
    exists i',
      callee # l = Some i' /\
      inline_instr (max_reg_code caller) (max_lbl_code caller) retreg retlbl tgt vm sl i' = i.
Proof.
  assert (forall callee caller mixcode retreg retlbl tgt vm sl l i calleelist,
   (fold_left
      (fun (c : PTree.t instruction) (lbli : label * instruction) =>
         c # (shift_lbl (max_lbl_code caller) (fst lbli)) <-
         (inline_instr (max_reg_code caller) (max_lbl_code caller) retreg retlbl tgt vm sl (snd lbli)))
      calleelist mixcode) ! (shift_lbl (max_lbl_code caller) l) = Some i ->
   (forall x, In x calleelist -> callee # (fst x) = Some (snd x)) ->
   (mixcode # (shift_lbl (max_lbl_code caller) l) = Some i ->
    exists i',
      callee # l = Some i' /\
      inline_instr (max_reg_code caller) (max_lbl_code caller) retreg retlbl tgt vm sl i' = i) ->
   exists i',
     callee # l = Some i' /\
     inline_instr (max_reg_code caller) (max_lbl_code caller) retreg retlbl tgt vm sl i' = i).
  {
    intros callee caller mixcode retreg retlbl tgt vm sl l i calleelist H ELEMS H0.
    generalize dependent mixcode. induction (calleelist) as [|a elems IH]; intros.
    - simpl in H. apply H0 in H. auto.
    - simpl in H. apply IH in H; auto.
      { intros x IN. apply ELEMS. simpl. right. auto. }
      destruct a as [pos ins]. simpl.
      intros MIX. poseq_destr pos l.
      + rewrite PTree.gss in MIX. exists ins. split.
        * assert (In (l,ins) ((l,ins)::elems)). constructor. auto. apply ELEMS in H1. simpl in H1. auto.
        * inv MIX. auto.
      + rewrite PTree.gso in MIX. apply H0. apply MIX. unfold not. unfold shift_lbl. intros.
        apply HEQ. apply Pos.add_reg_r in H1. auto. }
  intros. eapply H; eauto.
  - intros. apply PTree.elements_complete. destruct x. simpl. auto.
  - intros. rewrite no_code_shift in H1. inv H1.
Qed.

Lemma callee_code_preserved:
  forall caller callee call_lbl args retreg next tgt vm sl params vopt i l,
    inline_version caller callee call_lbl args retreg next tgt vm sl params = OK vopt ->
    caller_lbl (max_lbl_code (ver_code caller)) call_lbl ->
    (ver_code vopt) # (shift_lbl (max_lbl_code (ver_code caller)) l) = Some i ->
    exists i', (ver_code callee) # l = Some i' /\
          inline_instr (max_reg_code (ver_code caller)) (max_lbl_code (ver_code caller)) retreg next tgt vm sl i' = i.
Proof.
  intros caller callee call_lbl args retreg next tgt vm sl params vopt i l H CALLCODE H0.
  unfold inline_version in H. repeat do_ok. inv HDO. unfold param_assign in HDO0. repeat do_ok.
  simpl in H0. rewrite PTree.gso in H0. apply join_code_callee_preserved in H0. auto.
  unfold shift_lbl. unfold caller_lbl in CALLCODE. unfold not. intros.
  rewrite <- H in CALLCODE. rewrite Pos.le_nlt in CALLCODE. apply CALLCODE.
  rewrite Pos.add_comm. apply Pos.lt_add_diag_r.
Qed.


(** * Safety Properties  *)
Lemma safe_caller_lbl:
  forall p s caller rm pc ms,
    safe (specir_sem p) (State s caller pc rm ms) ->
    caller_lbl (slv caller) pc .
Proof.
  intros p s caller rm pc ms H. apply safe_code in H. destruct H.
  eapply is_caller_lbl; eauto. unfold slv. auto.
Qed.

(** * Replacing the Call with a Move  *)
Lemma move_init_agree:
  forall sr movelist args params rm_r rm_opt newrm_opt,
    make_movelist args params sr = OK movelist ->
    update_movelist movelist rm_opt newrm_opt ->
    rm_agree sr rm_r rm_opt ->
    rm_agree sr rm_r newrm_opt.
Proof.
  intros. generalize dependent movelist. generalize dependent newrm_opt. generalize dependent params.
  induction args; intros.
  - simpl in H. destruct params; inv H. inv H0. auto.
  - simpl in H. destruct params as [| r params']; inv H. repeat do_ok.
    unfold update_movelist in H0. inv H0.
    eapply IHargs in HDO; auto.
    apply rm_agree_shift_insert. eauto. auto.
Qed.

Lemma move_init_shift:
  forall sr movelist args params rm_r rm_opt newrm_opt,
    make_movelist args params sr = OK movelist ->
    update_movelist movelist rm_opt newrm_opt ->
    rm_agree sr rm_r rm_opt ->
    caller_list_expr sr args ->
    exists valist newrm,
      eval_list args rm_r valist /\
      init_regs valist params = Some newrm /\
      shift_rm sr newrm newrm_opt.
Proof.
  intros. generalize dependent movelist. generalize dependent newrm_opt. generalize dependent params.
  induction args; intros.
  - destruct params; inv H. unfold update_movelist in H0. inv H0.
    exists nil. simpl. exists empty_regmap. split; try split.
    + constructor.
    + simpl. auto.
    + apply shift_rm_empty.
  - simpl in H. destruct params as [|r params']. inv H. repeat do_ok. unfold update_movelist in H0.
    inv H0.  inv H2. eapply IHargs in HDO.
    2: auto. 2: { unfold update_movelist. eauto. }
    destruct HDO as [valist [newrm [EVALL [INIT SHIFT]]]].
    exists (v::valist). exists (newrm # r <- v). split; try split.
    + constructor; auto. eapply agree_exprb; eauto.
    + simpl. rewrite INIT. auto.
    + apply shift_rm_insert. auto.
Qed.

(** * Correctness of deoptimizing in the inlined code  *)
Lemma fold_and:
  forall X f (l:list X) start,
    fold_left (fun b x => andb b (f x)) l start = true ->
    start = true.
Proof.
  intros X f l start H. generalize dependent start. induction l; intros.
  - simpl in H. auto.
  - simpl in H. specialize (IHl (start && f a) H). unfold andb in IHl.
    destruct start; auto.
Qed.

Lemma in_fold_and:
  forall X f (l:list X) i,
    In i l ->
    fold_left (fun b x => andb b (f x)) l true = true ->
    f i = true.
Proof.
  intros X f l i H H0. induction l. inv H.
  simpl in H. destruct H as [AI|IND].
  - subst. simpl in H0. eapply fold_and; eauto.
  - specialize (IHl IND). apply IHl. simpl in H0. apply fold_and in H0 as FA. rewrite FA in H0. auto.
Qed.

Lemma fold_andb_cons:
  forall X (a:X) l f,
    fold_left (fun b e => andb b (f e)) (a::l) true = true ->
    (f a) = true /\
    fold_left (fun b e => andb b (f e)) l true = true.
Proof.
  intros. destruct (f a) eqn:FA.
  - split; auto. simpl in H. rewrite FA in H. auto.
  - simpl in H. apply fold_and in H. rewrite H in FA. inv FA.
Qed.

Lemma eval_op_more:
  forall r o rm v val,
    eval_op o rm val ->
    op_no_use r o = true ->
    eval_op o (rm#r<-v) val.
Proof.
  intros. destruct o; inv H; constructor. rewrite PTree.gso; auto.
  inv H0. unfold reg_neq in H1. poseq_destr r r0; auto. simpl in H1. inv H1.
Qed.

Lemma eval_expr_more:
  forall r e rm v val,
    eval_expr e rm val ->
    expr_no_use r e = true ->
    eval_expr e (rm#r<-v) val.
Proof.
  intros. destruct e.
  - inv H. inv EVAL. inv H0. apply andb_prop in H1. inv H1.
    eapply eval_op_more in EVALL; eauto. eapply eval_op_more in EVALR; eauto.
    constructor. econstructor; eauto.
  - inv H. inv EVAL. eapply eval_op_more in EVAL0; eauto.
    constructor. econstructor; eauto.
Qed.

Lemma update_more:
  forall rm r v vm newrm,
    update_regmap vm rm newrm ->
    varmap_no_use r vm = true ->
    update_regmap vm (rm#r<-v) newrm.
Proof.
  intros. generalize dependent newrm. induction vm; intros.
  - inv H. constructor.
  - destruct a as [r' e]. inv H.
    assert (varmap_no_use r vm = true).
    { apply fold_andb_cons in H0.  destruct H0. auto. }
    assert (expr_no_use r e = true).
    { apply fold_andb_cons in H0.  destruct H0. apply andb_prop in H0. destruct H0. auto. }
    eapply IHvm in H; eauto.
    constructor; auto. inv H0.
    apply eval_expr_more; eauto.
Qed.

(* Correctness of deoptimizing with (retreg<-retreg) at the beginning *)
Lemma update_deopt_regmap_first:
  forall vm rm_r rm_deopt r v,
    update_regmap ((r, Unexpr Assign (Reg r))::vm) rm_r rm_deopt ->
    varmap_no_use r vm = true ->
    update_regmap ((r, Unexpr Assign (Reg r))::vm) (rm_r # r <- v) (rm_deopt # r <- v).
Proof.
  intros. inv H. rewrite PTree.set2. constructor.
  - constructor. econstructor; constructor. rewrite PTree.gss. auto.
  - apply update_more; auto.
Qed.

(* If a varmap doesn't use r, neither do its first assignment *)
Lemma no_use_head:
  forall r r0 e vm1,
    varmap_no_use r ((r0,e)::vm1) = true -> reg_neq r r0 = true /\ expr_no_use r e = true.
Proof.
  intros. unfold varmap_no_use in H. apply fold_andb_cons in H. destruct H. apply andb_prop in H. auto.
Qed.

(* If a varmap doesn't use r, neither do its tail *)
Lemma no_use_tail:
  forall r r0 e vm1,
    varmap_no_use r ((r0,e)::vm1) = true -> varmap_no_use r vm1 = true.
Proof.
  intros. unfold varmap_no_use in H. apply fold_andb_cons in H.
  unfold varmap_no_use. destruct H. auto.
Qed.

(* If a varmap which captures retreg doesn't have (retreg<-retreg) in its head, it has in its tail *)
Lemma capture_retreg_not_first:
  forall a vm r,
    check_varmap_capture_retreg (a::vm) r = true ->
    check_reconstructed r a = false ->
    check_varmap_capture_retreg vm r = true.
Proof.
  intros. unfold check_varmap_capture_retreg. unfold check_varmap_capture_retreg in H. simpl in H. rewrite H0 in H. auto. 
Qed.

(* If a varmap doesn't use retreg, it has at most once (retreg<-retreg) *)
Lemma no_use_only_once:
  forall vm r,
    varmap_no_use r vm = true -> check_varmap_only_once vm r = true.
Proof.
  induction vm; intros; auto.
  unfold varmap_no_use in H. apply fold_andb_cons in H.
  destruct H. unfold check_varmap_only_once. apply orb_true_intro. right.
  rewrite H. simpl. apply IHvm. auto.
Qed.

(* If a varmap has at most once (retreg<-retreg), its tail too *)
Lemma only_once_first:
  forall a vm r,
    check_varmap_only_once (a :: vm) r = true ->
    check_varmap_only_once vm r = true.
Proof.
  intros. unfold check_varmap_only_once in H. apply orb_prop in H. destruct H.
  - apply andb_prop in H. destruct H. apply no_use_only_once. auto.
  - unfold check_varmap_only_once. apply andb_prop in H. destruct H. auto.
Qed.

(* If a varmap has at most once (retreg<-retreg) and its head is (retreg<-retreg) then the tail doesn't use r *)
Lemma only_once_no_use:
  forall a vm r,
    check_varmap_only_once (a :: vm) r = true ->
    check_reconstructed r a = true ->
    varmap_no_use r vm = true.
Proof.
  intros. unfold check_varmap_only_once in H. rewrite H0 in H. simpl in H.
  assert (H1 : reg_neq r (fst a) = false).
  {
    unfold check_reconstructed in H0. destruct a. simpl. unfold reg_neq.
    rewrite Pos.eqb_sym.
    poseq_destr r0 r.
    + auto.
    + inv H0.
  }
  rewrite H1 in H. simpl in H. rewrite orb_false_r in H. auto.
Qed.

(* If we take a varmap which verifies the hypotheses of check_vm for the retreg r, if its first assignment is not (r<-r) then it doesn't use r *)
Lemma ifnot_reconstructed_then_no_use:
  forall a vm r,
    check_varmap_capture_retreg (a :: vm) r = true ->
    check_varmap_only_once (a :: vm) r = true ->
    check_reconstructed r a = false ->
    reg_neq r (fst a) = true /\ expr_no_use r (snd a) = true.
Proof.
  intros. split.
  - unfold check_varmap_only_once in H0.
    apply orb_prop in H0. destruct H0. rewrite H1 in H0. inv H0.
    apply andb_prop in H0. destruct H0. apply andb_prop in H0. destruct H0. auto.
  - unfold check_varmap_only_once in H0.
    apply orb_prop in H0. destruct H0. rewrite H1 in H0. inv H0.
    apply andb_prop in H0. destruct H0. apply andb_prop in H0. destruct H0. auto.
Qed.

(* Each varmap which verifies the hypotheses of check_vm is well formed, i.e. of the form :
        
       [  vm1  ] (retreg<-retreg) [  vm2  ]

where vm1 and vm2 are two regmaps which doesn't use retreg. *)
Lemma well_formed_regmap:
  forall vm r,
    check_varmap_capture_retreg vm r = true ->
    check_varmap_only_once vm r = true ->
    exists vm1 vm2,
      vm = vm1 ++ (r, Unexpr Assign (Reg r))::vm2 /\
      varmap_no_use r vm1 = true /\
      varmap_no_use r vm2 = true.
Proof.
  induction vm; intros. inv H.
  case_eq (check_reconstructed r a).
  + exists nil. exists vm. simpl. split.
    * destruct a.
      unfold check_reconstructed in H1.
      poseq_destr r0 r.
      ** destruct e. inv H1.
         destruct u; inv H1. destruct o; inv H3.
         apply Peqb_true_eq in H2. rewrite H2. auto. 
      ** inv H1.
    * apply only_once_no_use in H0; auto.
  + intros. apply ifnot_reconstructed_then_no_use in H as NOT_REC_NO_USE; auto. destruct NOT_REC_NO_USE. apply capture_retreg_not_first in H; auto. apply only_once_first in H0.
    specialize (IHvm r). rewrite H in IHvm. rewrite H0 in IHvm.
    destruct IHvm; auto. destruct H4.
    exists (a::x). exists x0. split.
    * rewrite <- app_comm_cons. destruct H4. rewrite H4. auto.
    * destruct H4. split.
      ** destruct H5. destruct a. unfold varmap_no_use. simpl. simpl in H2. rewrite H2. simpl in H3. rewrite H3. simpl. unfold varmap_no_use in H5. auto. 
      ** destruct H5. auto.      
Qed.

(* If a varmap with (retreg<-retreg) in the middle deoptimize from rm_r to rm_deopt,
   the same varmap with (retreg<-retreg) at the beginning will deoptimize from rm_r to a regmap equivalent to rm_deopt. *)
Lemma middle_to_first:
  forall vm1 vm2 rm_r rm_deopt r,
    varmap_no_use r vm1 = true ->
    varmap_no_use r vm2 = true ->
    update_regmap (vm1 ++ (r, (Unexpr Assign (Reg r)))::vm2) rm_r rm_deopt ->
    exists rm_deopt',
      update_regmap ((r, (Unexpr Assign (Reg r)))::(vm1 ++ vm2)) rm_r rm_deopt' /\
      regmap_eq rm_deopt' rm_deopt.
Proof.
  induction vm1.
  - intros. exists rm_deopt. split. auto. apply regmap_eq_refl.
  - intros. inv H1. apply IHvm1 in UPDATE; auto.
    + destruct UPDATE as [rm_deopt']. destruct H1. inv H1.
      exists (rm'0 # r0 <- v) # r <- v0. split.
      * apply update_cons. auto. rewrite <- app_comm_cons. apply update_cons; auto.
      * apply regmap_eq_trans with (rm'0 # r <- v0) # r0 <- v.
        apply regmap_eq_comm. apply regmap_eq_refl.
        apply no_use_head in H. destruct H. unfold reg_neq. rewrite Pos.eqb_sym. unfold reg_neq in H. auto.        
      apply regmap_eq_insert. auto.      
    + apply no_use_tail in H. auto.
Qed.

(* If a varmap with (retreg<-retreg) at the beginning deoptimize from rm_r to rm_deopt,
   the same varmap with (retreg<-retreg) in the middle will deoptimize from rm_r to a regmap equivalent to rm_deopt. *)
Lemma first_to_middle:
  forall vm1 vm2 rm_r rm_deopt r,
    varmap_no_use r vm1 = true ->
    varmap_no_use r vm2 = true ->
    update_regmap ((r, (Unexpr Assign (Reg r)))::(vm1 ++ vm2)) rm_r rm_deopt ->
    exists rm_deopt',
      update_regmap (vm1 ++ (r, (Unexpr Assign (Reg r)))::vm2) rm_r rm_deopt' /\
      regmap_eq rm_deopt' rm_deopt.
Proof.
  induction vm1.
  - intros. exists rm_deopt. simpl. simpl in H0. split. auto. apply regmap_eq_refl.
  - intros. inv H1. inv UPDATE. rewrite <- app_comm_cons.
    apply update_cons with r (Unexpr Assign (Reg r)) (vm1 ++ vm2) v rm_r rm'0 in UPDATE0; auto.
    apply no_use_tail in H as H'.
    specialize (IHvm1 vm2).
    apply IHvm1 with rm_r (rm'0 # r <- v) r in H'; auto.
    destruct H' as [rm_deopt']. destruct H1. exists rm_deopt' # r0 <- v0. split.
      * apply update_cons; auto.
      * apply regmap_eq_trans with (rm'0 # r <- v) # r0 <- v0.
        ** apply regmap_eq_insert. auto.
        ** apply regmap_eq_comm. apply regmap_eq_refl.
           apply no_use_head in H. destruct H. auto. 
Qed.

(* Correctness of deoptimizing, even with (retreg<-retreg) in the middle of the varmap *)
Lemma update_deopt_regmap_middle:
  forall vm1 vm2 rm_r rm_deopt r v,
    update_regmap (vm1 ++ (r, (Unexpr Assign (Reg r)))::vm2) rm_r rm_deopt ->
    varmap_no_use r vm1 = true ->
    varmap_no_use r vm2 = true ->
    exists rm_deopt',
      update_regmap (vm1 ++ (r, (Unexpr Assign (Reg r)))::vm2) (rm_r # r <- v) rm_deopt' /\
      regmap_eq rm_deopt' (rm_deopt # r <- v).
Proof.
  intros. apply middle_to_first with vm1 vm2 rm_r rm_deopt r in H0 as UPD_FIRST; auto.
  destruct UPD_FIRST as [rm_deopt'1]. destruct H2. eapply update_deopt_regmap_first in H2.
  - eapply first_to_middle in H2; auto. destruct H2 as [rm_deopt'2]. exists rm_deopt'2. split.
    + destruct H2. eauto.
    + apply regmap_eq_trans with rm_deopt'1 # r <- v. destruct H2. auto.
      apply regmap_eq_insert. auto.
  - unfold varmap_no_use. rewrite fold_left_app. unfold varmap_no_use in H0. rewrite H0. auto.
Qed.

(* Final theorem with check_vm
   Deoptimizing from inlined code creates a stackframe of the callee function, whatever the result of the inlined function is. *)
Lemma update_deopt_regmap:
  forall vm rm_r rm_deopt retreg def,
    update_regmap vm rm_r rm_deopt ->
    check_vm vm retreg def = OK tt ->
    forall retval, exists rm_deopt',
        update_regmap vm (rm_r # retreg <- retval) rm_deopt' /\
        regmap_eq rm_deopt' (rm_deopt # retreg <- retval).
Proof.
  intros. unfold check_vm in H0.
  destruct def eqn:DEF; inv H0.
  destruct (check_varmap_progress vm r) eqn:PROGRESS; inv H2.
  destruct (check_varmap_capture_retreg vm retreg) eqn:CAPTURE; inv H1.
  destruct (check_varmap_only_once vm retreg) eqn:ONCE; inv H2.
  assert (H0 : exists vm1 vm2,
             vm = vm1 ++ (retreg, Unexpr Assign (Reg retreg))::vm2 /\
             varmap_no_use retreg vm1 = true /\ varmap_no_use retreg vm2 = true).
  { apply well_formed_regmap; auto. }
  destruct H0 as [vm1]. destruct H0 as [vm2]. destruct H0. rewrite H0. destruct H1.
  apply update_deopt_regmap_middle; auto.
  rewrite <- H0. auto.
Qed.

Lemma app_synthsized:
  forall p rm sl1 sl2 s1 s2,
    synthesize_frame p rm sl1 s1 ->
    synthesize_frame p rm sl2 s2 ->
    synthesize_frame p rm (sl1 ++ sl2) (s1 ++ s2).
Proof.
  intros. generalize dependent s1. induction sl1; intros.
  - inv H. simpl. auto.
  - inv H. apply IHsl1 in SYNTH. simpl. constructor; auto.
Qed.

Lemma synthesized_app:
  forall p rm sl1 sl2 s,
    synthesize_frame p rm (sl1 ++ sl2) s ->
    exists s1, exists s2,
        s = s1 ++ s2 /\
        synthesize_frame p rm sl1 s1 /\
        synthesize_frame p rm sl2 s2.
Proof.
  intros. generalize dependent s. induction sl1; intros.
  - simpl in H. exists nil. exists s. split; auto. split; auto. constructor.
  - simpl in H. inv H. apply IHsl1 in SYNTH. destruct SYNTH as [s1 [s2 [APP [SYNTH1 SYNTH2]]]].
    exists (Stackframe r version l update::s1). exists s2. split; try split; auto.
    + simpl. rewrite APP. auto.
    + constructor; auto.
Qed.

(** * Progress preservation  *)
Lemma evaluate_op:
  forall rm rs op,
    defined rm (DefFlatRegset.Inj rs) ->
    check_op op rs = true ->
    exists v, eval_op op rm v.
Proof.
  intros rm rs op H H0. destruct op.
  simpl in H0.  unfold check_reg in H0. rewrite PositiveSet.mem_spec in H0.
  unfold defined in H. apply H in H0. destruct H0. exists x. constructor. auto.
  exists v. constructor.
Qed.

Lemma evaluate_expr:
  forall rm rs e,
    defined rm (DefFlatRegset.Inj rs) ->
    check_expr e rs = true ->
    exists v, eval_expr e rm v.
Proof.
  intros rm rs e H H0. destruct e; simpl in H0.
  - apply andb_prop in H0. destruct H0. eapply evaluate_op in H0; eauto. eapply evaluate_op in H1; eauto.
    destruct H0. destruct H1. destruct x. destruct x0.
    destruct b; econstructor; econstructor; econstructor; eauto; econstructor.
  - eapply evaluate_op in H0; eauto. destruct H0. destruct x.
    destruct u; econstructor; econstructor; econstructor; eauto; constructor.
Qed.

Lemma evaluate_succeeds:
  forall rm rs vm,
    defined rm (DefFlatRegset.Inj rs) ->
    check_varmap_progress vm rs = true ->
    exists newrm, update_regmap vm rm newrm.
Proof.
  intros rm rs vm H H0. induction vm; intros.
  - inv H0. exists empty_regmap. constructor.
  - destruct a as [r e]. inv H0. apply andb_prop in H2. destruct H2.
    apply IHvm in H1. destruct H1 as [newrm UP].
    eapply evaluate_expr in H0; eauto. destruct H0 as [v EVAL].
    exists (newrm # r <- v). constructor; auto.
Qed.

Lemma preserved_join_code_caller:
  forall callee caller sr sl retreg retlbl tgt vm sy l i,
    caller # l = Some i ->
    sl = (max_lbl_code caller) ->
    (join_code callee caller sr sl retreg retlbl tgt vm sy) # l = Some i.
Proof.
  intros.
  assert (forall c, c # l = Some i -> (join_code callee c sr sl retreg retlbl tgt vm sy) # l = Some i).
  { unfold join_code. induction (PTree.elements callee); intros; simpl; auto.
    apply IHl0. rewrite PTree.gso. auto. eapply is_caller_lbl in H; auto. unfold caller_lbl in H.
    unfold not. intros. subst. unfold shift_lbl in H. apply Pos.le_nlt in H. apply H.
    rewrite Pos.add_comm. apply Pos.lt_add_diag_r. }
  apply H1. auto.
Qed.

Lemma preserved_caller_code:
  forall caller callee call_lbl args retreg next tgt vm sl params vopt l i,
    inline_version caller callee call_lbl args retreg next tgt vm sl params = OK vopt ->
    l <> call_lbl ->
    ((ver_code caller) # l) = Some i ->
    ((ver_code vopt) # l) = Some i.
Proof.
  intros caller callee call_lbl args retreg next tgt vm sl params vopt l i INLINE DIFF CODE.
  unfold inline_version in INLINE. repeat do_ok. inv HDO. unfold param_assign in HDO0. repeat do_ok.
  simpl. rewrite PTree.gso; auto. apply preserved_join_code_caller; auto.
Qed.

Lemma replaced_call_move:
  forall caller callee call_lbl args retreg next tgt vm sl params vopt,
    inline_version caller callee call_lbl args retreg next tgt vm sl params = OK vopt ->
    exists movelist,
      make_movelist args params (max_reg_code (ver_code caller)) = OK movelist /\
      ((ver_code vopt) # call_lbl) = Some (Move movelist (shift_lbl (slv caller) (ver_entry callee))).
Proof.
  intros. unfold inline_version in H. repeat do_ok. inv HDO.
  unfold param_assign in HDO0. repeat do_ok. exists m. split; auto.
  simpl. rewrite PTree.gss. unfold slv. auto.
Qed.

Lemma folded_already:
  forall caller sr sl retreg retlbl tgt vm sy l i l0,
    caller # (shift_lbl sl l) = Some i ->
    ~ In l (map fst l0) ->
    (fold_left (fun c lbli => PTree.set (shift_lbl sl (fst lbli)) (inline_instr sr sl retreg retlbl tgt vm sy (snd lbli)) c)
               l0 caller) # (shift_lbl sl l) = Some i.
Proof.
  intros. generalize dependent caller.
  induction l0; intros.
  - simpl. auto.
  - simpl. apply IHl0.
    + unfold not. intros. apply H0. simpl. right. auto.
    + rewrite PTree.gso. auto. unfold not. intros. apply H0. simpl. left.
      unfold shift_lbl in H1. apply Pos.add_reg_r in H1. auto.
Qed.

Lemma preserved_join_code_callee:
  forall callee caller sr sl retreg retlbl tgt vm sy l i,
    callee # l = Some i ->
    (join_code callee caller sr sl retreg retlbl tgt vm sy) # (shift_lbl sl l) = Some (inline_instr sr sl retreg retlbl tgt vm sy i).
Proof.
  intros. unfold join_code.
  assert (list_norepet (map fst (PTree.elements callee))) by apply PTree.elements_keys_norepet.
  apply PTree.elements_correct in H. generalize dependent caller.

  induction (PTree.elements callee); intros; inv H.
  - simpl. simpl in H0. inv H0.
    apply folded_already.
    + rewrite PTree.gss. auto.
    + auto.
  - apply IHl0; auto. inv H0. auto.
Qed.

Lemma preserved_callee_code:
  forall caller callee p call_lbl args retreg retlbl tgt vm sy params vopt callee_fid callee_f l i,
    inline_version caller callee call_lbl args retreg retlbl tgt vm sy params = OK vopt ->
    (ver_code caller) # call_lbl = Some (Call callee_fid args retreg retlbl) ->
    find_function callee_fid p = Some callee_f ->
    callee = current_version callee_f ->
    (ver_code callee) # l = Some i ->
    (ver_code vopt) # (shift_lbl (slv caller) l) = Some (inline_instr (srv caller) (slv caller) retreg retlbl tgt vm sy i).
Proof.
  intros caller callee p call_lbl args retreg retlbl tgt vm sy params vopt callee_fid callee_f l i INLINE CALLCODE FINDOPTF CALLEE CODE.
  unfold inline_version in INLINE. repeat do_ok. inv HDO. unfold param_assign in HDO0. repeat do_ok.
  simpl. rewrite PTree.gso; auto.
  apply preserved_join_code_callee. auto.
  assert (H: caller_lbl (max_lbl_code (ver_code caller)) call_lbl).
  { eapply is_caller_lbl; eauto. }
  unfold caller_lbl in H. unfold not. intros. rewrite <- H0 in H.
  unfold shift_lbl in H. apply Pos.le_nlt in H. apply H. rewrite Pos.add_comm. apply Pos.lt_add_diag_r.
Qed.

(* The new Move instruction progresses *)
Lemma init_move:
  forall args params rm rm_opt sr valist movelist,
    rm_agree sr rm rm_opt ->
    caller_list_expr sr args ->
    eval_list args rm valist ->
    make_movelist args params sr = OK movelist ->
    exists newrm_opt,
      update_movelist movelist rm_opt newrm_opt.
Proof.
  intros args params rm rm_opt sr valist movelist H H0 H1 H2.
  generalize dependent movelist. generalize dependent valist. generalize dependent params.
  induction args; intros.
  - inv H2. destruct params; inv H4. inv H1. exists rm_opt. constructor.
  - inv H0. inv H2. destruct params. inv H3. repeat do_ok. inv H1.
    eapply IHargs in HDO; eauto. destruct HDO as [newrmopt UPDATE].
    exists (newrmopt # (shift_reg sr r) <- v). constructor; auto.
    eapply agree_expr; eauto.
Qed.

Lemma  progress_preserved:
  forall caller callee call_lbl args retreg next tgt vm sl params abs vopt p s1 s2 fidoptim caller_f fid callee_f l,
    inline_version caller callee call_lbl args retreg next tgt vm sl params = OK vopt ->
    find_function fidoptim p = Some caller_f ->
    caller = current_version caller_f ->
    (ver_code caller) ! call_lbl = Some (Call fid args retreg next) ->
    (ver_code caller) ! next = Some (Framestate tgt vm sl l) ->
    find_function fid p = Some callee_f ->
    callee = current_version callee_f ->
    check_synth_list sl = OK tt ->
    check_vm vm retreg (def_absstate_get call_lbl abs) = OK tt ->
    check_tgt tgt p = OK tt ->
    (match_states p caller callee call_lbl args retreg next tgt vm sl params abs) tt s1 s2 ->
    safe (specir_sem p) s1 ->
    (exists r : value, final_state (set_version p fidoptim vopt) s2 r) \/
    (exists (t : trace) (s2' : Smallstep.state (specir_sem (set_version p fidoptim vopt))),
        Step (specir_sem (set_version p fidoptim vopt)) s2 t s2').
Proof.
  intros caller callee call_lbl args retreg next tgt vm sl params abs vopt p s1 s2 fidoptim caller_f fid_e callee_f fsl INLINEV FINDOPTF CALLERV CALLCODE FSCODE FINDCALLEE CALLEEV SLCHECK VMCHECK TGTCHECK MATCH SAFE.
  inv MATCH.
  - right. apply safe_step in SAFE as [s1' [t STEP]]. (* refl_match *)
    inv STEP.
    { inv STEP0.
      - exists E0. exists (State stk' v next0 rm' ms). apply nd_exec_lowered. eapply exec_Nop; eauto.
      - exists E0. exists (State stk' v next0 (rm'#reg<-v0) ms). apply nd_exec_lowered. eapply exec_Op; eauto. eapply eval_expr_eq; eauto.
      - exists E0. assert (NEWUPDATE : exists newrm' : reg_map, update_movelist ml rm' newrm' /\ regmap_eq newrm' newrm).
        { eapply update_movelist_eq; eauto. apply regmap_eq_sym. auto. }
        destruct NEWUPDATE as [newrm']. exists (State stk' v next0 newrm' ms). apply nd_exec_lowered. eapply exec_Move; eauto. destruct H. auto.
      - exists E0. exists (State stk' v (pc_cond v0 iftrue iffalse) rm' ms). apply nd_exec_lowered.
        eapply exec_Cond; eauto. eapply eval_expr_eq; eauto.
      - poseq_destr fid fidoptim.
        + exists E0. exists (State (Stackframe retreg0 v next0 rm'::stk') (current_version (set_version_function vopt caller_f)) (ver_entry (current_version (set_version_function vopt caller_f))) newrm ms).
          apply nd_exec_lowered. eapply exec_Call; eauto.
          simpl. erewrite find_function_same; eauto. eapply eval_list_eq; eauto.
          unfold set_version_function. simpl. simpl in FINDF. rewrite FINDOPTF in FINDF. inv FINDF. auto.
        + exists E0. exists (State (Stackframe retreg0 v next0 rm'::stk') (current_version func) (ver_entry (current_version func)) newrm ms).
          apply nd_exec_lowered. eapply exec_Call; eauto.
          simpl. rewrite <- find_function_unchanged; auto. eapply eval_list_eq; eauto.
      - inv MS.
        + exists E0. exists (State s2 fprev next0 (rm'0#retreg0<-retval) ms). apply nd_exec_lowered.
          eapply exec_Return; eauto. eapply eval_expr_eq; eauto.
        + exists E0. exists (State s2 vopt0 (shift_lbl (slv (current_version caller_f)) next0) rm_opt#(shift_reg (srv (current_version caller_f)) retreg0)<-retval ms).
          apply nd_exec_lowered. eapply exec_Return; eauto. eapply eval_expr_eq; eauto.
        + exists E0. exists (State s2 vopt0 next0 (rm_opt#retreg0<-retval) ms). apply nd_exec_lowered.
          eapply exec_Return; eauto. eapply eval_expr_eq; eauto.
        + exists E0. exists (State (synth++s2) tgtver (snd tgt) (rmdeopt#retreg0<-retval) ms). apply nd_exec_lowered.
          eapply exec_Return; eauto. eapply eval_expr_eq; eauto.
      - inv MS. exists E0. exists (Final retval ms). apply nd_exec_lowered. eapply exec_Return_Final; eauto. eapply eval_expr_eq; eauto.
      - exists (Valprint printval::E0). exists (State stk' v next0 rm' ms). apply nd_exec_lowered.
        eapply exec_Printexpr; eauto. eapply eval_expr_eq; eauto.
      - exists (Stringprint str::E0). exists (State stk' v next0 rm' ms). apply nd_exec_lowered.
        eapply exec_Printstring; eauto.
      - exists E0. exists (State stk' v next0 rm' newms). apply nd_exec_lowered. eapply exec_Store; eauto. eapply eval_expr_eq; eauto. eapply eval_expr_eq; eauto.
      - exists E0. exists (State stk' v next0 (rm'#reg<-val) ms). apply nd_exec_lowered. eapply exec_Load; eauto. eapply eval_expr_eq; eauto.
      - exists E0. exists (State stk' v next0 rm' ms). apply nd_exec_lowered. eapply exec_Assume_holds; eauto. eapply eval_list_expr_eq; eauto.
      - exists E0. exists (State (synth++stk') newver la newrm ms). apply nd_exec_lowered.
        eapply exec_Assume_fails; eauto. eapply eval_list_expr_eq; eauto.
        simpl. rewrite <- base_version_unchanged. auto.
        eapply update_regmap_eq; eauto. apply regmap_eq_sym; auto. 
        apply synth_frame_unchanged. simpl in SYNTH. eapply synthesize_frame_eq; eauto. apply regmap_eq_sym. auto.
    }
    + exists E0. exists (State stk' v next0 rm' ms). inv DEOPT_COND.
      eapply nd_exec_Framestate_go_on. econstructor; eauto.
      simpl. rewrite <- base_version_unchanged. eauto. eapply update_regmap_eq; eauto. apply regmap_eq_sym. auto.
      apply synth_frame_unchanged. simpl in SYNTH. eapply synthesize_frame_eq; eauto. apply regmap_eq_sym. auto.
    + exists E0. exists (State stk' v next0 rm' ms). inv DEOPT_COND.
      eapply nd_exec_Framestate_go_on. econstructor; eauto.
      simpl. rewrite <- base_version_unchanged. eauto. eapply update_regmap_eq; eauto. apply regmap_eq_sym. auto. 
      apply synth_frame_unchanged. simpl in SYNTH. eapply synthesize_frame_eq; eauto. apply regmap_eq_sym. auto.

  - right. rewrite OPT in INLINEV. inv INLINEV. apply safe_step in SAFE as [s1' [t STEP]]. (* caller_match *)
    poseq_destr l call_lbl.
    + exists E0. apply replaced_call_move in OPT as [movelist [MAKE CODEMOVE]].
      inv STEP; try inv DEOPT_COND; try inv STEP0; rewrite CODE in CALLCODE; inv CALLCODE.
      eapply init_move in EVALL; eauto. destruct EVALL as [newrmopt UPDATE].
      2: { eapply is_caller_list_expr; eauto. unfold srv. auto. }
      exists (State stk' vopt (shift_lbl (slv (current_version caller_f)) (ver_entry (current_version callee_f))) newrmopt ms).
      apply nd_exec_lowered. eapply exec_Move; eauto.
    + inv STEP.
      { inv STEP0; eapply preserved_caller_code in HEQ; eauto.
        - exists E0. exists (State stk' vopt next0 rm_opt ms). apply nd_exec_lowered. eapply exec_Nop; eauto.
        - exists E0. exists (State stk' vopt next0 (rm_opt#reg<-v) ms). apply nd_exec_lowered. eapply exec_Op; eauto.
          eapply agree_expr; eauto. clear HEQ. eapply is_caller_expr; eauto. unfold srv. auto.
          simpl. left. auto.
        - eapply agree_movelist in UPDATE as [newrmopt [UPDATE AGREE']]; eauto.
          2: { clear HEQ. eapply is_caller_movelist; eauto. unfold srv. auto. }
          exists E0. exists (State stk' vopt next0 newrmopt ms). apply nd_exec_lowered. eapply exec_Move; eauto.
        - exists E0. exists (State stk' vopt (pc_cond v iftrue iffalse) rm_opt ms). apply nd_exec_lowered.
          eapply exec_Cond; eauto. eapply agree_expr; eauto. clear HEQ. eapply is_caller_expr; eauto.
          unfold srv. auto. simpl. left. auto.
        - exists E0. poseq_destr fid fidoptim.
          + exists (State (Stackframe retreg0 vopt next0 rm_opt::stk') (current_version (set_version_function vopt caller_f)) (ver_entry (current_version (set_version_function vopt caller_f))) newrm ms).
            apply nd_exec_lowered. eapply exec_Call; eauto.
            simpl. erewrite <- find_function_same; eauto.
            eapply agree_list; eauto. clear HEQ. eapply is_caller_list_expr; eauto. unfold srv. auto.
            unfold set_version_function. simpl. simpl in FINDF. rewrite FINDOPTF in FINDF. inv FINDF. auto.
          + exists (State (Stackframe retreg0 vopt next0 rm_opt::stk') (current_version func) (ver_entry (current_version func)) newrm ms).
            apply nd_exec_lowered. eapply exec_Call; eauto. simpl. rewrite <- find_function_unchanged; auto.
            eapply agree_list; eauto. clear HEQ. eapply is_caller_list_expr; eauto. unfold srv. auto.
        - eapply agree_expr in EVAL; eauto.
          2: { clear HEQ. eapply is_caller_expr; eauto. unfold srv; auto. simpl. left. auto. }
          inv MS.
          + exists E0. exists (State s2 fprev next0 (rm'#retreg0<-retval) ms). apply nd_exec_lowered.
            eapply exec_Return; eauto.
          + exists E0. exists (State s2 vopt0 (shift_lbl (slv (current_version caller_f)) next0) rm_opt0#(shift_reg (srv (current_version caller_f)) retreg0)<-retval ms).
            apply nd_exec_lowered. eapply exec_Return; eauto.
          + exists E0. exists (State s2 vopt0 next0 (rm_opt0#retreg0<-retval) ms). apply nd_exec_lowered.
            eapply exec_Return; eauto.
          + exists E0. exists (State (synth++s2) tgtver (snd tgt) (rmdeopt#retreg0<-retval) ms). apply nd_exec_lowered.
            eapply exec_Return; eauto.
        - inv MS. exists E0. exists (Final retval ms). apply nd_exec_lowered. eapply exec_Return_Final; eauto.
          eapply agree_expr; eauto. clear HEQ. eapply is_caller_expr; eauto. unfold srv. auto.
          simpl. left. auto.
        - exists (Valprint printval::E0). exists (State stk' vopt next0 rm_opt ms). apply nd_exec_lowered.
          eapply exec_Printexpr; eauto. eapply agree_expr; eauto. clear HEQ. eapply is_caller_expr; eauto.
          unfold srv. auto. simpl. left. auto.
        - exists (Stringprint str::E0). exists (State stk' vopt next0 rm_opt ms). apply nd_exec_lowered.
          eapply exec_Printstring; eauto.
        - exists E0. exists (State stk' vopt next0 rm_opt newms). apply nd_exec_lowered. eapply exec_Store; eauto.
          eapply agree_expr; eauto. clear HEQ. eapply is_caller_expr; eauto. unfold srv; auto.
          simpl. left. auto.
          eapply agree_expr; eauto. clear HEQ. eapply is_caller_expr; eauto. unfold srv; auto.
          simpl. right. left. auto.
        - exists E0. exists (State stk' vopt next0 (rm_opt#reg<-val) ms). apply nd_exec_lowered. eapply exec_Load; eauto.
          eapply agree_expr; eauto. clear HEQ. eapply is_caller_expr; eauto. unfold srv; auto.
          simpl. left. auto.
        - exists E0. exists (State stk' vopt next0 rm_opt ms). apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
          eapply agree_list_expr; eauto. clear HEQ. eapply is_caller_list_expr; eauto. unfold srv. auto.
        - exists E0. exists (State (synth++stk') newver la newrm ms). apply nd_exec_lowered.
          eapply exec_Assume_fails; eauto. eapply agree_list_expr; eauto. clear HEQ.
          eapply is_caller_list_expr; eauto. unfold srv. auto. simpl. rewrite <- base_version_unchanged. auto.
          eapply rm_agree_regmap; eauto. clear HEQ. eapply is_caller_varmap_assume; eauto. unfold srv. auto.
          apply synth_frame_unchanged. eapply rm_agree_synth; eauto. clear HEQ.
          eapply is_caller_synth_list_assume; eauto. unfold srv. auto. }
      * inv DEOPT_COND. eapply preserved_caller_code in HEQ; eauto.
        exists E0. exists (State stk' vopt next0 rm_opt ms). eapply nd_exec_Framestate_go_on.
        econstructor; eauto. simpl. rewrite <- base_version_unchanged. eauto.
        eapply rm_agree_regmap; eauto. clear HEQ. eapply is_caller_varmap_fs; eauto. unfold srv. auto.
        simpl. apply synth_frame_unchanged. eapply rm_agree_synth; eauto. clear HEQ.
        eapply is_caller_synth_list_fs; eauto. unfold srv. auto.
      * inv DEOPT_COND. eapply preserved_caller_code in HEQ; eauto.
        exists E0. exists (State stk' vopt next0 rm_opt ms). eapply nd_exec_Framestate_go_on.
        econstructor; eauto. simpl. rewrite <- base_version_unchanged. eauto.
        eapply rm_agree_regmap; eauto. clear HEQ. eapply is_caller_varmap_fs; eauto. unfold srv. auto.
        simpl. apply synth_frame_unchanged. eapply rm_agree_synth; eauto. clear HEQ.
        eapply is_caller_synth_list_fs; eauto. unfold srv. auto.

  - right. rewrite OPT in INLINEV. inv INLINEV. (* callee_match *)
    apply safe_step in SAFE as [s1' [t STEP]].
    set (caller := current_version caller_f). fold caller in SHIFT, AGREE, MS, OPT, STEP, CALLCODE.
    set (callee := current_version callee_f). fold callee in MS, OPT, STEP.
    inv STEP.
    { inv STEP0; eapply preserved_callee_code in CODE; eauto; unfold inline_instr, transf_instr, replace_return, stackframe_synthesis in CODE.
      - exists E0. simpl in CODE. exists (State stk' vopt (shift_lbl (slv caller) next0) rm_opt ms).
        apply nd_exec_lowered. eapply exec_Nop; eauto.
      - exists E0. exists (State stk' vopt (shift_lbl (slv caller) next0) (rm_opt#(shift_reg (srv caller) reg)<-v) ms).
        apply nd_exec_lowered. eapply exec_Op; eauto. eapply eval_expr_callee; eauto.
      - eapply eval_movelist_callee in UPDATE as H; eauto. destruct H as [newrmopt [UP SHIFT']].
        exists E0. exists (State stk' vopt (shift_lbl (slv caller) next0) newrmopt ms).
        apply nd_exec_lowered. eapply exec_Move; eauto.
      - exists E0. exists (State stk' vopt (shift_lbl (slv caller) (pc_cond v iftrue iffalse)) rm_opt ms).
        apply nd_exec_lowered. eapply exec_Cond; eauto. eapply eval_expr_callee; eauto.
        rewrite shift_pc_cond. auto.
      - exists E0. poseq_destr fid fidoptim.
        + simpl in FINDF. rewrite FINDF in FINDOPTF. inv FINDOPTF.
          exists (State (Stackframe (shift_reg (srv caller) retreg0) vopt (shift_lbl (slv caller) next0) rm_opt::stk') (current_version (set_version_function vopt caller_f)) (ver_entry (current_version (set_version_function vopt caller_f))) newrm ms).
          apply nd_exec_lowered. eapply exec_Call; eauto. simpl.
          erewrite find_function_same; eauto.
          eapply eval_list_callee; eauto.
        + exists (State (Stackframe (shift_reg (srv caller) retreg0) vopt (shift_lbl (slv caller) next0) rm_opt::stk') (current_version func) (ver_entry (current_version func)) newrm ms).
          apply nd_exec_lowered. eapply exec_Call; eauto. simpl. rewrite <- find_function_unchanged; auto.
          eapply eval_list_callee; eauto.
      - exists E0. exists (State stk' vopt next (rm_opt#(retreg)<-retval) ms). (* going back to the caller part *)
        apply nd_exec_lowered. eapply exec_Op; eauto. eapply eval_expr_callee; eauto.
      - exists (Valprint printval::E0). exists (State stk' vopt (shift_lbl (slv caller) next0) rm_opt ms).
        apply nd_exec_lowered. eapply exec_Printexpr; eauto. eapply eval_expr_callee; eauto.
      - exists (Stringprint str::E0). exists (State stk' vopt (shift_lbl (slv caller) next0) rm_opt ms).
        apply nd_exec_lowered. eapply exec_Printstring; eauto.
      - exists E0. exists (State stk' vopt (shift_lbl (slv caller) next0) rm_opt newms).
        apply nd_exec_lowered. eapply exec_Store; eauto. eapply eval_expr_callee; eauto.
        eapply eval_expr_callee; eauto.
      - exists E0. exists (State stk' vopt (shift_lbl (slv caller) next0) (rm_opt#(shift_reg (srv caller) reg)<-val) ms).
        apply nd_exec_lowered. eapply exec_Load; eauto. eapply eval_expr_callee; eauto.
      - exists E0. exists (State stk' vopt (shift_lbl (slv caller) next0) rm_opt ms).
        apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
        eapply eval_list_expr_callee; eauto.
      - exists E0. destruct sl. 2: { inv SLCHECK. }
        assert (H: exists newrm',
                   update_regmap vm rm_r newrm').
        { unfold check_vm in VMCHECK. destruct (def_absstate_get call_lbl abs) eqn:RS; inv VMCHECK.
          destruct (check_varmap_progress vm r) eqn:PROGRESS; inv H0. 
          eapply evaluate_succeeds; eauto. }
        destruct H as [newrm' UP]. unfold check_tgt in TGTCHECK.
        destruct (find_base_version (fst tgt) p) eqn:BASETGT; inv TGTCHECK.
        assert (SYNTH': synthesize_frame p rm_r ((tgt, retreg, vm)::nil) ((Stackframe retreg v (snd tgt) newrm')::nil)).
        { destruct tgt. constructor; auto. constructor. }
        exists (State ((synth++((Stackframe retreg v (snd tgt) newrm')::nil))++stk') newver la newrm ms).
        apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
        + eapply eval_list_expr_callee; eauto.
        + simpl. rewrite <- base_version_unchanged. auto.
        + eapply eval_deopt_callee; eauto.
        + simpl globalenv. apply synth_frame_unchanged.
          apply app_synthsized. eapply synth_callee; eauto.
          eapply rm_agree_synth; eauto. constructor. 2: constructor. unfold caller_synth_frame.
          simpl. eapply is_caller_varmap_fs; unfold srv; eauto. }

    + inv DEOPT_COND; eapply preserved_callee_code in CODE; eauto; unfold inline_instr, transf_instr, replace_return, stackframe_synthesis in CODE.
      exists E0. destruct sl. 2: { inv SLCHECK. }
      assert (H: exists newrm',
                 update_regmap vm rm_r newrm').
      { unfold check_vm in VMCHECK. destruct (def_absstate_get call_lbl abs) eqn:RS; inv VMCHECK.
        destruct (check_varmap_progress vm r) eqn:PROGRESS; inv H0. 
        eapply evaluate_succeeds; eauto. }
      destruct H as [newrm' UP]. unfold check_tgt in TGTCHECK.
      destruct (find_base_version (fst tgt) p) eqn:BASETGT; inv TGTCHECK.
      assert (SYNTH': synthesize_frame p rm_r ((tgt, retreg, vm)::nil) ((Stackframe retreg v (snd tgt) newrm')::nil)).
      { destruct tgt. constructor; auto. constructor. }
      exists (State stk' vopt (shift_lbl (slv caller) next0) rm_opt ms). eapply nd_exec_Framestate_go_on.
      econstructor; eauto.
      * simpl. rewrite <- base_version_unchanged. eauto.
      * eapply eval_deopt_callee; eauto.
      * simpl globalenv. apply synth_frame_unchanged.
        apply app_synthsized. eapply synth_callee; eauto.
        eapply rm_agree_synth; eauto. constructor. 2: constructor. unfold caller_synth_frame.
        simpl. eapply is_caller_varmap_fs; unfold srv; eauto.

    + inv DEOPT_COND; eapply preserved_callee_code in CODE; eauto; unfold inline_instr, transf_instr, replace_return, stackframe_synthesis in CODE.
      exists E0. destruct sl. 2: { inv SLCHECK. }
      assert (H: exists newrm',
                 update_regmap vm rm_r newrm').
      { unfold check_vm in VMCHECK. destruct (def_absstate_get call_lbl abs) eqn:RS; inv VMCHECK.
        destruct (check_varmap_progress vm r) eqn:PROGRESS; inv H0. 
        eapply evaluate_succeeds; eauto. }
      destruct H as [newrm' UP]. unfold check_tgt in TGTCHECK.
      destruct (find_base_version (fst tgt) p) eqn:BASETGT; inv TGTCHECK.
      assert (SYNTH': synthesize_frame p rm_r ((tgt, retreg, vm)::nil) ((Stackframe retreg v (snd tgt) newrm')::nil)).
      { destruct tgt. constructor; auto. constructor. }
      exists (State ((synth++((Stackframe retreg v (snd tgt) newrm')::nil))++stk') newver la newrm ms).
      eapply nd_exec_Framestate_deopt. econstructor; eauto.
      * simpl. rewrite <- base_version_unchanged. eauto.
      * eapply eval_deopt_callee; eauto.
      * simpl globalenv. apply synth_frame_unchanged.
        apply app_synthsized. eapply synth_callee; eauto.
        eapply rm_agree_synth; eauto. constructor. 2: constructor. unfold caller_synth_frame.
        simpl. eapply is_caller_varmap_fs; unfold srv; eauto.

  - left. exists retval. constructor.
Qed.

(** * The internal backward simulation  *)
Ltac agreeb :=
  match goal with
  | [H: eval_expr ?expr ?rm_opt ?v,
        H1: rm_agree ?s ?rm_r ?rm_opt |- _] => eapply agree_exprb in H; eauto; try eapply is_caller_expr; eauto; try constructor; auto
  | [H: eval_list_expr ?expr ?rm_opt ?v,
        H1: rm_agree ?s ?rm_r ?rm_opt |- _] => eapply agree_list_exprb in H; eauto; try eapply is_caller_list_expr; eauto; try constructor; auto
  | [H: eval_list ?expr ?rm_opt ?v,
        H1: rm_agree ?s ?rm_r ?rm_opt |- _] => eapply agree_listb in H; eauto; try eapply is_caller_list_expr; eauto; try constructor; auto
  end.


Theorem inlining_correct:
  forall p fidoptim call_lbl newp,
    optimize_inline fidoptim call_lbl p = OK newp ->
    backward_internal_simulation p newp.
Proof.
  intros p fidoptim call_lbl newp H. unfold optimize_inline in H. repeat do_ok.
  rename HDO0 into FINDOPTF. destruct ((ver_code (current_version f))!call_lbl) eqn:CALL_CODE; inv H1.
  destruct i; inv H0. rename f0 into fid. rename l into args. rename r into retreg. rename l0 into next.
  destruct ((ver_code (current_version f))!next) eqn:FS_CODE; inv H1. destruct i; inv H0.
  rename d into tgt. rename v into vm. rename l into sl. rename l0 into nextfs.
  repeat do_ok. rename f0 into callee_f. rename f into caller_f. rename HDO4 into OPT.
  rename HDO0 into SL_CHECK. rename HDO1 into VM_CHECK. destruct u. destruct u0. destruct u1.
  rename HDO2 into TGT_CHECK. rename HDO3 into DEFS. rename HDO5 into FIND_E. rename d into abs.
  set (caller := current_version (caller_f)). fold caller in CALL_CODE, FS_CODE, OPT.
  set (callee := current_version (callee_f)). fold callee in OPT.
  set (params := (fn_params callee_f)). fold params in OPT. rename v into vopt.
  assert (SAME_ENTRY: ver_entry vopt = ver_entry caller).
  { unfold inline_version in OPT. repeat do_ok. simpl. auto. }
  apply Backward_internal_simulation with (bsim_match_states := match_states p caller callee call_lbl args retreg next tgt vm sl params abs) (bsim_order := order).
  - apply wfounded.
  - apply trans.

  - unfold reflexive_forge. intros synchro stack r1 s1 ms FORGE.
    destruct synchro; simpl in FORGE; repeat do_ok; simpl.
    + poseq_destr f fidoptim.  (* is the called function the optimized one? *)
      * erewrite find_function_same; eauto. simpl. rewrite HDO0. simpl.
        repeat (esplit; eauto). rewrite current_version_same. rewrite SAME_ENTRY.
        rewrite FINDOPTF in HDO1. inv HDO1.
        eapply caller_match; auto. apply match_stack_same.
        apply interpreter_proof.init_regs_correct in HDO0. eapply def_analyze_init; eauto.
        apply rm_agree_refl.
      * erewrite <- find_function_unchanged; eauto. rewrite HDO1. simpl. rewrite HDO0. simpl.
        repeat (esplit; eauto). constructor. apply match_stack_same. apply regmap_eq_refl.
    + destruct stack; try destruct s; inv FORGE.
      * repeat (esplit; eauto). constructor.
      * repeat (esplit; eauto). simpl. constructor. apply match_stack_same.
        apply regmap_eq_insert. apply regmap_eq_refl.
    + destruct d. repeat do_ok. simpl. rewrite <- base_version_unchanged. rewrite HDO0. simpl.
      repeat (esplit; eauto). simpl. constructor. apply match_stack_same. apply regmap_eq_refl.
    + inv FORGE. destruct r1; repeat (esplit; eauto).
      * simpl. apply refl_match. apply match_stack_same. apply regmap_eq_refl.
      * simpl. apply final_match.

  - intros i s1 s2 r H H0 H1. inv H1. inv H. exists (Final r ms). split.
    apply star_refl. constructor.

  - intros. destruct i. eapply progress_preserved; eauto.

  - intros s2 t s2' STEP i s1 MATCH SAFE. exists tt. (* Backward diagram *)
    inv MATCH.

    + inv STEP.                 (* refl_match *)
      { inv STEP0.
        - exists (State stk v next0 rm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Nop; eauto.
          + apply refl_match; auto.
        - exists (State stk v next0 (rm#reg<-v0) ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Op; eauto.
            eapply eval_expr_eq; eauto. apply regmap_eq_sym. auto.
          + apply refl_match. auto. apply regmap_eq_insert. auto.
        - assert (NEWUPDATE : exists newrm' : reg_map, update_movelist ml rm newrm' /\ regmap_eq newrm' newrm).
          + eapply update_movelist_eq; eauto.
          + destruct NEWUPDATE as [newrm']. destruct H. exists (State stk v next0 newrm' ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Move; eauto.
            * apply refl_match; auto.
        - exists (State stk v (pc_cond v0 iftrue iffalse) rm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Cond; eauto. eapply eval_expr_eq; eauto. apply regmap_eq_sym; auto. 
          + apply refl_match; auto.
        - poseq_destr fid0 fidoptim; simpl in FINDF.
          + erewrite find_function_same in FINDF; eauto. inv FINDF. (* calling optimized caller function *)
            exists (State (Stackframe retreg0 v next0 rm ::stk) (current_version caller_f) (ver_entry (current_version caller_f)) newrm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto. eapply eval_list_eq; eauto. apply regmap_eq_sym; auto. 
            * rewrite current_version_same. rewrite SAME_ENTRY. apply caller_match; auto.
              apply ms_same; auto. 
              eapply def_analyze_init; eauto.
              apply rm_agree_refl. 
          + rewrite <- find_function_unchanged in FINDF; auto. (* calling any other function *)
            exists (State (Stackframe retreg0 v next0 rm :: stk) (current_version func) (ver_entry (current_version func)) newrm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto. eapply eval_list_eq; eauto. apply regmap_eq_sym. auto. 
            * apply refl_match. apply ms_same; auto. apply regmap_eq_refl.
        - inv MS.
          + exists (State s1 fprev next0 (rm0#retreg0<-retval) ms). split. (* ms_same *)
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto. eapply eval_expr_eq; eauto. apply regmap_eq_sym. auto.
            * apply refl_match. auto. apply regmap_eq_insert. auto.
          + exists (State (Stackframe retreg caller next rm_r ::s1) callee retlbl_e (rm_e # retreg_e <- retval) ms). split. (* ms_callee *)
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto. eapply eval_expr_eq; eauto. apply regmap_eq_sym. auto.
            * apply callee_match; auto.
              apply rm_agree_shift_insert. auto. apply shift_rm_insert. auto.
          + exists (State s1 caller next0 (rm_r # retreg0 <- retval) ms). split. (* ms_caller *)
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto. eapply eval_expr_eq; eauto. apply regmap_eq_sym. auto. 
            * apply caller_match; auto.
              apply rm_agree_insert. auto.
          + destruct tgt as [fidtgt lbltgt]. simpl. simpl in FINDBASE. (* ms_deopt *)
            destruct UPDATE with retval as [rmdeopt UPDATE']. destruct UPDATE'.
            exists (State (synth++s1) (*no*) fprev lbltgt rmdeopt ms). split.
            (* Since deoptimization occurred in the inlined part, when returning *)
            (* from the inlined function in the source execution, we must deoptimize *)
            (* using the Framestate after the inlined Call *)
            * left. eapply plus_two.
              ** apply nd_exec_lowered. eapply exec_Return; eauto. eapply eval_expr_eq; eauto. apply regmap_eq_sym. auto.
              ** { eapply nd_exec_Framestate_deopt. econstructor.
                   - apply FS_CODE.
                   - apply FINDBASE.
                   - apply H.
                   - apply SYNTH. }
              ** auto.
            * apply refl_match; auto. apply match_app. auto.
        - inv MS. exists (Final retval ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Return_Final; eauto. eapply eval_expr_eq; eauto. apply regmap_eq_sym. auto.
          + apply final_match.
        - exists (State stk v next0 rm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Printexpr; eauto. eapply eval_expr_eq; eauto. apply regmap_eq_sym. auto.
          + apply refl_match; auto.
        - exists (State stk v next0 rm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Printstring; eauto.
          + apply refl_match; auto.
        - exists (State stk v next0 rm newms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Store; eauto. eapply eval_expr_eq; eauto. apply regmap_eq_sym. auto. eapply eval_expr_eq; eauto. apply regmap_eq_sym. auto. 
          + apply refl_match; auto.
        - exists (State stk v next0 (rm#reg<-val) ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Load; eauto. eapply eval_expr_eq; eauto. apply regmap_eq_sym. auto.
          + apply refl_match; auto. apply regmap_eq_insert. auto.
        - exists (State stk v next0 rm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_holds; eauto. eapply eval_list_expr_eq; eauto. apply regmap_eq_sym. auto.
          + apply refl_match; auto.
        - simpl in FINDF. rewrite <- base_version_unchanged in FINDF. apply synth_frame_unchanged in SYNTH.
          exists (State (synth++stk) newver la newrm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_fails; eauto. eapply eval_list_expr_eq; eauto. apply regmap_eq_sym. auto. eapply update_regmap_eq; eauto. eapply synthesize_frame_eq; eauto.
          + apply refl_match. apply match_app. auto. apply regmap_eq_refl. }
      * inv DEOPT_COND. simpl in FINDF. rewrite <- base_version_unchanged in FINDF.
        apply synth_frame_unchanged in SYNTH. exists (State stk v next0 rm ms). split.
        ** left. apply plus_one. eapply nd_exec_Framestate_go_on. econstructor; eauto. eapply update_regmap_eq; eauto. eapply synthesize_frame_eq; eauto. 
        ** apply refl_match; auto.
      * inv DEOPT_COND. simpl in FINDF. rewrite <- base_version_unchanged in FINDF.
        apply synth_frame_unchanged in SYNTH. exists (State (synth++stk) newver la newrm ms). split.
        ** left. apply plus_one. eapply nd_exec_Framestate_deopt. econstructor; eauto. eapply update_regmap_eq; eauto. eapply synthesize_frame_eq; eauto. 
        ** apply refl_match. apply match_app. auto. apply regmap_eq_refl.

    + rewrite OPT0 in OPT. inv OPT. (* caller_match *)
      apply safe_caller_lbl in SAFE as CALLERLBL.
      poseq_destr l call_lbl.
      { apply call_move_code in OPT0 as H. destruct H as [movelist [MAKE CODE_CALL]].
        (* going into the inlined part *)
        inv STEP; try inv DEOPT_COND. 2: { rewrite CODE in CODE_CALL. inv CODE_CALL. }
        2: { rewrite CODE in CODE_CALL. inv CODE_CALL. }
        inv STEP0; rewrite CODE in CODE_CALL; inv CODE_CALL.
        eapply move_init_agree in MAKE as AGREE'; eauto. rename newrm into newrmopt.
        eapply move_init_shift in MAKE; eauto.
        2: { eapply is_caller_list_expr. eauto. eapply CALL_CODE. simpl. auto. }
        destruct MAKE as [valist [newrmsrc [EVAL [INIT SHIFT]]]].
        exists (State (Stackframe retreg caller next rm_r ::stk) (current_version callee_f) (ver_entry (current_version callee_f)) newrmsrc ms). split.
        - left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
        - apply callee_match; auto. }
      inv STEP.
      { inv STEP0; eapply caller_code_preserved in HEQ; eauto.
        - exists (State stk caller next0 rm_r ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Nop; eauto.
          + apply caller_match; auto.
            eapply def_analyze_correct; eauto. simpl. auto.
            unfold caller in HEQ. unfold def_dr_transf. rewrite HEQ. auto.
        - exists (State stk caller next0 (rm_r#reg<-v) ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Op; eauto. agreeb.
          + apply caller_match; auto.
            eapply def_analyze_correct; eauto. simpl. auto.
            unfold caller in HEQ. unfold def_dr_transf. rewrite HEQ. apply define_insert. auto.
            apply rm_agree_insert. auto.
        - eapply agree_movelistb in UPDATE; auto. destruct UPDATE as [newrmsrc [UPDATE AGREE']].
          exists (State stk caller next0 newrmsrc ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Move; eauto.
          + apply caller_match; eauto.
            eapply def_analyze_correct; eauto. simpl. auto.
            unfold caller in HEQ. unfold def_dr_transf. rewrite HEQ. eapply define_insert_list; eauto.
          + auto.
          + eapply is_caller_movelist; eauto. unfold srv. auto.
        - exists (State stk caller (pc_cond v iftrue iffalse) rm_r ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Cond; eauto. agreeb.
          + apply caller_match; auto.
            eapply def_analyze_correct; eauto.
            { destruct v; destruct z; simpl; auto. }
            unfold caller in HEQ. unfold def_dr_transf. rewrite HEQ. auto.
        - poseq_destr fid0 fidoptim; simpl in FINDF.
          + erewrite find_function_same in FINDF; eauto. inv FINDF. (* calling optimized caller function *)
            exists (State (Stackframe retreg0 caller next0 rm_r ::stk) (current_version caller_f) (ver_entry (current_version caller_f)) newrm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto. agreeb.
            * rewrite current_version_same. rewrite SAME_ENTRY. apply caller_match; auto.
              apply ms_caller; auto.
              { intros. eapply def_analyze_correct; eauto. simpl. auto. unfold caller in HEQ.
                unfold def_dr_transf. rewrite HEQ. apply define_insert. auto. }
              eapply def_analyze_init; eauto. apply rm_agree_refl.
          + rewrite <- find_function_unchanged in FINDF; auto. (* calling any other function *)
            exists (State (Stackframe retreg0 caller next0 rm_r :: stk) (current_version func) (ver_entry (current_version func)) newrm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto. agreeb.
            * apply refl_match; try (apply regmap_eq_refl). apply ms_caller; auto.
              { intros. eapply def_analyze_correct; eauto. simpl. auto. unfold caller in HEQ.
                unfold def_dr_transf. rewrite HEQ. apply define_insert. auto. }
        - inv MS.
          + exists (State s1 fprev next0 (rm#retreg0<-retval) ms). split. (* ms_same *)
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto. agreeb.
            * apply refl_match. auto. apply regmap_eq_insert. auto.
          + exists (State (Stackframe retreg caller next rm_r0 ::s1) callee retlbl_e (rm_e # retreg_e <- retval) ms). split. (* ms_callee *)
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto. agreeb.
            * apply callee_match; auto.
              apply rm_agree_shift_insert. auto. apply shift_rm_insert. auto.
          + exists (State s1 caller next0 (rm_r0 # retreg0 <- retval) ms). split. (* ms_caller *)
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto. agreeb.
            * apply caller_match; auto. apply rm_agree_insert. auto.
          + destruct tgt as [fidtgt lbltgt]. simpl. simpl in FINDBASE. (* ms_deopt *)
            destruct UPDATE with retval as [rmdeopt UPDATE']. destruct UPDATE'.
            exists (State (synth++s1) (*no*) fprev lbltgt rmdeopt ms). split.
            * left. eapply plus_two.
              ** apply nd_exec_lowered. eapply exec_Return; eauto. agreeb.
              ** { eapply nd_exec_Framestate_deopt. econstructor.
                   - apply FS_CODE.
                   - apply FINDBASE.
                   - auto.
                   - apply SYNTH. }
              ** auto.
            * apply refl_match; auto. apply match_app. auto.
        - inv MS. exists (Final retval ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Return_Final; eauto. agreeb.
          + apply final_match.
        - exists (State stk caller next0 rm_r ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Printexpr; eauto. agreeb.
          + apply caller_match; auto.
            eapply def_analyze_correct; eauto. simpl. auto.
            unfold caller in HEQ. unfold def_dr_transf. rewrite HEQ. auto.
        - exists (State stk caller next0 rm_r ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Printstring; eauto.
          + apply caller_match; auto.
            eapply def_analyze_correct; eauto. simpl. auto.
            unfold caller in HEQ. unfold def_dr_transf. rewrite HEQ. auto.
        - exists (State stk caller next0 rm_r newms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Store; eauto. clear EVAL_AD. agreeb.
            eapply agree_exprb; eauto. eapply is_caller_expr; unfold srv; eauto. simpl.
            right. left. auto.
          + apply caller_match; auto.
            eapply def_analyze_correct; eauto. simpl. auto.
            unfold caller in HEQ. unfold def_dr_transf. rewrite HEQ. auto.
        - exists (State stk caller next0 (rm_r#reg<-val) ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Load; eauto. agreeb.
          + apply caller_match; auto.
            eapply def_analyze_correct; eauto. simpl. auto.
            unfold caller in HEQ. unfold def_dr_transf. rewrite HEQ. apply define_insert. auto.
            apply rm_agree_insert. auto.
        - exists (State stk caller next0 rm_r ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_holds; eauto. agreeb.
          + apply caller_match; auto.
            eapply def_analyze_correct; eauto. simpl. auto.
            unfold caller in HEQ. unfold def_dr_transf. rewrite HEQ. auto.
        - eapply agree_regmapb in UPDATE; eauto.
          2: { eapply is_caller_varmap_assume; eauto. unfold srv. auto. }
          eapply agree_synthb in SYNTH; eauto.
          2: { eapply is_caller_synth_list_assume; eauto. unfold srv. auto. }
          simpl in FINDF. rewrite <- base_version_unchanged in FINDF. apply synth_frame_unchanged in SYNTH.
          exists (State (synth++stk) newver la newrm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_fails; eauto. agreeb.
          + apply refl_match. apply match_app. auto. apply regmap_eq_refl. }
      * inv DEOPT_COND. simpl in FINDF. rewrite <- base_version_unchanged in FINDF.
        apply synth_frame_unchanged in SYNTH. eapply caller_code_preserved in HEQ; eauto.
        eapply agree_regmapb in UPDATE; eauto.
        2: { eapply is_caller_varmap_fs; eauto. unfold srv. auto. }
        eapply agree_synthb in SYNTH; eauto.
        2: { eapply is_caller_synth_list_fs; eauto. unfold srv. auto. }
        exists (State stk caller next0 rm_r ms). split.
        ** left. apply plus_one. eapply nd_exec_Framestate_go_on. econstructor; eauto.
        ** apply caller_match; auto.
           eapply def_analyze_correct; eauto. simpl. auto.
           unfold caller in HEQ. unfold def_dr_transf. rewrite HEQ. auto.
      * inv DEOPT_COND. simpl in FINDF. rewrite <- base_version_unchanged in FINDF.
        apply synth_frame_unchanged in SYNTH. eapply caller_code_preserved in HEQ; eauto.
        eapply agree_regmapb in UPDATE; eauto.
        2: { eapply is_caller_varmap_fs; eauto. unfold srv. auto. }
        eapply agree_synthb in SYNTH; eauto.
        2: { eapply is_caller_synth_list_fs; eauto. unfold srv. auto. }
        exists (State (synth++stk) newver la newrm ms). split.
        ** left. apply plus_one. eapply nd_exec_Framestate_deopt. econstructor; eauto.
        ** apply refl_match; auto. apply match_app. auto. apply regmap_eq_refl.


    + rewrite OPT0 in OPT. inv OPT. (* callee_match *)
      assert (CALLERCALL: caller_lbl (max_lbl_code (ver_code caller)) call_lbl).
      { eapply is_caller_lbl; eauto. }
      inv STEP.
      { inv STEP0; eapply callee_code_preserved in CODE as [i' [CODESRC INLINE_INSTR]]; eauto.
        - destruct i'; inv INLINE_INSTR.
          exists (State (Stackframe retreg caller next rm_r::stk) callee l0 rm_e ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Nop; eauto.
          + apply callee_match; auto.
        - destruct i'; inv INLINE_INSTR.
          + exists (State (Stackframe retreg caller next rm_r::stk) callee l0 (rm_e#r<-v) ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Op; eauto.
              apply safe_step in SAFE as [s' [t STEPSRC]].
              inv STEPSRC; try inv DEOPT_COND; try inv STEP; rewrite CODESRC in CODE; inv CODE.
              assert (v0=v) by (eapply shift_exprb; eauto). subst. auto.
            * apply callee_match; auto. apply rm_agree_shift_insert. auto. apply shift_rm_insert. auto.
          + (* Return replaced, going back to caller_match *)
            exists (State stk caller next0 (rm_r#reg<-v) ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
              apply safe_step in SAFE as [s' [t STEPSRC]].
              inv STEPSRC; try inv DEOPT_COND; try inv STEP; rewrite CODESRC in CODE; inv CODE.
              assert (retval=v) by (eapply shift_exprb; eauto). subst. auto.
            * apply caller_match; auto.
              { eapply def_analyze_correct. apply DEFS. apply CALL_CODE. simpl. auto.
                unfold def_dr_transf. unfold caller in CALL_CODE. rewrite CALL_CODE. apply define_insert. auto. }
              apply rm_agree_insert. auto.
        - destruct i'; inv INLINE_INSTR. apply safe_step in SAFE as [s' [t STEPSRC]].
          inv STEPSRC; try inv DEOPT_COND; try inv STEP; rewrite CODESRC in CODE; inv CODE.
          assert (shift_rm (max_reg_code (ver_code caller)) newrm0 newrm) by (eapply shift_movelistb; eauto).
          exists (State (Stackframe retreg caller next rm_r::stk) callee next0 newrm0 ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Move; eauto.
          + apply callee_match; auto. eapply rm_agree_shift_insert_ml; eauto.
        - destruct i'; inv INLINE_INSTR.
          exists (State (Stackframe retreg caller next rm_r::stk) callee (pc_cond v l0 l1) rm_e ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Cond; eauto.
            fold srv in EVAL. unfold shift_expr in EVAL. apply safe_step in SAFE as [s' [t STEPSRC]].
            inv STEPSRC; try inv DEOPT_COND; try inv STEP; rewrite CODESRC in CODE; inv CODE.
            assert (v0=v) by (eapply shift_exprb; eauto). subst. auto.
          + rewrite <- shift_pc_cond. apply callee_match; auto.
        - destruct i'; inv INLINE_INSTR.
          poseq_destr fid0 fidoptim; simpl in FINDF.
          + erewrite find_function_same in FINDF; eauto. inv FINDF. (* calling optimized caller function *)
            exists (State (Stackframe r callee l1 rm_e ::(Stackframe retreg caller next rm_r::stk)) (current_version caller_f) (ver_entry (current_version caller_f)) newrm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
              apply safe_step in SAFE as [s' [t STEPSRC]].
              inv STEPSRC; try inv DEOPT_COND; try inv STEP; rewrite CODESRC in CODE; inv CODE.
              assert (valist0=valist) by (eapply shift_listb; eauto). subst. auto.
            * rewrite current_version_same. rewrite SAME_ENTRY. apply caller_match; auto.
              apply ms_callee; auto. eapply def_analyze_init; eauto. apply rm_agree_refl.
          + rewrite <- find_function_unchanged in FINDF; auto. (* calling any other function *)
            exists (State (Stackframe r callee l1 rm_e :: (Stackframe retreg caller next rm_r::stk)) (current_version func) (ver_entry (current_version func)) newrm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
              apply safe_step in SAFE as [s' [t STEPSRC]].
              inv STEPSRC; try inv DEOPT_COND; try inv STEP; rewrite CODESRC in CODE; inv CODE.
              assert (valist0=valist) by (eapply shift_listb; eauto). subst. auto.
            * apply refl_match. apply ms_callee; auto. apply regmap_eq_refl.
        - destruct i'; inv INLINE_INSTR.      (* all returns have been replaced *)
        - destruct i'; inv INLINE_INSTR.
        - destruct i'; inv INLINE_INSTR.
          exists (State (Stackframe retreg caller next rm_r::stk) callee l0 rm_e ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Printexpr; eauto.
            apply safe_step in SAFE as [s' [t STEPSRC]].
            inv STEPSRC; try inv DEOPT_COND; try inv STEP; rewrite CODESRC in CODE; inv CODE.
            assert (printval0=printval) by (eapply shift_exprb; eauto). subst. auto.
          + apply callee_match; auto.
        - destruct i'; inv INLINE_INSTR.
          exists (State (Stackframe retreg caller next rm_r::stk) callee l0 rm_e ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Printstring; eauto.
          + apply callee_match; auto.
        - destruct i'; inv INLINE_INSTR.
          exists (State (Stackframe retreg caller next rm_r::stk) callee l0 rm_e newms). split.
          + left. apply plus_one. apply nd_exec_lowered. apply safe_step in SAFE as [s' [t STEPSRC]].
            inv STEPSRC; try inv DEOPT_COND; try inv STEP; rewrite CODESRC in CODE; inv CODE.
            assert (val0=val) by (eapply shift_exprb; eauto). subst.
            assert (addr0=addr) by (eapply shift_exprb; eauto). subst.
            eapply exec_Store; eauto.
          + apply callee_match; auto.
        - destruct i'; inv INLINE_INSTR.
          exists (State (Stackframe retreg caller next rm_r::stk) callee l0 (rm_e#r<-val) ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Load; eauto.
            apply safe_step in SAFE as [s' [t STEPSRC]].
            inv STEPSRC; try inv DEOPT_COND; try inv STEP; rewrite CODESRC in CODE; inv CODE.
            assert (addr0=addr) by (eapply shift_exprb; eauto). subst. auto.
          + apply callee_match; auto. apply rm_agree_shift_insert. auto. apply shift_rm_insert. auto.
        - destruct i'; inv INLINE_INSTR.
          exists (State (Stackframe retreg caller next rm_r::stk) callee l2 rm_e ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
            apply safe_step in SAFE as [s' [t STEPSRC]].
            inv STEPSRC; try inv DEOPT_COND; try inv STEP; rewrite CODESRC in CODE; inv CODE.
            auto. assert (false=true) by (eapply shift_listexprb; eauto). inv H.
          + apply callee_match; auto.
        - destruct i'; inv INLINE_INSTR.
          apply safe_step in SAFE as [s' [t STEPSRC]].
          inv STEPSRC; try inv DEOPT_COND; try inv STEP; rewrite CODESRC in CODE; inv CODE.
          assert (true=false) by (eapply shift_listexprb; eauto). inv H.
          assert (newrm0=newrm) by (eapply shift_deoptb; eauto). subst.
          simpl in FINDF. rewrite <- base_version_unchanged in FINDF. simpl in FINDF0.
          rewrite FINDF0 in FINDF. inv FINDF.  apply synth_frame_unchanged in SYNTH.
          apply synthesized_app in SYNTH. destruct SYNTH as [s_inl [s_er [APP [SYNTH1 SYNTH2]]]].
          simpl in SYNTH0. assert (synth0=s_inl) by (eapply shift_synthb; eauto). subst.
          exists (State (s_inl++(Stackframe retreg caller next rm_r::stk)) newver la0 newrm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
          + apply refl_match. rewrite <- app_assoc. apply match_app.
            assert (sl=nil).    (* right now, nested inlined should be done depth first *)
            { unfold check_synth_list in SL_CHECK. destruct sl; auto. inv SL_CHECK. }
            subst. inv SYNTH2. inv SYNTH.
            apply ms_deopt; auto. 2: { intros. constructor. }
            eapply update_deopt_regmap.
            eapply agree_regmapb; eauto.
            eapply is_caller_varmap_fs; eauto. unfold srv; auto. eapply VM_CHECK. apply regmap_eq_refl.
      }
      * inv DEOPT_COND. eapply callee_code_preserved in CODE as [i [CODESRC INLINE_INSTR]]; eauto.
        destruct i; inv INLINE_INSTR.
        apply safe_step in SAFE as [s' [t STEPSRC]].
        assert (H: exists newrm0, update_regmap v rm_e newrm0).
        { inv STEPSRC; try inv DEOPT_COND; try inv STEP; rewrite CODESRC in CODE; inv CODE; eauto. }
        destruct H as [newrm0 UPDATE_SRC].
        assert (newrm0=newrm) by (eapply shift_deoptb; eauto). subst.
        simpl in FINDF. rewrite <- base_version_unchanged in FINDF.
        apply synth_frame_unchanged in SYNTH.
        apply synthesized_app in SYNTH. destruct SYNTH as [s_inl [s_er [APP [SYNTH1 SYNTH2]]]].
        assert (H: exists synth0, synthesize_frame p rm_e l0 synth0).
        { inv STEPSRC; try inv DEOPT_COND; try inv STEP; rewrite CODESRC in CODE; inv CODE; eauto. }
        destruct H as [synth0 SYNTH_SRC].
        assert (synth0=s_inl) by (eapply shift_synthb; eauto). subst.
        exists (State (Stackframe retreg caller next rm_r::stk) callee l1 rm_e ms). split.
        ** left. apply plus_one. eapply nd_exec_Framestate_go_on.
           econstructor; eauto.
        ** apply callee_match; auto.
      * inv DEOPT_COND. eapply callee_code_preserved in CODE as [i [CODESRC INLINE_INSTR]]; eauto.
        destruct i; inv INLINE_INSTR.
        apply safe_step in SAFE as [s' [t STEPSRC]].
        assert (H: exists newrm0, update_regmap v rm_e newrm0).
        { inv STEPSRC; try inv DEOPT_COND; try inv STEP; rewrite CODESRC in CODE; inv CODE; eauto. }
        destruct H as [newrm0 UPDATE_SRC].
        assert (newrm0=newrm) by (eapply shift_deoptb; eauto). subst.
        simpl in FINDF. rewrite <- base_version_unchanged in FINDF.
        apply synth_frame_unchanged in SYNTH.
        apply synthesized_app in SYNTH. destruct SYNTH as [s_inl [s_er [APP [SYNTH1 SYNTH2]]]].
        assert (H: exists synth0, synthesize_frame p rm_e l0 synth0).
        { inv STEPSRC; try inv DEOPT_COND; try inv STEP; rewrite CODESRC in CODE; inv CODE; eauto. }
        destruct H as [synth0 SYNTH_SRC].
        assert (synth0=s_inl) by (eapply shift_synthb; eauto). subst.
        exists (State (s_inl++(Stackframe retreg caller next rm_r::stk)) newver la newrm ms). split.
        ** left. apply plus_one. eapply nd_exec_Framestate_deopt.
           econstructor; eauto.
        ** apply refl_match. rewrite <- app_assoc. apply match_app.
           assert (sl=nil).    (* right now, nested inlined should be done depth first *)
           { unfold check_synth_list in SL_CHECK. destruct sl; auto. inv SL_CHECK. }
           subst. inv SYNTH2. inv SYNTH.
           apply ms_deopt; auto. 2: { intros. constructor. }
           eapply update_deopt_regmap; eauto.
           eapply agree_regmapb; eauto.
           eapply is_caller_varmap_fs; eauto. unfold srv; auto. apply regmap_eq_refl.
    + inv STEP. inv STEP0.      (* final_match *)
Qed.

