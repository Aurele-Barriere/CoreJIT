(* Defined Registers ANalysis *)
(* For Assume and Framestate insertion, we need to know the *)
(* exact set of defined registers at some program point *)
(* This analysis tracks defined registers, using Kildall library *)

Require Import specIR.
Require Import Kildall.
Require Import Coq.MSets.MSetPositive.
Require Import Lattice.

(* A set of defined registers *)
Definition regset: Type := PositiveSet.t.
Lemma regset_eq_refl: forall x, PositiveSet.eq x x.
Proof. apply PositiveSet.eq_equiv. Qed.
Lemma regset_eq_sym: forall x y, PositiveSet.eq x y -> PositiveSet.eq y x.
Proof. apply PositiveSet.eq_equiv. Qed.
Lemma regset_eq_trans: forall x y z, PositiveSet.eq x y -> PositiveSet.eq y z -> PositiveSet.eq x z.
Proof. apply PositiveSet.eq_equiv. Qed.

(* A Flat Semi-Lattice for sets of defined registers *)
(* Either Bot, a given set, or Top *)
Module FlatRegset <: SEMILATTICE_WITH_TOP.

Inductive t' : Type :=
  | Bot: t'
  | Inj: regset -> t'
  | Top: t'.

Definition t : Type := t'.

Definition eq (x y: t) : Prop :=
  match x with
  | Bot => match y with
          | Bot => True
          | _ => False
          end
  | Top => match y with
          | Top => True
          | _ => False
          end
  | Inj rsx => match y with
              | Inj rsy => PositiveSet.Equal rsx rsy
              | _ => False
              end
  end.

Lemma eq_refl: forall x, eq x x.
Proof. intros.   destruct x; simpl; auto. apply regset_eq_refl. Qed.

Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof. intros. destruct x; destruct y; simpl; auto. simpl in H. apply regset_eq_sym. auto. Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof.
  intros. destruct x; destruct y; destruct z; simpl; auto; simpl in H; simpl in H0.
  inv H. eapply regset_eq_trans; eauto. inv H.
Qed.

Definition beq (x y: t) : bool :=
  match x, y with
  | Bot, Bot => true
  | Inj u, Inj v => if PositiveSet.equal u v then true else false
  | Top, Top => true
  | _, _ => false
  end.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof.
  unfold eq; destruct x; destruct y; simpl; try congruence; intro; auto.
  destruct (PositiveSet.equal r r0) eqn:EQ; auto; inv H. apply PositiveSet.equal_spec. auto.
Qed.

Definition ge (x y: t) : Prop :=
  match x, y with
  | Top, _ => True
  | _, Bot => True
  | Inj a, Inj b => PositiveSet.eq a b
  | _, _ => False
  end.

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof.
  unfold eq, ge. intros. destruct x; destruct y; simpl; auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge; destruct x; destruct y; try destruct z; intuition.
  eapply regset_eq_trans; eauto.
Qed.

Definition bot: t := Bot.

Lemma ge_bot: forall x, ge x bot.
Proof.
  destruct x; simpl; auto.
Qed.

Definition top: t := Top.

Lemma ge_top: forall x, ge top x.
Proof.
  destruct x; simpl; auto.
Qed.

Definition lub (x y: t) : t :=
  match x, y with
  | Bot, _ => y
  | _, Bot => x
  | Top, _ => Top
  | _, Top => Top
  | Inj a, Inj b => if PositiveSet.equal a b then Inj a else Top
  end.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof.
  destruct x; destruct y; simpl; auto. apply regset_eq_refl.
  destruct (PositiveSet.equal r r0); simpl; auto. apply regset_eq_refl.
Qed.

Lemma ge_lub_right: forall x y, ge (lub x y) y.
Proof.
  destruct x; destruct y; simpl; auto. apply regset_eq_refl.
  destruct (PositiveSet.equal r r0) eqn:EQ; simpl; auto. apply PositiveSet.equal_spec. auto.
Qed.

End FlatRegset.


Definition abs_dr: Type := FlatRegset.t.
(* Top means we can't know for sure the set of defined registers *)
(* Inj rs means rs is the set of defined registers at this point *)
(* Bot is the initial value *)

(* At the function entry, we know parameters are defined *)
Fixpoint entry_set (params:list reg): regset :=
  match params with
  | nil => PositiveSet.empty
  | p::params' => PositiveSet.add p (entry_set params')
  end.

Definition entry_abs_dr (params:list reg): abs_dr :=
  FlatRegset.Inj (entry_set params).

Module DS := Dataflow_Solver (FlatRegset) (NodeSetBackward).

(* Associating an abs_dr to each label *)
Definition abs_state : Type := PMap.t abs_dr.
Definition absstate_get (pc:label) (abs:abs_state) : abs_dr :=
  PMap.get pc abs.


(* Inserting a new defined register into an abstract set *)
Definition insert (r:reg) (adr:abs_dr) : abs_dr :=
  match adr with
  | FlatRegset.Top => FlatRegset.Top
  | FlatRegset.Bot => FlatRegset.Inj (PositiveSet.singleton r)
  | FlatRegset.Inj rs => FlatRegset.Inj (PositiveSet.add r rs)
  end.

Fixpoint insert_list (lr:list reg) (adr:abs_dr) : abs_dr :=
  match lr with
  | nil => adr
  | r::lr' => insert r (insert_list lr' adr)
  end.

(* The transf function that updates reg sets *)
Definition dr_transf (c:code) (l:label) (adr:abs_dr) : abs_dr :=
  match c!l with
  | None => adr
  | Some i =>
    match i with
    | Op expr reg next =>
      insert reg adr
    | Move ml next =>
      insert_list (map fst ml) adr
    | Call fid args retreg next =>
      insert retreg adr
    | Load expr reg next =>
      insert reg adr
    | _ => adr                   (* other instructions can't declare registers *)
    end
  end.

Definition defined_regs_analysis (c:code) (params:list reg) (entry:label): option abs_state:=
  DS.fixpoint
    (PTree.map1 instr_succ c)
    (dr_transf c)
    ((entry,(entry_abs_dr params))::nil).


(** * Correctness of the analysis *)

(* Matching abstract reg_sets with a concrete regmap *)
Definition defined (rm:reg_map) (adr:abs_dr) :=
  match adr with
  | FlatRegset.Top => True
  | FlatRegset.Bot => False
  | FlatRegset.Inj rs =>
    forall r, PositiveSet.In r rs <-> exists v, rm # r = Some v
  end.

Lemma mem_empty:
  forall r s, PositiveSet.is_empty s = true -> PositiveSet.mem r s = false.
Proof.
  intros r s H. generalize dependent r. induction s; intros; auto.
  inv H. destruct (negb b) eqn:NEG; inv H1.
  destruct (PositiveSet.is_empty s1) eqn:EMPTY1; inv H0. 
  simpl. destruct r.
  - apply IHs2. auto.
  - apply IHs1. auto.
  - destruct b; auto.
Qed.

(* There might be a simpler way *)
Lemma mem_eq:
  forall r s1 s2,
    PositiveSet.eq s1 s2 ->
    PositiveSet.mem r s2 = PositiveSet.mem r s1.
Proof.
  intros. unfold PositiveSet.eq in H. rewrite <- PositiveSet.equal_spec in H.
  generalize dependent s2. generalize dependent r. induction s1; intros.
  - inv H. simpl. apply mem_empty. auto.
  - destruct s2.
    + inv H. destruct (negb b) eqn:NEG; inv H1. destruct (PositiveSet.is_empty s1_1) eqn:EMPTY; inv H0.
      simpl. destruct r.
      * symmetry. apply mem_empty. auto.
      * symmetry. apply mem_empty. auto.
      * destruct b; inv NEG. auto.
    + simpl in H. simpl. destruct (eqb b b0) eqn:EQ; inv H.
      destruct (PositiveSet.equal s1_1 s2_1) eqn:EQ1; inv H1. destruct r.
      * apply IHs1_2. auto.
      * apply IHs1_1. auto.
      * symmetry. apply eqb_true_iff. auto.
Qed.

Lemma eq_defined:
  forall s1 s2 rm,
    PositiveSet.eq s1 s2 ->
    defined rm (FlatRegset.Inj s2) ->
    defined rm (FlatRegset.Inj s1).
Proof.
  unfold defined, PositiveSet.In. intros s1 s2 rm EQ DEF. intros r. specialize (DEF r).
  apply mem_eq with (r:=r) in EQ. rewrite EQ in DEF. auto.
Qed.

Lemma defined_increasing:
  forall rm adr1 adr2,
    FlatRegset.ge adr1 adr2 ->
    defined rm adr2 ->
    defined rm adr1.
Proof.
  intros rm adr1 adr2 GE DEF.
  destruct adr1; destruct adr2; try inv GE; auto; try inv DEF.
  simpl in GE. eapply eq_defined; eauto. constructor.
Qed.

(* The iterative analysis is correct *)
Lemma analyze_successor:
  forall v params abs pc i pc',
    defined_regs_analysis (ver_code v) params (ver_entry v) = Some abs ->
    (ver_code v) # pc = Some i ->
    In pc' (instr_succ i) ->
    FlatRegset.ge (absstate_get pc' abs) (dr_transf (ver_code v) pc (absstate_get pc abs)).
Proof.
  intros v params abs pc i pc' H H0 H1. unfold defined_regs_analysis in H.
  eapply DS.fixpoint_solution; eauto.
  assert (@PTree.get (list positive) pc (PTree.map1 instr_succ (ver_code v)) = Some (instr_succ i)).
  { rewrite PTree.gmap1. unfold option_map. rewrite H0. auto. }
  unfold successors_list. rewrite H2.
  simpl. auto.
Qed.

Theorem analyze_correct:
  forall v pc i pc' abs params rm,
    defined_regs_analysis (ver_code v) params (ver_entry v) = Some abs ->
    (ver_code v) # pc = Some i ->
    In pc' (instr_succ i) ->
    defined rm (dr_transf (ver_code v) pc (absstate_get pc abs)) ->
    defined rm (absstate_get pc' abs).
Proof.
  intros. eapply analyze_successor in H; eauto.
  eapply defined_increasing; eauto.
Qed.

Lemma analyze_init':
  forall rm params valist,
    specIR.init_regs valist params = Some rm ->
    defined rm (entry_abs_dr params).
Proof.
  intros. unfold entry_abs_dr. simpl. generalize dependent valist. generalize dependent rm.
  induction params; intros.
  - destruct valist; inv H. split; intros; inv H.
    unfold empty_regmap in H0. rewrite PTree.gempty in H0. inv H0.
  - destruct valist; inv H. destruct (init_regs valist params) eqn:INIT; inv H1.
    specialize (IHparams r0 valist INIT r). split; intros.
    + simpl in H. apply PositiveSet.add_spec in H. destruct H.
      * subst. rewrite PTree.gss. eauto.
      * apply IHparams in H. destruct H. poseq_destr a r.
        rewrite PTree.gss; eauto.
        rewrite PTree.gso; auto. eauto.
    + apply PositiveSet.add_spec. fold entry_set. poseq_destr a r.
      * left. auto.
      * right. rewrite PTree.gso in H; auto. apply <- IHparams in H. auto.
Qed.

Theorem analyze_init:
  forall rm v params abs valist,
    defined_regs_analysis (ver_code v) params (ver_entry v) = Some abs ->
    specIR.init_regs valist params = Some rm ->
    defined rm (absstate_get (ver_entry v) abs).
Proof.
  unfold defined_regs_analysis. intros rm v params abs valist FIX INIT.
  assert (A: FlatRegset.ge (absstate_get (ver_entry v) abs) (entry_abs_dr params)).
  { eapply DS.fixpoint_entry; eauto. left. auto. }
  eapply defined_increasing; eauto.
  eapply analyze_init'; eauto.
Qed.

(** * More defined Properties *)
Lemma define_insert:
  forall rm reg v rs,
    defined rm rs ->
    defined rm # reg <- v (insert reg rs).
Proof.
  intros rm reg v rs DEF. destruct rs. inv DEF. 2: simpl; auto.
  simpl in DEF. simpl. intros x.
  split; intros.
  - apply PositiveSet.add_spec in H. destruct H.
    + subst. rewrite PTree.gss. eauto.
    + specialize (DEF x). apply DEF in H. destruct H.
      poseq_destr reg x. rewrite PTree.gss. eauto. rewrite PTree.gso; eauto.
  - apply PositiveSet.add_spec. poseq_destr x reg; auto.
    right. rewrite PTree.gso in H; auto. apply DEF in H. auto.
Qed.

Lemma define_insert_list:
  forall ml rm newrm rs,
    defined rm rs ->
    update_movelist ml rm newrm ->
    defined newrm (insert_list (map fst ml) rs).
Proof.
  unfold update_movelist. intros ml. induction ml; intros; inv H0. auto.
  simpl. apply define_insert. eapply IHml; eauto.
Qed.
