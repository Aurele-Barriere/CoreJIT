(* Liveness Analysis *)

(** Liveness analysis on SpecIR *)
(* Inspired by CompCert analysis over RTL *)

Require Import Coqlib.
Require Import Maps.
Require Import Kildall.
Require Import Lattice.
Require Import specIR.
Require Import Ordered.
Require Import Coq.MSets.MSetPositive.
Require Import ir_properties.

(** A register [r] is live at a point [p] if there exists a path
  from [p] to some instruction that uses [r] as argument,
  and [r] is not redefined along this path.
  Liveness can be computed by a backward dataflow analysis.
  The analysis operates over sets of (live) pseudo-registers. *)

(* Basic definitions over register sets *)
Definition regset: Type := PositiveSet.t.
Lemma regset_eq_refl: forall x, PositiveSet.eq x x.
Proof. apply PositiveSet.eq_equiv. Qed.
Lemma regset_eq_sym: forall x y, PositiveSet.eq x y -> PositiveSet.eq y x.
Proof. apply PositiveSet.eq_equiv. Qed.
Lemma regset_eq_trans: forall x y z, PositiveSet.eq x y -> PositiveSet.eq y z -> PositiveSet.eq x z.
Proof. apply PositiveSet.eq_equiv. Qed.

(* Definition of the lattice used to compute liveness *)
Module LiveFlatRegset <: SEMILATTICE.

Definition t : Type := regset.

Definition eq (x y: t) : Prop :=
  PositiveSet.Equal x y.

Lemma eq_refl: forall x, eq x x.
Proof. apply regset_eq_refl. Qed.

Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof. apply regset_eq_sym. Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof. apply regset_eq_trans. Qed.

Definition beq (x y: t) : bool := PositiveSet.equal x y.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof.
  unfold eq. intros. apply PositiveSet.equal_spec. auto.
Qed.

Definition ge (x y: t) : Prop :=
  PositiveSet.Subset y x.

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof.
  unfold eq, ge. intros x y EQ r IN. apply EQ. auto. 
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge. intros x y z Hxy Hyz r IN. auto. 
Qed.

Definition bot: t := PositiveSet.empty.

Lemma ge_bot: forall x, ge x bot.
Proof.
  unfold ge. intros x r IN. inv IN.
Qed.

Definition lub (x y: t) : t :=
  PositiveSet.union x y.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof.
  intros x y r IN. apply PositiveSet.union_spec. left. auto.
Qed.

Lemma ge_lub_right: forall x y, ge (lub x y) y.
Proof.
  intros x y r IN. apply PositiveSet.union_spec. right. auto.
Qed.

End LiveFlatRegset.

Definition live_abs_dr: Type := regset.

(* Starting the analysis, no registers are live *)
Definition live_entry_abs_dr: live_abs_dr :=
  PositiveSet.empty.

(* Associating a live_abs_dr to each label *)
Definition live_abs_state : Type := PMap.t live_abs_dr.
Definition live_absstate_get (pc:label) (abs:live_abs_state) : live_abs_dr :=
  PMap.get pc abs.

(* Inserting a new live register into an abstract set *)
Definition reg_live (r:reg) (adr:live_abs_dr) : live_abs_dr :=
  PositiveSet.add r adr.

(* Removing a new live register from an abstract set *)
Definition reg_dead (r:reg) (adr:live_abs_dr) : live_abs_dr :=
  PositiveSet.remove r adr.

(* Inserting a list of live registers *)
Fixpoint reg_list_live
             (rl: list reg) (lv: live_abs_dr) {struct rl} : live_abs_dr :=
  match rl with
  | nil => lv
  | r1 :: rs => reg_list_live rs (reg_live r1 lv)
  end.

(* Removing a list of live registers *)
Fixpoint reg_list_dead
             (rl: list reg) (lv: live_abs_dr) {struct rl} : live_abs_dr :=
  match rl with
  | nil => lv
  | r1 :: rs => reg_list_dead rs (reg_dead r1 lv)
  end.

(* Various operations on regsets, used in transfer function *)
Definition expr_live (expr: expr) (after: live_abs_dr): live_abs_dr :=
  match expr with
  | Binexpr binop op1 op2 =>
    match (op1,op2) with
    | (Reg r1, Reg r2) => reg_live r1 (reg_live r2 after)
    | (Reg r1, _) => reg_live r1 after
    | (_, Reg r2) => reg_live r2 after
    | _ => after
    end
  | Unexpr unop op =>
    match op with
    | Reg r => reg_live r after
    | _ => after
    end
  end.

Fixpoint expr_list_live (exl: list expr) (after: live_abs_dr): live_abs_dr :=
  match exl with
  | nil => after
  | e::t => expr_live e (expr_list_live t after)
  end.

Fixpoint movelist_live (l: movelist) (after: live_abs_dr): live_abs_dr :=
  match l with
  | nil => after
  | (_,e)::t => expr_live e (movelist_live t after)
  end.

Fixpoint movelist_dead (l: movelist) (after: live_abs_dr): live_abs_dr :=
  match l with
  | nil => after
  | (r,_)::t => reg_dead r (movelist_dead t after)
  end.

Definition varmap_live (vm: varmap) (after: live_abs_dr): live_abs_dr :=
  (* Same thing as movelist *)
  movelist_live vm after.

Definition varmap_dead (vm: varmap) (after: live_abs_dr): live_abs_dr :=
  (* Same thing as movelist *)
  movelist_dead vm after.

Fixpoint synth_live (sl: list synth_frame) (after: live_abs_dr): live_abs_dr :=
  match sl with
  | nil => after
  | (_,_,_,vm)::t => varmap_live vm (synth_live t after)
  end.

Fixpoint synth_dead (sl: list synth_frame) (after: live_abs_dr): live_abs_dr :=
  match sl with
  | nil => after
  | (_,_,_,vm)::t => varmap_dead vm (synth_dead t after)
  end.

(** Here is the transfer function for the dataflow analysis.
  Since this is a backward dataflow analysis, it takes as argument
  the abstract register set ``after'' the given instruction,
  i.e. the registers that are live after; and it returns as result
  the abstract register set ``before'' the given instruction,
  i.e. the registers that must be live before.
  The general relation between ``live before'' and ``live after''
  an instruction is that a register is live before if either
  it is one of the arguments of the instruction, or it is not the result
  of the instruction and it is live after. *)
(* The transf function that updates live_abs_dr *)
Definition live_dr_transf
            (c: code) (pc: positive) (after: live_abs_dr) : live_abs_dr :=
  match c!pc with
  | None =>
    PositiveSet.empty
  | Some i =>
      match i with
      | Nop oh next =>
        after
      | Op expr reg next =>
        expr_live expr (reg_dead reg after)
      | Move l next =>
        movelist_live l (movelist_dead l after)
      | Call f exl retreg next =>
        expr_list_live exl (reg_dead retreg after)
      | IReturn expr =>
        expr_live expr after
      | Cond expr iftrue iffalse =>
        expr_live expr after
      | Store expr1 expr2 next =>
        expr_live expr1 (expr_live expr2 after)
      | Load expr reg next =>
        expr_live expr (reg_dead reg after)
      | Printexpr expr next =>
        expr_live expr after
      | Printstring s next =>
        after
      | Framestate  (f,l) vm sl next =>
        varmap_live vm (synth_live sl after)
      | Assume le (f,l) vm sl next =>
        expr_list_live le (varmap_live vm (synth_live sl after))
      | Fail s =>
        after
      end
  end.

(** The liveness analysis is then obtained by instantiating the
  general framework for backward dataflow analysis provided by
  module [Kildall].  *)
Module DS := Backward_Dataflow_Solver (LiveFlatRegset) (NodeSetBackward).

Definition list_entries (f: version) : list (label * live_abs_dr) :=
  ((ver_entry f), PositiveSet.empty)::nil.

Definition liveness_analyze (f: version): option live_abs_state :=
  DS.fixpoint (PTree.map1 instr_succ (ver_code f)) (live_dr_transf (ver_code f)) (list_entries f).

(** Basic property of the liveness information computed by [analyze]. *)
Lemma liveness_successor:
  forall f live n i s,
  liveness_analyze f = Some live ->
  (ver_code f)!n = Some i ->
  In s (instr_succ i) ->
  PositiveSet.Subset (live_dr_transf (ver_code f) s (live_absstate_get s live)) (live_absstate_get n live).
Proof.
  unfold liveness_analyze. intros. eapply DS.fixpoint_solution; eauto.
  unfold "!!!". rewrite PTree.gmap1. rewrite H0. simpl. auto.
Qed.

(* Basic inclusions of regsets *)
Lemma expr_live_subset:
  forall e rs, PositiveSet.Subset rs (expr_live e rs).
Proof.
  unfold PositiveSet.Subset. unfold expr_live. intros.
  destruct e; destruct o; try destruct o0;
    repeat (apply PositiveSet.add_spec; right); auto.
Qed.

Lemma expr_list_live_subset:
  forall exl rs, PositiveSet.Subset rs (expr_list_live exl rs).
Proof.
  unfold PositiveSet.Subset. induction exl; intros; auto.
  simpl. apply expr_live_subset. auto.
Qed.

Lemma movelist_subset:
  forall ml rs, PositiveSet.Subset rs (movelist_live ml rs).
Proof.
  unfold PositiveSet.Subset. induction ml; intros.
  - simpl. apply H.
  - simpl. destruct a. apply expr_live_subset. apply IHml. apply H.
Qed.

Lemma varmap_subset:
  forall vm rs, PositiveSet.Subset rs (varmap_live vm rs).
Proof.
  apply movelist_subset.
Qed.

Lemma synth_subset:
  forall sl rs, PositiveSet.Subset rs (synth_live sl rs).
Proof.
  unfold PositiveSet.Subset. induction sl; intros.
  - simpl. apply H.
  - simpl. destruct a; destruct p; destruct d. apply varmap_subset.
    apply IHsl. apply H.
Qed.

Lemma in_or_not:
  forall (l:label) l_fs,
    In l l_fs \/ ~ In l l_fs.
Proof.
  intros l l_fs. induction l_fs.
  - right. unfold not; intros. inv H.
  - poseq_destr a l.
    + left. simpl. left. auto.
    + destruct IHl_fs; [left | right]; simpl; try (right; auto).
      unfold not. intros [EQ | IN]; auto. 
Qed.

(* Two regmaps agree on a regset iff they have the same values
   on the registers of the regset (may be None) *)
Definition agree (rm1 rm2:reg_map) (adr:live_abs_dr) :=
  forall r:reg, PositiveSet.In r adr -> rm1 # r = rm2 # r.

Lemma agree_refl:
  forall rs rm,
    agree rm rm rs.
Proof.
  unfold agree. intros. auto.
Qed.

Lemma agree_sym:
  forall rs rm1 rm2,
    agree rm1 rm2 rs ->
    agree rm2 rm1 rs.
Proof.
  unfold agree. intros. symmetry. auto.
Qed.

Lemma agree_trans:
  forall rs rm1 rm2 rm3,
    agree rm1 rm2 rs ->
    agree rm2 rm3 rs ->
    agree rm1 rm3 rs.
Proof.
  unfold agree. intros. rewrite H; auto.
Qed.

Lemma agree_subset:
  forall rs1 rs2 rms rmo,
    PositiveSet.Subset rs1 rs2 ->
    agree rms rmo rs2 ->
    agree rms rmo rs1.
Proof.
  unfold agree. intros. auto.
Qed.

(* Liveness transfer preserves agree *)
Lemma agree_transfer:
  forall live rms rmo f pc pc' i,
    liveness_analyze f = Some live ->
    (ver_code f)!pc = Some i ->
    In pc' (instr_succ i) ->
    agree rms rmo (live!!pc) ->
    agree rms rmo (live_dr_transf (ver_code f) pc' (live!!pc')).
Proof.
  intros. apply agree_subset with (live!!pc); auto.
  eapply liveness_successor; eauto.
Qed.

(* The following lemmas express the fact that agreeing on the regset obtained 
   after adding registers implies agreeing on the original regset 
   (which contains less registers) *)
Lemma expr_live_agree:
  forall e rs rms rmo,
    agree rms rmo (expr_live e rs) ->
    agree rms rmo rs.
Proof.
  intros. eapply agree_subset; eauto. apply expr_live_subset.
Qed.

Lemma expr_list_live_agree:
  forall exl rs rms rmo,
    agree rms rmo (expr_list_live exl rs) ->
    agree rms rmo rs.
Proof.
  intros. eapply agree_subset; eauto. apply expr_list_live_subset.
Qed.

Lemma movelist_live_agree:
  forall ml rs rms rmo,
    agree rms rmo (movelist_live ml rs) ->
    agree rms rmo rs.
Proof.
  intros. eapply agree_subset; eauto. apply movelist_subset.
Qed.

Lemma varmap_live_agree:
  forall vm rs rms rmo,
    agree rms rmo (varmap_live vm rs) ->
    agree rms rmo rs.
Proof.
  intros. eapply agree_subset; eauto. apply varmap_subset.
Qed.

Lemma synth_live_agree:
  forall sl rs rms rmo,
    agree rms rmo (synth_live sl rs) ->
    agree rms rmo rs.
Proof.
  intros. eapply agree_subset; eauto. apply synth_subset.
Qed.

(* If two regmaps agree on the registers used for the evaluation of e, 
   then e evaluates to the same value in both regmaps *)
Lemma agree_eval_expr:
  forall e v rs rms rmo ,
    agree rms rmo (expr_live e rs) ->
    eval_expr e rms v ->
    eval_expr e rmo v.
Proof.
  intros. inv H0; inv EVAL; constructor; econstructor; eauto.
  - inv EVALL; constructor. unfold agree in H. rewrite <- H; auto.
    simpl. destruct o2; apply PositiveSet.add_spec; left; auto.
  - inv EVALR; constructor. unfold agree in H. rewrite <- H; auto.
    simpl. destruct o1; apply PositiveSet.add_spec; try (left; reflexivity).
    right. apply PositiveSet.add_spec. left. auto.
  - inv EVAL0; constructor. unfold agree in H. rewrite <- H; auto.
    simpl. apply PositiveSet.add_spec. left. auto.
Qed.

(* If two regmaps agree on the registers used for the evaluation of 
   the list of expressions [le], then [le] evaluates to the same boolean value
   in both regmaps *)
Lemma agree_eval_list_expr:
  forall rs rm1 rm2 le b,
    agree rm1 rm2 (expr_list_live le rs) ->
    eval_list_expr le rm1 b ->
    eval_list_expr le rm2 b.
Proof.
  intros. generalize dependent b. induction le; intros; inv H0; try constructor.
  - eapply agree_eval_expr in EVAL; eauto.
  - eapply agree_eval_expr in EVALH; eauto.
    econstructor; eauto. apply IHle; auto.
    unfold agree in *. intros. apply H. simpl.
    eapply expr_live_subset; eauto.
Qed.

(* If two regmaps agree on the registers used for the evaluation of 
   the list of expressions [le], then each expression of [le] evaluates to the same value
   in both regmaps *)
Lemma agree_eval_list:
  forall rs rm1 rm2 le lv,
    agree rm1 rm2 (expr_list_live le rs) ->
    eval_list le rm1 lv ->
    eval_list le rm2 lv.
Proof.
  intros. generalize dependent lv.
  induction le; intros; inv H0; try constructor.
  - eapply agree_eval_expr in EVALH; eauto.
  - apply IHle; auto. eapply agree_subset; eauto. apply expr_live_subset.
Qed.

(* Auxiliary lemmas on movelists *)
(* If a register is not assigned by a movelist, it contains the same value 
   before and after the update *)
Lemma not_use_movelist:
  forall ml r rm rmu,
    ~(In r (map fst ml)) ->
    update_movelist ml rm rmu ->
    rm ! r = rmu ! r.
Proof.
  induction ml; intros.
  - inv H0. auto.
  - inv H0. poseq_destr r r0.
    + simpl in H. unfold not in H.
      exfalso. apply H. left. auto. 
    + rewrite PTree.gso; auto. simpl in H.
      eapply Classical_Prop.not_or_and in H as [NEQ NIN]. apply IHml; auto.
Qed.

(* If a register is assigned by a movelist and two regmaps agree on all the
   registers whose value is needed to evaluate all the expressions of
   the movelist, then we can decompose the movelist appropriately *)
Lemma reg_in_movelist:
  forall ml r rs rm1 rm2,
    agree rm1 rm2 (movelist_live ml rs) ->
    In r (map fst ml) ->
    exists ml1 ml2 e rs',
      ml = ml1 ++ (r,e)::ml2 /\ ~(In r (map fst ml1)) /\
      agree rm1 rm2 (expr_live e rs').
Proof.
  induction ml; intros; inv H0.
  - simpl in H. destruct a. exists nil, ml, e, (movelist_live ml rs).
    split; auto.
  - simpl in H. destruct a.
    apply IHml with r rs rm1 rm2 in H1 as [ml1 [ml2 [e' [rs' [EQ [NIN AGREE]]]]]].
    2: { eapply expr_live_agree. eauto. }
    poseq_destr r r0.
    + exists nil, (ml1 ++ (r0,e')::ml2), e, (movelist_live (ml1 ++ (r0, e') :: ml2) rs).
      split; auto.
    + exists ((r0,e)::ml1), ml2, e', rs'. subst.
      split; auto; try split; auto.
      simpl. intros [EQ' | IN]; subst; auto.
Qed.

(* If we assign a register [r] with a movelist, and two regmaps agree on the 
   registers used by the expression assigned to [r], then they agree on [r]
   after the update no matter what was the value before *)
Lemma use_movelist:
  forall ml1 ml2 ml r e rs rm1 rm1u rm2 rm2u,
    ml = ml1 ++ (r,e)::ml2 ->
    ~(In r (map fst ml1)) ->
    agree rm1 rm2 (expr_live e rs) ->
    update_movelist ml rm1 rm1u ->
    update_movelist ml rm2 rm2u ->
    rm1u ! r = rm2u ! r.
Proof.
  induction ml1.
  - intros. inv H2; inv H4.
    inv H3. rewrite PTree.gss. rewrite PTree.gss. f_equal.
    eapply agree_eval_expr in EVAL; eauto.
    eapply eval_expr_determ; eauto.
  - intros. inv H2; inv H4.
    inv H3. assert (r <> r0).
    { intros contra. apply H0. simpl. left. auto. }
    rewrite PTree.gso; auto. rewrite PTree.gso; auto.
    eapply IHml1; eauto. intros contra. simpl in H0.
    apply H0. right. auto.
Qed.

(* Two agreeing regmaps still agree after having the same update *)
Lemma agree_update_movelist_aux:
  forall ml rs rm1 rm2 rm1u rm2u,
    agree rm1 rm2 (movelist_live ml rs) ->
    update_movelist ml rm1 rm1u ->
    update_movelist ml rm2 rm2u ->
    agree rm1u rm2u (movelist_live ml rs).
Proof.
  induction ml; intros; inv H0; inv H1; auto.
  unfold agree. intros.
  simpl in H0. simpl in H. poseq_destr r r0.
  - repeat rewrite PTree.gss. f_equal.
    eapply agree_eval_expr in EVAL; eauto.
    eapply eval_expr_determ; eauto.
  - repeat (rewrite PTree.gso; auto).
    assert (In r0 (map fst ml) \/ ~(In r0 (map fst ml))) as [IN' | NIN'] by (apply in_or_not).
    + eapply reg_in_movelist in IN' as [ml1 [ml2 [e' [rs' [EQ [NIN'' AGREE]]]]]]; eauto.
      * eapply use_movelist; eauto.
      * eapply expr_live_agree; eauto.
    + assert (rm1 ! r0 = rm' ! r0).
      { eapply not_use_movelist; eauto. }
      assert (rm2 ! r0 = rm'0 ! r0).
      { eapply not_use_movelist; eauto. }
      rewrite <- H1. rewrite <- H2. apply H. apply H0.
Qed.

Lemma agree_update_movelist:
  forall rs rm1 rm2 rm2u ml,
    agree rm1 rm2 (movelist_live ml rs) ->
    update_movelist ml rm2 rm2u ->
    exists rm1u,
      update_movelist ml rm1 rm1u /\
      agree rm1u rm2u (movelist_live ml rs).
Proof.
  intros. generalize dependent rm2u. induction ml; intros; inv H0.
  - exists rm1. split; auto. constructor.
  - assert (UPDATE':= UPDATE). apply IHml in UPDATE as [rm1u [UPDATE EQ]].
    2: { unfold agree in *. intros. apply H. simpl.
         apply expr_live_subset. auto. }
    apply agree_sym in H.
    assert (EVAL':=EVAL).
    eapply agree_eval_expr in EVAL; eauto.
    exists (rm1u#r<-v). split; try constructor; eauto.
    apply agree_sym. eapply agree_update_movelist_aux; eauto; econstructor; eauto.
Qed.

Lemma agree_update_regmap:
  forall rs rm1 rm2 newrm vm,
    agree rm1 rm2 (varmap_live vm rs) ->
    update_regmap vm rm2 newrm ->
    update_regmap vm rm1 newrm.
Proof.
  intros. generalize dependent newrm.
  induction vm; intros; inv H0; try constructor.
  apply agree_sym in H. eapply agree_eval_expr in EVAL; eauto.
  apply IHvm in UPDATE; auto. simpl in H.
  eapply expr_live_agree. eauto.
Qed.

Lemma agree_synthesize_frame:
  forall rs rm1 rm2 p sl stack,
    agree rm1 rm2 (synth_live sl rs) ->
    synthesize_frame p rm2 sl stack ->
    synthesize_frame p rm1 sl stack.
Proof.
  intros. generalize dependent stack.
  induction sl; intros; inv H0; try constructor; auto.
  - eapply agree_update_regmap in UPDATE; eauto.
  - apply IHsl; auto. simpl in H.
    eapply varmap_live_agree. eauto.
Qed.

(* It is sufficient to agree on all the registers of [rs] excepted [reg]
   before an assignation provided we assign the same value to [reg]
   on both sides *)
Lemma agree_insert_dead:
  forall rs rm rm_opt reg v,
    agree rm rm_opt (reg_dead reg rs) ->
    agree (rm # reg <- v) (rm_opt # reg <- v) rs.
Proof.
  intros. unfold agree in *.
  intros r IN. poseq_destr r reg.
  - rewrite PTree.gss. rewrite PTree.gss. auto.
  - rewrite PTree.gso; auto. rewrite PTree.gso; auto. apply H.
    apply PositiveSet.remove_spec; split; auto.
Qed.

(* updating the rm on both sides *)
Lemma agree_insert:
  forall rs rm rm_opt reg v,
    agree rm rm_opt rs ->
    agree (rm # reg <- v) (rm_opt # reg <- v) rs.
Proof.
  intros. apply agree_subset with (reg_dead reg rs) rs rm rm_opt in H.
  - apply agree_insert_dead. auto.
  - intros r IN. apply PositiveSet.remove_spec in IN as [IN _]. auto.
Qed.

Lemma agree_movelist_live:
  forall ml rs rs' rms rmo,
    agree rms rmo (movelist_live ml rs) ->
    agree rms rmo rs ->
    agree rms rmo rs' ->
    agree rms rmo (movelist_live ml rs').
Proof.
  induction ml; intros; auto.
  simpl. destruct a. simpl in H. intros r' IN.
  destruct e; destruct o; try destruct o0; simpl in *;
    try (apply (IHml rs rs' rms rmo); assumption); poseq_destr r' r0;
      try (apply H; apply PositiveSet.add_spec; left; reflexivity).
  - poseq_destr r' r1.
    + apply H. apply PositiveSet.add_spec. right.
      apply PositiveSet.add_spec. left. auto.
    + apply (IHml rs rs' rms rmo); auto.
      * eapply agree_subset; try apply H.
        intros reg IN'. repeat (apply PositiveSet.add_spec; right; auto).
      * repeat (apply PositiveSet.add_spec in IN as [contra | IN]; auto;
                try contradiction).
  - apply (IHml rs rs' rms rmo); auto.
    + eapply agree_subset; try apply H.
      intros reg IN'. apply PositiveSet.add_spec. right. auto.
    + apply PositiveSet.add_spec in IN as [contra | IN]; auto. contradiction.
  - apply (IHml rs rs' rms rmo); auto.
    + eapply agree_subset; try apply H.
      intros reg IN'. apply PositiveSet.add_spec. right. auto.
    + apply PositiveSet.add_spec in IN as [contra | IN]; auto. contradiction.
  - apply (IHml rs rs' rms rmo); auto.
    + eapply agree_subset; try apply H.
      intros reg IN'. apply PositiveSet.add_spec. right. auto.
    + apply PositiveSet.add_spec in IN as [contra | IN]; auto. contradiction.
Qed.

Lemma movelist_reg_dead_subset:
  forall ml r rs,
    PositiveSet.Subset (movelist_dead ml (reg_dead r rs)) (reg_dead r (movelist_dead ml rs)).
Proof.
  induction ml; intros.
  - simpl. intros r' IN. auto.
  - simpl. destruct a. intros r' IN. poseq_destr r' r0.
    + apply PositiveSet.remove_spec in IN as [_ contra]. destruct contra. auto.
    + poseq_destr r' r.
      * apply PositiveSet.remove_spec in IN as [IN _]. apply IHml in IN.
        apply PositiveSet.remove_spec in IN as [_ contra]. destruct contra. auto.
      * repeat (apply PositiveSet.remove_spec; split; auto).
        apply PositiveSet.remove_spec in IN as [IN _]. apply IHml in IN.
        apply PositiveSet.remove_spec in IN as [IN _]. auto.
Qed.

(* Before an update_movelist, it is sufficient to agree on all the registers
   of [rs] excepted the registers assigned by the movelist *)
Lemma agree_movelist_dead:
  forall ml rs rms rmsu rmo rmou,
    agree rms rmo (movelist_live ml (movelist_dead ml rs)) ->
    update_movelist ml rms rmsu ->
    update_movelist ml rmo rmou ->
    agree rmsu rmou rs.
Proof.
  induction ml; intros; inv H0; inv H1; simpl in H; auto.
  simpl in H. eapply agree_eval_expr in EVAL; eauto.
  eapply eval_expr_determ in EVAL0; eauto.
  inv EVAL0. apply agree_insert_dead.
  eapply IHml; eauto.
  apply agree_subset with
      (movelist_live ml (reg_dead r (movelist_dead ml rs)))
      (expr_live e (movelist_live ml (reg_dead r (movelist_dead ml rs))))
      rms rmo in H; try apply expr_live_subset.
  eapply agree_movelist_live; eauto.
  + eapply movelist_live_agree. eauto.
  + eapply agree_subset. apply movelist_reg_dead_subset.
    eapply movelist_live_agree. eauto.
Qed.
