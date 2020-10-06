(* Verification of the Framestate Insertion pass *)
(* The first pass of the dynamic optimizer *)

Require Export specIR.
Require Export framestate_insertion.
Require Export ir_properties.
Require Export internal_simulations.
Require Import Coq.MSets.MSetPositive.
Require Import Lists.SetoidList.
Require Export def_regs.

(** * Regmap equivalence  *)
(* Deoptimizing to the original version gives you a regmap that is not equal to the source one *)
(* not with Coq equality.  *)
(* We define an equivalence over Regmaps here *)
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

(** * Exploiting the def_regs analysis  *)
Lemma Inl_In:
  forall r l, PositiveSet.InL r l <-> In r l.
Proof.
  intros. induction l.
  - split; intros. inv H. inv H. 
  - split; intros.
    + inv H.
      * unfold PositiveSet.E.eq in H1. subst. simpl. left. auto.
      * apply IHl in H1. simpl. right. auto.
    + inv H.
      * constructor. unfold PositiveSet.E.eq. auto.
      * apply InA_cons_tl. apply IHl. auto.
Qed.

Lemma PSin_in:
  forall r rs,
    PositiveSet.In r rs <-> In r (PositiveSet.elements rs).
Proof.
  intros. rewrite <- PositiveSet.elements_spec1.
  apply Inl_In.
Qed.

Lemma nodup_elements:
  forall rs, NoDup (PositiveSet.elements rs).
Proof.
  assert (forall l, NoDupA PositiveSet.E.eq l <-> NoDup l).
  { intros. induction l.
    - split; intros. constructor. constructor.
    - split; intros.
      + inv H. constructor.
        * unfold not. intros. rewrite <- Inl_In in H. contradiction.
        * apply IHl. auto.
      + inv H. constructor.
        * unfold not. intros. rewrite Inl_In in H. contradiction.
        * apply IHl. auto. }
  intros. apply H. apply PositiveSet.elements_spec2w.
Qed.  

Lemma defined_ind:
  forall a l rm,
    NoDup (a::l) ->
    (forall r : positive, In r (a :: l) <-> (exists v : value, rm ! r = Some v)) ->
    (forall r : positive, In r l <-> (exists v, (PTree.remove a rm)!r = Some v)).
Proof.
  intros. split; intros.
  - assert (In r (a::l)) by (right; auto). apply H0 in H2 as [v SOME].
    exists v. rewrite PTree.gro. auto. inv H. poseq_destr r a; auto.
  - destruct H1 as [v REMOVE].
    poseq_destr r a.
    + rewrite PTree.grs in REMOVE. inv REMOVE.
    + rewrite PTree.gro in REMOVE; auto. specialize (H0 r).
      assert (exists v', rm ! r = Some v') by eauto. apply H0 in H1. simpl in H1.
      destruct H1; auto. subst. contradiction.
Qed.

Lemma udpate_more:
  forall rm newrm l a,
    ~ In a l ->
    update_regmap (map (fun r : reg => (r, Unexpr Assign (Reg r))) l) (PTree.remove a rm) newrm ->
    update_regmap (map (fun r : reg => (r, Unexpr Assign (Reg r))) l) rm newrm.
Proof.
  intros. generalize dependent rm. generalize dependent newrm. induction l; intros.
  - inv H0. constructor.
  - inv H0. poseq_destr a a0.
    + simpl in H. exfalso. apply H. left. auto.
    + assert (~ In a l).
      { unfold not. intros. apply H. simpl. right. auto. }
      specialize (IHl H0). simpl. constructor.
      inv EVAL. inv EVAL0. inv EVALV. inv EVAL.
      constructor. econstructor; econstructor. rewrite PTree.gro in GETRM; auto.
      apply IHl. auto.
Qed.

(* Deoptimizing in the new version or keeping your old reg_map is equivalent *)
Theorem defined_deopt_eq:
  forall rm rs,
    defined rm (FlatRegset.Inj rs)  ->
    exists rmdeopt,
      update_regmap (identity_varmap rs) rm rmdeopt /\
      regmap_eq rm rmdeopt.
Proof.
  assert (forall l, NoDup l ->
               forall rm,
               (forall r, In r l <-> exists v, rm!r = Some v) ->
               exists rmdeopt, update_regmap (map (fun r : reg => (r, Unexpr Assign (Reg r))) l) rm rmdeopt /\ regmap_eq rm rmdeopt).
  { intros l NODUP. induction l; intros.
    - simpl in H. simpl. exists empty_regmap. split. constructor.
      unfold regmap_eq. intros. unfold empty_regmap. rewrite PTree.gempty.
      destruct (rm!r) eqn:GET; auto. exfalso. rewrite H. eauto.
    - specialize (defined_ind a l rm NODUP H). intros H1.
      apply IHl in H1.
      2: { apply NoDup_cons_iff in NODUP. destruct NODUP. auto. }
      destruct H1 as [rmdeopt [UPDATE EQ]].
      assert (GETA: exists va, rm ! a = Some va).
      { apply H. simpl. left. auto. }
      destruct GETA as [va GETA].
      exists (rmdeopt # a <- va). split.
      +  simpl. constructor.
         * constructor. econstructor; eauto. constructor. eauto. constructor.
         * eapply udpate_more; eauto. apply NoDup_cons_iff in NODUP. destruct NODUP. auto.
      + unfold regmap_eq in *. intros r. specialize (EQ r). poseq_destr r a.
        * rewrite PTree.gss. auto.
        * rewrite PTree.gro in EQ; auto. rewrite PTree.gso; auto.          
  }
  intros. apply H.
  apply nodup_elements.
  unfold defined in H0. intros. rewrite <- PSin_in. apply H0.  
Qed.

Lemma deopt_eq:
  forall rm rs newrm,
    defined rm (FlatRegset.Inj rs) ->
    update_regmap (identity_varmap rs) rm newrm ->
    regmap_eq rm newrm.
Proof.
  intros. apply defined_deopt_eq in H. destruct H. destruct H.
  eapply ir_properties.update_regmap_determ in H; eauto. subst. auto.
Qed.

(** * Properties of clean_label_list *)
Lemma nodup_clean:
  forall l c abs,
    NoDup (clean_label_list abs c l).
Proof.
  intros l c abs. unfold clean_label_list.
  assert (ND: NoDup (remove_dup l)).
  { unfold remove_dup. apply NoDup_nodup. }
  unfold filter_unused. unfold filter_analyzed.
  assert (P: forall X (li:list X) f, NoDup li -> NoDup (filter f li)).
  { intros X li f H. induction li; simpl. constructor.
    destruct (f a) eqn:FA.
    - constructor.
      + unfold not. intros. apply filter_In in H0. destruct H0. inv H. apply H4. auto.
      + apply IHli. inv H. auto.
    - apply IHli. inv H. auto. }
  apply P. apply P. auto.
Qed.

Definition used (l:list label) (c:code) :=
  forall lbl, In lbl l -> exists i, c ! lbl = Some i.

Lemma used_clean:
  forall l c abs, used (clean_label_list abs c l) c.
Proof.
  unfold used. intros l c abs lbl IN. unfold clean_label_list in IN. apply filter_In in IN as [IN ANLZ].
  apply filter_In in IN as [IN USED].
  unfold is_used in USED. destruct (c!lbl); inv USED. eauto.
Qed.

Lemma used_cons:
  forall a l c,
    used (a::l) c -> used l c.
Proof.
  unfold used. intros a l c H lbl H0. apply H. simpl. right. auto.
Qed.

Lemma nodup_cons_in:
  forall  (l:list label) x y,
    NoDup (y::l) ->
    In x (y::l) ->
    (x = y /\ ~ In x l) \/ (x <> y /\ In x l).
Proof.
  intros l x y H H0. inv H. simpl in H0.
  poseq_destr x y.
  - left. split; auto.
  - right. split; auto. destruct H0. exfalso. apply HEQ. auto. auto.
Qed.

Definition analyzed (l:list label) (abs:abs_state) :=
  forall lbl, In lbl l -> exists rs, absstate_get lbl abs = FlatRegset.Inj rs.

Lemma analyzed_clean:
  forall l c abs,
    analyzed (clean_label_list abs c l) abs.
Proof.
  intros. unfold analyzed. intros. unfold clean_label_list in H. apply filter_In in H as [IN ANLZ].
  apply filter_In in IN as [IN USED]. unfold is_analyzed in ANLZ. unfold defined_rs in ANLZ.
  destruct (absstate_get lbl abs) eqn:GET; eauto; inv ANLZ.
Qed.


(** * Matching the stack and properties  *)
(* Matching stackframes: a version may have been replaced with its optimized version *)
Inductive match_stackframe (v:version) (fid:fun_id) (l:list label) (abs:abs_state): stackframe -> stackframe -> Prop :=
| frame_same:
    forall r v' lbl rms rmo
      (RMEQ: regmap_eq rms rmo),
      (match_stackframe v fid l abs) (Stackframe r v' lbl rms) (Stackframe r v' lbl rmo)
| frame_opt:
    forall r lbl rms rmo vins
      (FS_INSERT: fs_insert_version v fid l abs = OK vins)
      (DEF: forall retval, defined (rms#r<-retval) (absstate_get lbl abs))
      (RMEQ: regmap_eq rms rmo),
      (match_stackframe v fid l abs) (Stackframe r v lbl rms) (Stackframe r vins lbl rmo).

(* Generalizing match_stackframe to the entire stack *)
Inductive match_stack (v:version) (fid:fun_id) (l:list label) (abs:abs_state): stack -> stack -> Prop :=
| match_nil:
    (match_stack v fid l abs) nil nil
| match_cons:
    forall s s' sf sf'
      (MS: (match_stack v fid l abs) s s')
      (MSF: (match_stackframe v fid l abs) sf sf'),
      (match_stack v fid l abs) (sf::s) (sf'::s').

Lemma match_stackframe_same:
  forall v fid l abs sf,
    (match_stackframe v fid l abs) sf sf.
Proof.
  intros v fid l abs sf. destruct sf. apply frame_same. apply regmap_eq_refl.
Qed.

Lemma match_stack_same:
  forall s v fid l abs,
    (match_stack v fid l abs) s s.
Proof.
  intros s v fid l abs. induction s; constructor. auto. apply match_stackframe_same.
Qed.

Lemma match_app:
  forall synth s s' v fid l abs,
    (match_stack v fid l abs) s s' ->
    (match_stack v fid l abs) (synth++s) (synth++s').
Proof.
  intros. induction synth.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. apply match_cons. auto. apply match_stackframe_same.
Qed.

Lemma app_match:
  forall synth synthopt s s' v fid l abs,
    (match_stack v fid l abs) s s' ->
    (match_stack v fid l abs) synth synthopt ->
    (match_stack v fid l abs) (synth++s) (synthopt++s').
Proof.
  intros. induction H0.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. apply match_cons; auto.
Qed.

(** * Index and order used in the simulation *)
(* There is one stuttering step for each inserted Framestate *)
Inductive fs_index: Type :=
| One : fs_index
| Zero: fs_index.

Inductive fs_order: fs_index -> fs_index -> Type :=
| order: fs_order Zero One.

Lemma wfounded: well_founded fs_order.
Proof.
  unfold well_founded. intros a. constructor. intros y H. inv H. constructor. intros y H. inv H.
Qed.

Lemma trans: Relation_Definitions.transitive _ fs_order.
Proof.
  unfold Relation_Definitions.transitive. intros x y z H H0. inv H. inv H0.
Qed.

(** * The match_states relation  *)
(* This proof is a backward internal simulation.
   Each step of the source is matched with a step of the optimized program.
   Except for the steps of newly inserted Framestates.
   At a new Framestate, we stutter in the source.
   
<<
                 
       st1 --------------- st2
        |                   |
       t|(1 or 2 steps)     |t
        |                   |
        v                   v
       st1'--------------- st2'
                 
>>
*)

Inductive match_states (p:program) (v:version) (fid:fun_id) (lbllist:list label) (abs:abs_state): fs_index -> specIR.state -> specIR.state -> Prop :=
| fs_match:                (* matching at a new Framestate in the optimized version *)
    forall vins s s' rms rmo ms lbl
      (MATCHSTACK: (match_stack v fid lbllist abs) s s')
      (DEF: defined rms (absstate_get lbl abs))
      (OPT: fs_insert_version v fid lbllist abs = OK vins)
      (IN: In lbl lbllist)
      (RMEQ:  regmap_eq rms rmo),
      (match_states p v fid lbllist abs) One (State s v lbl rms ms) (State s' vins lbl rmo ms)
                                        
| shift_match:                     (* matching at a shifted instruction *)
    forall vins s s' rms rmo ms lbl fresh
      (MATCHSTACK: (match_stack v fid lbllist abs) s s')
      (DEF: defined rms (absstate_get lbl abs))
      (OPT: fs_insert_version v fid lbllist abs = OK vins)
      (NOT_IN: ~ In fresh lbllist)
      (SAME_CODE: (ver_code v) # lbl = (ver_code vins) # fresh)
      (RMEQ:  regmap_eq rms rmo),
      (match_states p v fid lbllist abs) Zero (State s v lbl rms ms) (State s' vins fresh rmo ms)
      
| opt_match:           (* matching inside the optimized version *)
    forall vins s s' lbl rms rmo ms
      (MATCHSTACK: (match_stack v fid lbllist abs) s s')
      (DEF: defined rms (absstate_get lbl abs))
      (OPT: fs_insert_version v fid lbllist abs = OK vins)
      (NOTIN: ~ In lbl lbllist)
      (RMEQ:  regmap_eq rms rmo),
      (match_states p v fid lbllist abs) Zero (State s v lbl rms ms) (State s' vins lbl rmo ms)
                                        
| refl_match:                   (* matching outside of the optimized version *)
    forall v' s s' pc rms rmo ms
      (MATCHSTACK: (match_stack v fid lbllist abs) s s')
      (RMEQ:  regmap_eq rms rmo),
      (match_states p v fid lbllist abs) Zero (State s v' pc rms ms) (State s' v' pc rmo ms)
                                        
| final_match:                  (* matching final states *)
    forall retval ms,
      (match_states p v fid lbllist abs) One (Final retval ms) (Final retval ms).


(** * Code preservation properties  *)
Lemma code_preservation':        (* use at opt_match *)
  forall vbase vins fid l_fs lbl abs,
    fs_insert_version vbase fid l_fs abs = OK vins ->
    ~ In lbl l_fs ->
    forall iopt isrc,
      (ver_code vins) # lbl = Some iopt ->
      (ver_code vbase) # lbl = Some isrc ->
    iopt = isrc.
Proof.
  intros vbase vins fid l_fs lbl abs OPT NOTIN iopt isrc CODEOPT CODESRC.
  unfold fs_insert_version in OPT. repeat do_ok.
  assert (H: forall cs co, insert_list_framestate cs fid l_fs abs = OK co ->
                      co ! lbl = Some iopt -> cs ! lbl = Some isrc -> iopt = isrc).
  { clear HDO CODEOPT CODESRC. induction l_fs; intros.
    - simpl in H. inv H. rewrite H0 in H1. inv H1. auto.
    - simpl in H. repeat do_ok. simpl in NOTIN.
      assert (NOTIN': a<>lbl /\ ~ In lbl l_fs).
      { split; unfold not; intros; apply NOTIN. left. auto. right. auto. }
      clear NOTIN. destruct NOTIN' as [DIFF NOTIN].
      specialize (IHl_fs NOTIN c0 co H3 H0). unfold insert_single_framestate in HDO. repeat do_ok.
      rewrite PTree.gso in IHl_fs; auto.
      poseq_destr (fresh_label (Pos.add a spacing) cs) lbl.
      + erewrite fresh_label_correct in H1; eauto. inv H1.
      + rewrite PTree.gso in IHl_fs; auto. }
  eapply H; eauto.
Qed.

Lemma code_preservation:        (* use at opt_match *)
  forall p p' s s' rms rmo ms t news vbase vins fid l_fs lbl abs,
    fs_insert_version vbase fid l_fs abs = OK vins ->
    ~ In lbl l_fs ->
    safe (specir_sem p) (State s vbase lbl rms ms) ->
    Step (specir_sem p') (State s' vins lbl rmo ms) t news ->
    (ver_code vbase) # lbl = (ver_code vins) # lbl.
Proof.
  intros p p' s s' rms rmo ms t news vbase vins fid vm_fs l_fs lbl H H0 H1 H2.
  apply safe_code in H1 as [isrc CODESRC]. apply step_code in H2 as [iopt CODEOPT].
  rewrite CODESRC. rewrite CODEOPT. f_equal. symmetry. eapply code_preservation'; eauto.
Qed.


(* The pass  cannot remove any code *)
Lemma more_code:
  forall vbase vins fid l_fs lbl abs,
    fs_insert_version vbase fid l_fs abs = OK vins ->
    (ver_code vins) # lbl = None ->
    (ver_code vbase) # lbl = None.
Proof.
  intros vbase vins fid l_fs lbl abs OPT CODE.
  unfold fs_insert_version in OPT. repeat do_ok.
  assert (H: forall cs co, insert_list_framestate cs fid l_fs abs = OK co -> co ! lbl = None -> cs ! lbl = None).
  { clear HDO. induction l_fs; intros.
    - unfold insert_list_framestate in H. inv H. auto.
    - simpl in H. repeat do_ok. specialize (IHl_fs c0 co H2 H0).
      unfold insert_single_framestate in HDO. repeat do_ok.
      poseq_destr a lbl.
      + rewrite PTree.gss in IHl_fs. inv IHl_fs.
      + rewrite PTree.gso in IHl_fs; auto.
        poseq_destr (fresh_label (Pos.add a spacing) cs) lbl.
        * eapply fresh_label_correct. eauto.
        * rewrite PTree.gso in IHl_fs; auto. }
  specialize (H (ver_code vbase) c HDO CODE). auto.
Qed.

Lemma more_code':
  forall cs co fid lbl fs_lbl abs,
    insert_single_framestate cs fid fs_lbl abs = OK co ->
    co ! lbl = None ->
    cs ! lbl = None.
Proof.
  intros cs co fid lbl fs_lbl abs H H0. unfold insert_single_framestate in H. repeat do_ok.
  poseq_destr fs_lbl lbl.
  - rewrite PTree.gss in H0. inv H0.
  - rewrite PTree.gso in H0; auto.
    poseq_destr (fresh_label (Pos.add fs_lbl spacing) cs) lbl.
    + rewrite PTree.gss in H0. eapply fresh_label_correct. eauto.
    + rewrite PTree.gso in H0; auto.
Qed.

(* The code is preserved outside of the list of labels *)
Lemma code_preserved:
  forall fid lbl i l abs cs co,
    insert_list_framestate cs fid l abs = OK co ->
    cs ! lbl = Some i ->
    ~ In lbl l ->
    co ! lbl = Some i.
Proof.
  intros fid lbl i l abs. induction l; intros.
  - simpl in H. inv H. auto.
  - simpl in H. repeat do_ok. 
    specialize (IHl c co H3). rewrite in_cns in H1. apply Decidable.not_or in H1. destruct H1.
    apply IHl; auto.
    unfold insert_single_framestate in HDO. repeat do_ok. rewrite PTree.gso; auto.
    poseq_destr (fresh_label (Pos.add a spacing) cs) lbl.
    + erewrite fresh_label_correct in H0; auto. inv H0.
    + rewrite PTree.gso; auto.
Qed.

(* Used is preserved by insertion of framestate *)
Lemma used_insert_single_framestate:
  forall l cs co fid lbl abs,
    used l cs ->
    insert_single_framestate cs fid lbl abs = OK co ->
    used l co.
Proof.
  intros. unfold insert_single_framestate in H0. repeat do_ok.
  unfold used. intros x IN. apply H in IN as [i' CODE].
  poseq_destr lbl x.
  - rewrite PTree.gss. eauto.
  - rewrite PTree.gso; auto. poseq_destr (fresh_label (Pos.add lbl spacing) cs) x.
    + rewrite PTree.gss. eauto.
    + rewrite PTree.gso; auto. eauto.
Qed.

(* At the insertion point, the code is shifted *)
Lemma code_fs:                  (* use at fs_match *)
  forall vbase vins fid l_fs lbl abs,
    fs_insert_version vbase fid l_fs abs = OK vins ->
    In lbl l_fs ->
    NoDup l_fs ->
    used l_fs (ver_code vbase) ->
    (exists freshlbl rs,
        absstate_get lbl abs = FlatRegset.Inj rs /\
        (ver_code vins) # lbl = Some (Framestate (fid,lbl) (identity_varmap rs) nil freshlbl) /\
        (ver_code vbase) # freshlbl = None /\
        exists i, (ver_code vbase) # lbl = Some i /\ (ver_code vins) # freshlbl = Some i).
Proof.
  intros vbase vins fid l_fs lbl abs OPT IN NODUP DEF.
  unfold fs_insert_version in OPT. repeat do_ok.
  assert (forall cs co, insert_list_framestate cs fid l_fs abs = OK co ->
                   In lbl l_fs -> used l_fs cs ->
                   exists freshlbl rs,
                     absstate_get lbl abs = FlatRegset.Inj rs /\
                     co ! lbl = Some (Framestate (fid,lbl) (identity_varmap rs) nil freshlbl) /\
                     cs ! freshlbl = None /\
                     exists i, cs ! lbl = Some i /\
                          co ! freshlbl = Some i).
  { clear HDO IN. induction l_fs; intros.
    - simpl in H. inv H. inv H0.
    - simpl in H. repeat do_ok. apply nodup_cons_in in H0; auto.
      destruct H0 as [[EQ NOTIN] | [DIFF IN]].
      + subst. unfold insert_single_framestate in HDO. repeat do_ok.
        exists (fresh_label (Pos.add a spacing) cs). exists r. split.
        unfold defined_rs in HDO1. destruct (absstate_get a abs); inv HDO1. auto. split.
        * eapply code_preserved; eauto. rewrite PTree.gss. auto.
        * split. { eapply fresh_label_correct. eauto. }
          exists i. split; auto. poseq_destr (fresh_label (Pos.add a spacing) cs) a.
          erewrite fresh_label_correct in HDO; eauto. inv HDO.
          eapply code_preserved; eauto. rewrite PTree.gso; auto. rewrite PTree.gss. auto.
          unfold not; intro. apply used_cons in H1. apply H1 in H. destruct H.
          erewrite fresh_label_correct in H; auto. inv H.
      + inv NODUP. apply used_cons in DEF as DEF'. apply used_cons in H1 as DEF''.
        assert (used l_fs c0) by (eapply used_insert_single_framestate; eauto).
        specialize (IHl_fs H4 DEF' c0 co H3 IN H). destruct IHl_fs as [freshlbl [rs [GET [CO [FRESH [i [C0 CO']]]]]]].
        exists freshlbl. exists rs. split; auto. split; auto. split. { eapply more_code'; eauto. }
        exists i. split; auto.
        unfold insert_single_framestate in HDO. repeat do_ok. rewrite PTree.gso in C0; auto.
        poseq_destr (fresh_label (Pos.add a spacing) cs) lbl.
        * apply DEF'' in IN. destruct IN. erewrite fresh_label_correct in H0; eauto. inv H0.
        * rewrite PTree.gso in C0; auto. }
  apply H; auto.
Qed.  

Lemma code_notfs:               (* for progress preservation *)
  forall vbase vins fid l_fs lbl abs,
    fs_insert_version vbase fid l_fs abs = OK vins ->
    ~ In lbl l_fs ->
    forall i, (ver_code vbase) # lbl = Some i ->
         (ver_code vins) # lbl = Some i.
Proof.
  assert (H: forall (l:list label) i lbl fid abs cs co,
             insert_list_framestate cs fid l abs = OK co ->
             ~ In lbl l ->
             cs # lbl = Some i ->
             co # lbl = Some i).
  { intros. generalize dependent cs.
    induction l; intros.
    - simpl in H. inv H. auto.
    - simpl in H. repeat do_ok. simpl in H0.
      assert (NOTIN: ~ In lbl l). { unfold not. intros. apply H0. right. auto. }
      assert (NOTA: a <> lbl). { unfold not. intros. apply H0. left. auto. }
      specialize (IHl NOTIN c H3).
      unfold insert_single_framestate in HDO. repeat do_ok. rewrite PTree.gso in IHl; auto.
      apply IHl. poseq_destr (fresh_label (Pos.add a spacing) cs) lbl.
      + erewrite fresh_label_correct in H1; auto. inv H1.
      + rewrite PTree.gso; auto. }
  intros vbase vins fid vm_fs l_fs lbl H0 H1 i H2.
  unfold fs_insert_version in H0. repeat do_ok.
  eapply H in HDO; eauto.
Qed.

Ltac rmeqf :=
  match goal with
  | [H: eval_expr ?e ?rms ?v,
        H1: regmap_eq ?rms ?rmo |- _] => eapply eval_expr_eq in H; eauto
  | [H: eval_list ?e ?rms ?v,
        H1: regmap_eq ?rms ?rmo |- _] => eapply eval_list_eq in H; eauto
  | [H: eval_list_expr ?e ?rms ?v,
        H1: regmap_eq ?rms ?rmo |- _] => eapply eval_list_expr_eq in H; eauto
  end.


Lemma progress_preserved:
  forall vbase vins fid l_fs abs s1 s2 p i,
    fs_insert_version vbase fid l_fs abs = OK vins ->
    find_base_version fid p = Some vbase ->
    match_states p vbase fid l_fs abs i s1 s2 ->
    safe (specir_sem p) s1 ->
    NoDup l_fs ->
    used l_fs (ver_code vbase) ->
    (exists r : value, final_state (set_version p fid vins) s2 r) \/
    (exists (t : trace) (s2' : Smallstep.state (specir_sem (set_version p fid vins))),
        Step (specir_sem (set_version p fid vins)) s2 t s2').
Proof.
  intros vbase vins fid l_fs abs s1 s2 p i OPTV FINDBASE MATCH SAFE NODUP DEF.
  inv MATCH.
  + rewrite OPT in OPTV. inv OPTV.
    right. exists E0. apply code_fs with (lbl:=lbl)in OPT as CODE; auto.
    destruct CODE as [freshlbl [rs [GET [FSCODE [BASECODE [i SHIFTCODE]]]]]].
    rewrite GET in DEF0. apply defined_deopt_eq in DEF0 as [newrms [UPDATE RMEQ']].
    exists (State s' vins freshlbl rmo ms). eapply nd_exec_Framestate_go_on.
    econstructor; eauto.
    * simpl. rewrite <- base_version_unchanged. eauto. 
    * apply regmap_eq_sym in RMEQ. eapply update_regmap_eq; eauto. 
    * constructor.

  + apply safe_step in SAFE. destruct SAFE as [s'' [t STEP]].
    right. rewrite OPT in OPTV. inv OPTV. inv STEP.
    * exists t. { inv STEP0; rewrite SAME_CODE in CODE.
      + exists (State s' vins next rmo ms). apply nd_exec_lowered. eapply exec_Nop. eauto.
      + exists (State s' vins next (rmo#reg<-v) ms). rmeqf. apply nd_exec_lowered. eapply exec_Op; eauto.
      + apply regmap_eq_sym in RMEQ. eapply update_movelist_eq in UPDATE as [rmou [UPDATE EQ']]; eauto.
        exists (State s' vins next rmou ms). apply nd_exec_lowered. eapply exec_Move; eauto.
      + exists (State s' vins (pc_cond v iftrue iffalse) rmo ms). rmeqf.
        apply nd_exec_lowered. eapply exec_Cond; eauto.
      + poseq_destr fid0 fid.
        * eapply find_function_same with (v:=vins) in FINDF.
          exists (State (Stackframe retreg vins next rmo ::s') (current_version (set_version_function vins func)) (ver_entry (current_version (set_version_function vins func))) newrm ms).
          rmeqf. apply nd_exec_lowered. eapply exec_Call; eauto.
        * simpl in FINDF. eapply find_function_unchanged with (fid':=fid) (v:=vins) in HEQ.
          rewrite HEQ in FINDF.
          exists (State (Stackframe retreg vins next rmo ::s') (current_version (func)) (ver_entry (current_version (func))) newrm ms).
          rmeqf. apply nd_exec_lowered. eapply exec_Call; eauto.
      + inv MATCHSTACK. inv MSF.
        * exists (State s'0 fprev next (rmo0#retreg<-retval) ms).
          rmeqf. apply nd_exec_lowered. eapply exec_Return; eauto.
        * exists (State s'0 vins0 next (rmo0#retreg<-retval) ms). apply nd_exec_lowered.
          rmeqf. eapply exec_Return; eauto.
      + inv MATCHSTACK. exists (Final retval ms). rmeqf. apply nd_exec_lowered. eapply exec_Return_Final; eauto.
      + exists (State s' vins next rmo ms). rmeqf. apply nd_exec_lowered. eapply exec_Printexpr; eauto.
      + exists (State s' vins next rmo ms). apply nd_exec_lowered. eapply exec_Printstring. auto.
      + exists (State s' vins next rmo newms). rmeqf. rmeqf. apply nd_exec_lowered. eapply exec_Store; eauto.
      + exists (State s' vins next (rmo#reg<-val) ms). rmeqf. apply nd_exec_lowered. eapply exec_Load; eauto.
      + exists (State s' vins next rmo ms). rmeqf. apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
      + rewrite synth_frame_unchanged in SYNTH. erewrite base_version_unchanged in FINDF. rmeqf.
        apply regmap_eq_sym in RMEQ. eapply update_regmap_eq in UPDATE; eauto.
        exists (State (synth ++ s') newver la newrm ms). apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
        simpl in FINDF. simpl. eauto. simpl in SYNTH. simpl. eapply synthesize_frame_eq in SYNTH; eauto. }
    * exists E0. exists (State s' vins next rmo ms). inv DEOPT_COND. rewrite synth_frame_unchanged in SYNTH.
      rewrite SAME_CODE in CODE. apply regmap_eq_sym in RMEQ. eapply update_regmap_eq in UPDATE; eauto.
      eapply synthesize_frame_eq in SYNTH; eauto. eapply nd_exec_Framestate_go_on. 
      econstructor; eauto. simpl. rewrite <- base_version_unchanged. eauto. simpl in SYNTH. simpl. eauto.
    * exists E0. exists (State s' vins next rmo ms). inv DEOPT_COND. rewrite synth_frame_unchanged in SYNTH.
      rewrite SAME_CODE in CODE. apply regmap_eq_sym in RMEQ. eapply update_regmap_eq in UPDATE; eauto.
      eapply synthesize_frame_eq in SYNTH; eauto. eapply nd_exec_Framestate_go_on. 
      econstructor; eauto. simpl. rewrite <- base_version_unchanged. eauto. simpl in SYNTH. simpl. eauto.

  + rewrite OPT in OPTV. inv OPTV. apply safe_step in SAFE. destruct SAFE as [s'' [t STEP]].
    specialize (code_notfs vbase vins fid l_fs lbl abs OPT NOTIN). intros SAME_CODE.
    right. inv STEP.
    * exists t. { inv STEP0; apply SAME_CODE in CODE.
      + exists (State s' vins next rmo ms). apply nd_exec_lowered. eapply exec_Nop. eauto.
      + exists (State s' vins next (rmo#reg<-v) ms). rmeqf. apply nd_exec_lowered. eapply exec_Op; eauto.
      + apply regmap_eq_sym in RMEQ. eapply update_movelist_eq in UPDATE as [rmou [UPDATE EQ']]; eauto.
        exists (State s' vins next rmou ms). apply nd_exec_lowered. eapply exec_Move; eauto.
      + exists (State s' vins (pc_cond v iftrue iffalse) rmo ms). rmeqf. apply nd_exec_lowered.
        eapply exec_Cond; eauto.
      + poseq_destr fid0 fid.
        * eapply find_function_same with (v:=vins) in FINDF.
          exists (State (Stackframe retreg vins next rmo ::s') (current_version (set_version_function vins func)) (ver_entry (current_version (set_version_function vins func))) newrm ms).
          rmeqf. apply nd_exec_lowered. eapply exec_Call; eauto.
        * simpl in FINDF. eapply find_function_unchanged with (fid':=fid) (v:=vins) in HEQ.
          rewrite HEQ in FINDF.
          exists (State (Stackframe retreg vins next rmo ::s') (current_version (func)) (ver_entry (current_version (func))) newrm ms).
          rmeqf. apply nd_exec_lowered. eapply exec_Call; eauto.
      + inv MATCHSTACK. inv MSF.
        * exists (State s'0 fprev next (rmo0#retreg<-retval) ms).
          rmeqf. apply nd_exec_lowered. eapply exec_Return; eauto.
        * exists (State s'0 vins0 next (rmo0#retreg<-retval) ms). apply nd_exec_lowered.
          rmeqf. eapply exec_Return; eauto.
      + inv MATCHSTACK. exists (Final retval ms). rmeqf. apply nd_exec_lowered. eapply exec_Return_Final; eauto.
      + exists (State s' vins next rmo ms). rmeqf. apply nd_exec_lowered. eapply exec_Printexpr; eauto.
      + exists (State s' vins next rmo ms). apply nd_exec_lowered. eapply exec_Printstring. auto.
      + exists (State s' vins next rmo newms). rmeqf. rmeqf. apply nd_exec_lowered. eapply exec_Store; eauto.
      + exists (State s' vins next (rmo#reg<-val) ms). rmeqf. apply nd_exec_lowered. eapply exec_Load; eauto.
      + exists (State s' vins next rmo ms). rmeqf. apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
      + rmeqf. apply regmap_eq_sym in RMEQ. eapply synthesize_frame_eq in SYNTH; eauto.
        rewrite synth_frame_unchanged in SYNTH. erewrite base_version_unchanged in FINDF.
        exists (State (synth ++ s') newver la newrm ms). apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
        simpl in FINDF. simpl. eauto. eapply update_regmap_eq; eauto. simpl in SYNTH. simpl. eauto. }
    * exists E0. exists (State s' vins next rmo ms). inv DEOPT_COND. rewrite synth_frame_unchanged in SYNTH.
      apply regmap_eq_sym in RMEQ. eapply update_regmap_eq in UPDATE; eauto.
      eapply synthesize_frame_eq in SYNTH; eauto. eapply nd_exec_Framestate_go_on. 
      econstructor; eauto. simpl. rewrite <- base_version_unchanged. eauto. simpl in SYNTH. simpl. eauto.
    * exists E0. exists (State s' vins next rmo ms). inv DEOPT_COND. rewrite synth_frame_unchanged in SYNTH.
      apply regmap_eq_sym in RMEQ. eapply update_regmap_eq in UPDATE; eauto.
      eapply synthesize_frame_eq in SYNTH; eauto. eapply nd_exec_Framestate_go_on. 
      econstructor; eauto. simpl. rewrite <- base_version_unchanged. eauto. simpl in SYNTH. simpl. eauto.

  + right. apply safe_step in SAFE. destruct SAFE as [s'' [t STEP]].
    inv STEP.
    * exists t. { inv STEP0.
      + exists (State s' v' next rmo ms). apply nd_exec_lowered. eapply exec_Nop. eauto.
      + exists (State s' v' next (rmo#reg<-v) ms). rmeqf. apply nd_exec_lowered. eapply exec_Op; eauto.
      + apply regmap_eq_sym in RMEQ. eapply update_movelist_eq in UPDATE as [rm1u [UPDATE EQ]]; eauto.
        exists (State s' v' next rm1u ms). apply nd_exec_lowered. eapply exec_Move; eauto.
      + exists (State s' v' (pc_cond v iftrue iffalse) rmo ms). rmeqf. apply nd_exec_lowered.
        eapply exec_Cond; eauto.
      + poseq_destr fid0 fid.
        * eapply find_function_same with (v:=vins) in FINDF.
          exists (State (Stackframe retreg v' next rmo ::s') (current_version (set_version_function vins func)) (ver_entry (current_version (set_version_function vins func))) newrm ms).
          rmeqf. apply nd_exec_lowered. eapply exec_Call; eauto.
        * simpl in FINDF. eapply find_function_unchanged with (fid':=fid) (v:=vins) in HEQ.
          rewrite HEQ in FINDF.
          exists (State (Stackframe retreg v' next rmo ::s') (current_version (func)) (ver_entry (current_version (func))) newrm ms).
          rmeqf. apply nd_exec_lowered. eapply exec_Call; eauto.
      + inv MATCHSTACK. inv MSF.
        * exists (State s'0 fprev next (rmo0#retreg<-retval) ms).
          rmeqf. apply nd_exec_lowered. eapply exec_Return; eauto.
        * exists (State s'0 vins0 next (rmo0#retreg<-retval) ms). apply nd_exec_lowered.
          rmeqf. eapply exec_Return; eauto.
      + inv MATCHSTACK. exists (Final retval ms). rmeqf. apply nd_exec_lowered. eapply exec_Return_Final; eauto.
      + exists (State s' v' next rmo ms). rmeqf. apply nd_exec_lowered. eapply exec_Printexpr; eauto.
      + exists (State s' v' next rmo ms). apply nd_exec_lowered. eapply exec_Printstring. auto.
      + exists (State s' v' next rmo newms). rmeqf. rmeqf. apply nd_exec_lowered. eapply exec_Store; eauto.
      + exists (State s' v' next (rmo#reg<-val) ms). rmeqf. apply nd_exec_lowered. eapply exec_Load; eauto.
      + exists (State s' v' next rmo ms). rmeqf. apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
      + rmeqf. apply regmap_eq_sym in RMEQ. eapply synthesize_frame_eq in SYNTH; eauto.
        rewrite synth_frame_unchanged in SYNTH. erewrite base_version_unchanged in FINDF.
        exists (State (synth ++ s') newver la newrm ms). apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
        simpl in FINDF. simpl. eauto. eapply update_regmap_eq; eauto. simpl in SYNTH. simpl. eauto. }
    * exists E0. exists (State s' v' next rmo ms). inv DEOPT_COND. rewrite synth_frame_unchanged in SYNTH.
      apply regmap_eq_sym in RMEQ. eapply update_regmap_eq in UPDATE; eauto.
      eapply synthesize_frame_eq in SYNTH; eauto. eapply nd_exec_Framestate_go_on. 
      econstructor; eauto. simpl. rewrite <- base_version_unchanged. eauto. simpl in SYNTH. simpl. eauto.
    * exists E0. exists (State s' v' next rmo ms). inv DEOPT_COND. rewrite synth_frame_unchanged in SYNTH.
      apply regmap_eq_sym in RMEQ. eapply update_regmap_eq in UPDATE; eauto.
      eapply synthesize_frame_eq in SYNTH; eauto. eapply nd_exec_Framestate_go_on. 
      econstructor; eauto. simpl. rewrite <- base_version_unchanged. eauto. simpl in SYNTH. simpl. eauto.
  + left. exists retval. constructor.
Qed.


Lemma in_or_not:
  forall (l:label) l_fs,
    In l l_fs \/ ~ In l l_fs.
Proof.
  intros l l_fs. induction l_fs.
  - right. unfold not; intros. inv H.
  - poseq_destr a l.
    + left. simpl. left. auto.
    + destruct IHl_fs; [left | right]; simpl.
      right. auto. unfold not; intros. destruct H0. contradiction. apply H in H0. auto.
Qed.

Ltac def_ok :=
  match goal with
  | [CODE: (ver_code ?vsrc) ! ?lbl = Some ?i |- _] =>
    eapply analyze_correct; eauto; simpl; auto; unfold dr_transf; try rewrite CODE; auto
  end.

Ltac rmeqb :=
  match goal with
  | [ |- regmap_eq (?rm1 # ?r <- ?v) (?rm2 # ?r <- ?v)] => apply regmap_eq_insert; auto
  | [H: eval_expr ?e ?rmo ?v,
        H1: regmap_eq ?rms ?rmo |- _] => eapply eval_expr_eq in H; apply regmap_eq_sym in H1; eauto
  | [H: eval_list ?e ?rmo ?v,
        H1: regmap_eq ?rms ?rmo |- _] => eapply eval_list_eq in H; apply regmap_eq_sym in H1; eauto
  | [H: eval_list_expr ?e ?rmo ?v,
        H1: regmap_eq ?rms ?rmo |- _] => eapply eval_list_expr_eq in H; apply regmap_eq_sym in H1; eauto
  end.


(* The diagram of a backward simulation for lowered steps *)
(* We only require the same code on both sides, and reuse this lemma for both opt_match and shift_match *)
Lemma lowered_diagram:
  forall p vbase fid l_fs abs vins lblsrc lblopt s s' rms rmo ms t s2' f
    (OPT: fs_insert_version vbase fid l_fs abs = OK vins)
    (FINDF: find_function fid p = Some f)
    (NOOPT: fn_opt f = None)
    (BASE': fn_base f = vbase)
    (MATCHSTACK: match_stack vbase fid l_fs abs s s')
    (SAME_CODE: (ver_code vbase) ! lblsrc = (ver_code vins) ! lblopt)
    (DEFREGS: defined_regs_analysis (ver_code vbase) (fn_params f) (ver_entry vbase) = Some abs)
    (DEF: defined rms (absstate_get lblsrc abs))
    (STEP: lowered_step (set_version p fid vins) (State s' vins lblopt rmo ms) t s2')
    (RMEQ: regmap_eq rms rmo),
  exists (i: fs_index) (s1': Smallstep.state (specir_sem p)),
    (SPlus (specir_sem p) (State s vbase lblsrc rms ms) t s1' \/
     Star (specir_sem p) (State s vbase lblsrc rms ms) t s1' /\ fs_order i Zero) /\
    match_states p vbase fid l_fs abs i s1' s2'.
Proof.
  intros p vbase fid l_fs abs vins lblsrc lblopt s s' rms rmo ms t s2' f OPT FINDF NOOPT BASE' MATCHSTACK SAME_CODE DEFREGS DEF STEP RMEQ.
  assert (BASE: find_base_version fid p = Some vbase).
  { unfold find_base_version. rewrite FINDF. f_equal. auto. } clear BASE'.
  inv STEP; rewrite CODE in SAME_CODE.

  - destruct (in_or_not next l_fs) as [IN | NOTIN].
    + exists One. exists (State s vbase next rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Nop; eauto.
      * eapply fs_match; auto. def_ok. rewrite SAME_CODE. auto. 
    + exists Zero. exists (State s vbase next rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Nop; eauto.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.

  - destruct (in_or_not next l_fs) as [IN | NOTIN].
    + exists One. exists (State s vbase next (rms # reg <- v) ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Op; eauto. rmeqb.
      * eapply fs_match; auto. def_ok. rewrite SAME_CODE. apply define_insert. auto. rmeqb.
    + exists Zero. exists (State s vbase next (rms # reg <- v) ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Op; eauto. rmeqb.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. apply define_insert. auto. rmeqb.

  - eapply update_movelist_eq in UPDATE as [rm1u [UPDATE EQ]]; eauto.
    destruct (in_or_not next l_fs) as [IN | NOTIN].
    + exists One. exists (State s vbase next rm1u ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Move; eauto.        
      * eapply fs_match; auto. def_ok. rewrite SAME_CODE. eapply define_insert_list; eauto.
    + exists Zero. exists (State s vbase next rm1u ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Move; eauto.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. eapply define_insert_list; eauto.

  - destruct (in_or_not (pc_cond v iftrue iffalse) l_fs) as [IN | NOTIN].
    + exists One. exists (State s vbase (pc_cond v iftrue iffalse) rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Cond; eauto. rmeqb.
      * eapply fs_match; auto. def_ok. destruct v. destruct z; auto. rewrite SAME_CODE. auto.
    + exists Zero. exists (State s vbase (pc_cond v iftrue iffalse) rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Cond; eauto. rmeqb.
      * eapply opt_match; eauto. def_ok. destruct v. destruct z; auto. rewrite SAME_CODE. auto.

  - poseq_destr fid fid0.
    +                           (* calling the optimized function *)
      assert (ISBASE: vbase = current_version f).
      { unfold find_base_version in BASE. rewrite FINDF in BASE. inv BASE. unfold current_version.
        rewrite NOOPT. auto. }
      assert (ISINS: vins = current_version func).
      { unfold current_version. eapply find_function_same in FINDF; eauto. rewrite FINDF0 in FINDF.
        inv FINDF. simpl. auto. }
      assert (SAME_ENTRY:ver_entry vbase = ver_entry vins).
      { unfold fs_insert_version in OPT. repeat do_ok. simpl. auto. }
      assert (SAME_PARAMS: fn_params f = fn_params func).
      { erewrite find_function_same in FINDF0; eauto. inv FINDF0. unfold set_version_function. auto. }
      destruct (in_or_not (ver_entry(current_version f)) l_fs) as [IN|NOTIN].
      * exists One. exists (State (Stackframe retreg vbase next rms :: s) (current_version f) (ver_entry (current_version f)) newrm ms). split.
        ** left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto. rmeqb.
           eapply same_params in FINDF0 as PARAMS; eauto. rewrite PARAMS. auto.
        ** rewrite <- ISBASE. rewrite <- ISINS.
           rewrite SAME_ENTRY. apply fs_match; auto. constructor; auto. constructor; auto.
           intro. def_ok. rewrite SAME_CODE. apply define_insert. auto.
           rewrite <- SAME_ENTRY. eapply analyze_init; eauto. rewrite SAME_PARAMS. eauto.
           rewrite <- ISBASE in IN. rewrite <- SAME_ENTRY. auto. apply regmap_eq_refl.
      * exists Zero. exists (State (Stackframe retreg vbase next rms :: s) (current_version f) (ver_entry (current_version f)) newrm ms). split.
        ** left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto. rmeqb.
           eapply same_params in FINDF0 as PARAMS; eauto. rewrite PARAMS. auto.
        ** rewrite <- ISBASE. rewrite <- ISINS.
           rewrite SAME_ENTRY. apply opt_match; auto. constructor; auto. constructor; auto.
           intro. def_ok. rewrite SAME_CODE. apply define_insert. auto.
           rewrite <- SAME_ENTRY. eapply analyze_init; eauto. rewrite SAME_PARAMS. eauto.
           rewrite <- ISBASE in NOTIN. rewrite <- SAME_ENTRY. auto. apply regmap_eq_refl.
                                                                  
    + exists Zero. exists (State (Stackframe retreg vbase next rms :: s) (current_version func) (ver_entry (current_version func)) newrm ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
        erewrite <- find_function_unchanged in FINDF0; auto. rmeqb.
      * apply refl_match; auto. constructor; auto. constructor; auto.
        intro. def_ok. rewrite SAME_CODE. apply define_insert. auto. apply regmap_eq_refl.

  - inv MATCHSTACK. inv MSF.
    + exists Zero. exists (State s1 fprev next (rms0 # retreg <- retval) ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto. rmeqb.
      * apply refl_match. auto. rmeqb. 
    + rewrite FS_INSERT in OPT. inv OPT. (* returning into the optimized version *)
      destruct (in_or_not next l_fs).
      * exists One. exists (State s1 vbase next (rms0#retreg<-retval) ms). split.
        ** left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto. rmeqb.
        ** eapply fs_match; eauto. rmeqb.
      * exists Zero. exists (State s1 vbase next (rms0#retreg<-retval) ms). split.
        ** left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto. rmeqb.
        ** eapply opt_match; eauto. rmeqb.

  - inv MATCHSTACK. exists One. exists (Final retval ms). split.
    * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return_Final; eauto. rmeqb.
    * eapply final_match; eauto.

  - destruct (in_or_not next l_fs) as [IN | NOTIN].
    + exists One. exists (State s vbase next rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Printexpr; eauto. rmeqb.
      * eapply fs_match; auto. def_ok. rewrite SAME_CODE. auto.
    + exists Zero. exists (State s vbase next rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Printexpr; eauto. rmeqb.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.

  - destruct (in_or_not next l_fs) as [IN | NOTIN].
    + exists One. exists (State s vbase next rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Printstring; eauto.
      * eapply fs_match; auto. def_ok. rewrite SAME_CODE. auto.
    + exists Zero. exists (State s vbase next rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Printstring; eauto.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.

  - destruct (in_or_not next l_fs) as [IN | NOTIN].
    + exists One. exists (State s vbase next rms newms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Store; eauto. clear EVAL_AD. rmeqb. rmeqb.
      * eapply fs_match; auto. def_ok. rewrite SAME_CODE. auto.
    + exists Zero. exists (State s vbase next rms newms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Store; eauto. clear EVAL_AD. rmeqb. rmeqb.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.

  - destruct (in_or_not next l_fs) as [IN | NOTIN].
    + exists One. exists (State s vbase next (rms#reg<-val) ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Load; eauto. rmeqb.
      * eapply fs_match; auto. def_ok. rewrite SAME_CODE. eapply define_insert; eauto. rmeqb.
    + exists Zero. exists (State s vbase next (rms#reg<-val) ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Load; eauto. rmeqb.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. eapply define_insert; eauto. rmeqb.

  - destruct (in_or_not next l_fs) as [IN | NOTIN].
    + exists One. exists (State s vbase next rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_holds; eauto. rmeqb.
      * eapply fs_match; auto. def_ok. rewrite SAME_CODE. auto.
    + exists Zero. exists (State s vbase next rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_holds; eauto. rmeqb.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.

  - apply <- synth_frame_unchanged in SYNTH. exists Zero.
    rewrite <- base_version_unchanged in FINDF0.
    eapply synthesize_frame_eq in SYNTH; eauto.
    eapply update_regmap_eq in UPDATE; eauto.
    exists (State (synth ++ s) newver la newrm ms). split.
    + left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_fails; eauto. rmeqb.
    + apply refl_match. apply match_app. auto. apply regmap_eq_refl.
Qed.



 
(* Proved directly with a backward simulation *)
Theorem framestate_insertion_correct:
  forall p fid lbllist newp,
    insert_framestate fid lbllist p = OK newp ->
    backward_internal_simulation p newp.
Proof.
  intros p fid lbllist newp OPT. unfold insert_framestate in OPT. repeat do_ok.
  rename HDO1 into FINDOPTF. rename a into abs.
  set (l_fs := (clean_label_list abs (ver_code (fn_base f)) lbllist)).
  rename v into vins. unfold check_no_opt in HDO0. destruct (fn_opt f) eqn:NO_OPT; inv HDO0.
  set (vbase := (fn_base f)). fold l_fs vbase in HDO2. rename v0 into vins.
  assert (OPTV: fs_insert_version vbase fid l_fs abs = OK vins) by auto.
  unfold fs_insert_version in HDO2. repeat do_ok.
  set (vins := {|ver_code := c; ver_entry := ver_entry vbase |}). fold vins in OPTV.
  apply Backward_internal_simulation with (bsim_order := fs_order) (bsim_match_states := match_states p vbase fid l_fs abs).
  - apply wfounded.
  - apply trans.

  - unfold reflexive_forge. intros synchro stack r1 s1 ms FORGE.
    destruct synchro; simpl in FORGE; repeat do_ok; simpl.
    + poseq_destr f0 fid.  (* is the called function the optimized one? *)
      * erewrite find_function_same; eauto. simpl. rewrite HDO1. simpl.
        rewrite FINDOPTF in HDO2. inv HDO2.
        assert (CURRENT:  vbase  = (current_version f1)).
        { unfold vbase. unfold current_version. rewrite NO_OPT. auto. }
        rewrite <- CURRENT.        
        { destruct (in_or_not (ver_entry(current_version f1)) l_fs) as [IN|NOTIN]; repeat (esplit; eauto).
          - unfold vbase. apply fs_match; eauto. apply match_stack_same.
            apply interpreter_proof.init_regs_correct in HDO1. eapply analyze_init; eauto.
            rewrite <- CURRENT in IN. unfold vbase in IN. auto. apply regmap_eq_refl.
          - apply opt_match. apply match_stack_same.
            apply interpreter_proof.init_regs_correct in HDO1. eapply analyze_init; eauto. auto.
            rewrite <- CURRENT in NOTIN. auto. apply regmap_eq_refl. }
      * erewrite <- find_function_unchanged; eauto. rewrite HDO2. simpl. rewrite HDO1. simpl.
        repeat (esplit; eauto). constructor. apply match_stack_same. apply regmap_eq_refl.
    + destruct stack; try destruct s; inv FORGE.
      * repeat (esplit; eauto). constructor.
      * repeat (esplit; eauto). simpl. constructor. apply match_stack_same. apply regmap_eq_refl.
    + destruct d. repeat do_ok. simpl. rewrite <- base_version_unchanged. rewrite HDO1. simpl.
      repeat (esplit; eauto). simpl. constructor. apply match_stack_same. apply regmap_eq_refl.
    + inv FORGE. destruct r1; repeat (esplit; eauto). 
      * simpl. apply refl_match. apply match_stack_same. apply regmap_eq_refl.
      * simpl. apply final_match.
        
  - intros i s1 s2 r MATCH SAFE FINAL. inv FINAL. inv MATCH. exists (Final r ms). split.
    apply star_refl. constructor.

  - intros. eapply progress_preserved; eauto. unfold find_base_version. rewrite FINDOPTF. eauto.
    apply nodup_clean. apply used_clean.
    
  - intros s2 t s2' STEP i s1 MATCH SAFE.
    assert (NODUP: NoDup l_fs) by apply nodup_clean.
    assert (DEF: used l_fs (ver_code vbase)) by apply used_clean.
    inv MATCH.


    + rewrite OPT in OPTV. inv OPTV. (* fs_match *)
      eapply code_fs in IN as [fresh [rs [GET [FSCODE [FRESH [nextinstr [CODESRC CODEOPT]]]]]]]; eauto.
      inv STEP. { inv STEP0; rewrite CODE in FSCODE; inv FSCODE. }
      { exists Zero. exists (State s vbase lbl rms ms). split. (* stuttering, FS goes on  *)
        - right. split. 2:constructor. apply star_refl.
        - inv DEOPT_COND. rewrite CODE in FSCODE. inv FSCODE. inv SYNTH. apply shift_match; auto.
          unfold not; intros. apply DEF in H as [i CODE']. rewrite CODE' in FRESH. inv FRESH.
          rewrite CODESRC. rewrite CODEOPT. auto. }
      { exists Zero. exists (State s vbase lbl rms ms). split. (* stuttering, FS deoptimizes *)
        - right. split. 2:constructor. apply star_refl.
        - inv DEOPT_COND. rewrite CODE in FSCODE. inv FSCODE. inv SYNTH. simpl.
          rewrite GET in DEF0.
          assert (DEFO: defined rmo (FlatRegset.Inj rs)). { eapply regmap_eq_defined; eauto. }
          apply defined_deopt_eq in DEF0 as [rmdeopt [UPDATE' EQ]].
          assert (BASE: vbase = newver).
          { simpl in FINDF. rewrite <- base_version_unchanged in FINDF. unfold find_base_version in FINDF.
            rewrite FINDOPTF in FINDF. inv FINDF. unfold vbase. auto. } rewrite BASE.
          apply refl_match; auto. rewrite <- BASE. auto.
          apply deopt_eq in UPDATE. eapply regmap_eq_trans; eauto. auto. }

    + rewrite OPT in OPTV. inv OPTV. (* shift_match *)
      inv STEP.
      { eapply lowered_diagram; eauto. }
      * inv DEOPT_COND.         (* Framestate steps can't happen in shift_match *)
        rewrite CODE in SAME_CODE. unfold vbase in SAME_CODE. apply (base_no_spec f) in SAME_CODE.
        exfalso. apply SAME_CODE. constructor.
      * inv DEOPT_COND.         (* Framestate steps can't happen in shift_match *)
        rewrite CODE in SAME_CODE. unfold vbase in SAME_CODE. apply (base_no_spec f) in SAME_CODE.
        exfalso. apply SAME_CODE. constructor.
        
    + rewrite OPT in OPTV. inv OPTV. (* opt_match *)
      eapply code_preservation in NOTIN as SAME_CODE; eauto.
      inv STEP.
      { eapply lowered_diagram; eauto. }
      * inv DEOPT_COND. (* Framestate steps can't happen in opt_match *)
        rewrite CODE in SAME_CODE. unfold vbase in SAME_CODE. apply (base_no_spec f) in SAME_CODE.
        exfalso. apply SAME_CODE. constructor.
      * inv DEOPT_COND. (* Framestate steps can't happen in opt_match *)
        rewrite CODE in SAME_CODE. unfold vbase in SAME_CODE. apply (base_no_spec f) in SAME_CODE.
        exfalso. apply SAME_CODE. constructor.


    + inv STEP.                 (* refl_match *)
      { inv STEP0.
        - exists Zero. exists (State s v' next rms ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Nop; eauto.
          + apply refl_match; auto.
        - exists Zero. exists (State s v' next (rms#reg<-v) ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Op; eauto. rmeqb.
          + apply refl_match; auto. rmeqb.
        - eapply update_movelist_eq in UPDATE as [rm1u [UPDATE NEXT]]; eauto.
          exists Zero. exists (State s v' next rm1u ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Move; eauto. 
          + apply refl_match; auto.
        - exists Zero. exists (State s v' (pc_cond v iftrue iffalse) rms ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Cond; eauto. rmeqb.
          + apply refl_match; auto.
        - poseq_destr fid0 fid.
          + destruct (in_or_not (ver_entry vbase) l_fs) as [IN|NOTIN].
            * exists One. exists (State (Stackframe retreg v' next rms ::s) (current_version f) (ver_entry (current_version f)) newrm ms). split.
              ** left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto. rmeqb.
                 simpl in FINDF. eapply same_params in FINDOPTF; eauto. rewrite FINDOPTF. auto.
              ** simpl in FINDF. erewrite find_function_same in FINDF; eauto. inv FINDF.
                 unfold current_version. rewrite NO_OPT. simpl. apply fs_match; auto.
                 constructor; auto. eapply frame_same; eauto.
                 eapply analyze_init; eauto. apply regmap_eq_refl.
            * exists Zero. exists (State (Stackframe retreg v' next rms ::s) (current_version f) (ver_entry (current_version f)) newrm ms). split.
            ** left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto. rmeqb.
               simpl in FINDF. eapply same_params in FINDOPTF; eauto. rewrite FINDOPTF. auto.
            ** simpl in FINDF. erewrite find_function_same in FINDF; eauto. inv FINDF.
               unfold current_version. rewrite NO_OPT. simpl. apply opt_match; auto.
               constructor; auto. constructor. auto. eapply analyze_init; eauto. apply regmap_eq_refl.
          + simpl in FINDF. rewrite <- find_function_unchanged in FINDF; auto. exists Zero. 
            exists (State (Stackframe retreg v' next rms :: s) (current_version func) (ver_entry (current_version func)) newrm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto. rmeqb.
            * apply refl_match; auto. constructor; auto. constructor. auto. apply regmap_eq_refl.
        - inv MATCHSTACK. inv MSF.
          + exists Zero. exists (State s1 fprev next (rms0#retreg<-retval) ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto. rmeqb.
            * apply refl_match; auto. rmeqb.
          + destruct (in_or_not next l_fs).
            * exists One. exists (State s1 vbase next (rms0#retreg<-retval) ms). split.
              ** left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto. rmeqb.
              ** apply fs_match; auto. rmeqb.
            *  exists Zero. exists (State s1 vbase next (rms0#retreg<-retval) ms). split.
               ** left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto. rmeqb.
               ** apply opt_match; auto. rmeqb.
        - inv MATCHSTACK. exists One. exists (Final retval ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Return_Final; eauto. rmeqb.
          + apply final_match; auto.
        - exists Zero. exists (State s v' next rms ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Printexpr; eauto. rmeqb.
          + apply refl_match; auto.
        - exists Zero. exists (State s v' next rms ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Printstring; eauto.
          + apply refl_match; auto.
        - exists Zero. exists (State s v' next rms newms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Store; eauto. clear EVAL_AD. rmeqb. rmeqb.
          + apply refl_match; auto.
        - exists Zero. exists (State s v' next (rms#reg<-val) ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Load; eauto. rmeqb.
          + apply refl_match; auto. rmeqb.
        - exists Zero. exists (State s v' next rms ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_holds; eauto. rmeqb.
          + apply refl_match; auto.
        - eapply update_regmap_eq in UPDATE; eauto. eapply synthesize_frame_eq in SYNTH; eauto.
          exists Zero. exists (State (synth++s) newver la newrm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_fails; eauto. rmeqb.
            erewrite base_version_unchanged; eauto. apply FINDF. apply synth_frame_unchanged in SYNTH. auto.
          + apply refl_match; auto. apply match_app; auto. apply regmap_eq_refl. }
      * inv DEOPT_COND. simpl in FINDF. rewrite <- base_version_unchanged in FINDF.
        apply synth_frame_unchanged in SYNTH.
        eapply update_regmap_eq in UPDATE; eauto. eapply synthesize_frame_eq in SYNTH; eauto.
        exists Zero. exists (State s v' next rms ms). split.
        left. apply plus_one. eapply nd_exec_Framestate_go_on. 
        econstructor; eauto. apply refl_match; auto.
      * inv DEOPT_COND. simpl in FINDF. rewrite <- base_version_unchanged in FINDF.
        apply synth_frame_unchanged in SYNTH.
        eapply update_regmap_eq in UPDATE; eauto. eapply synthesize_frame_eq in SYNTH; eauto.
        exists Zero. exists (State (synth ++ s) newver la newrm ms). split.
        left. apply plus_one. eapply nd_exec_Framestate_deopt. 
        econstructor; eauto. apply refl_match; auto. apply match_app; auto. apply regmap_eq_refl.

    + inv STEP. inv STEP0.      (* final_match *)
Qed.
