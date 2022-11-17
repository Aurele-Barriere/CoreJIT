(* Verification of the Framestate Insertion pass *)
(* The first pass of the dynamic optimizer *)

Require Export specIR.
Require Export framestate_insertion.
Require Export ir_properties.
Require Export internal_simulations.
Require Import Coq.MSets.MSetPositive.
Require Import Lists.SetoidList.
Require Export def_regs.
Require Export liveness.

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
        * unfold not. intros. rewrite <- Inl_In in H. auto.
        * apply IHl. auto.
      + inv H. constructor.
        * unfold not. intros. rewrite Inl_In in H. auto.
        * apply IHl. auto. }
  intros. apply H. apply PositiveSet.elements_spec2w.
Qed.

Lemma defined_ind:
  forall a l rm,
    NoDup (a::l) ->
    (forall r : positive, In r (a :: l) -> (exists v : value, rm ! r = Some v)) ->
    (forall r : positive, In r l -> (exists v, (PTree.remove a rm)!r = Some v)).
Proof.
  intros. assert (In r (a::l)) by (right; auto). apply H0 in H2 as [v SOME].
  exists v. rewrite PTree.gro. auto. inv H. poseq_destr r a; auto.
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

(* rs is a subset of the set obtained by adding successively all its elements
   (actually both are the same set) *)
Lemma fold_elements:
  forall r rs,
    PositiveSet.In r rs -> PositiveSet.In r (fold_right PositiveSet.add PositiveSet.empty (PositiveSet.elements rs)).
Proof.
  intros r rs. rewrite PSin_in.
  induction (PositiveSet.elements rs).
  - intros. inv H.
  - simpl. intros. destruct H.
    + apply PositiveSet.add_spec. left. auto.
    + apply IHl in H. apply PositiveSet.add_spec. right. auto.
Qed.

(* If the regmap in the optimized version is defined on rs, the regmap obtained after 
   deoptimizing using the identity varmap on [rs'] a subset of [rs]
   agrees with the old regmap on rs'. *)
Theorem defined_deopt_subset_agree:
  forall rm rs rs' ,
    defined rm (DefFlatRegset.Inj rs) ->
    PositiveSet.Subset rs' rs ->
    exists rmdeopt,
      update_regmap (identity_varmap rs') rm rmdeopt /\
      agree rm rmdeopt rs'.
Proof.
  assert (forall l, NoDup l ->
                    forall rm,
                      (forall r, In r l -> exists v, rm!r = Some v) ->
                      exists rmdeopt,
                        update_regmap (map (fun r : reg => (r, Unexpr Assign (Reg r))) l) rm rmdeopt /\
                        agree rm rmdeopt (fold_right PositiveSet.add PositiveSet.empty l)).
  { intros l NODUP. induction l; intros.
    - simpl in H. simpl. exists empty_regmap. split. constructor.
      intros r IN. inv IN.
    - specialize (defined_ind a l rm NODUP H). intros H1.
      apply IHl in H1.
      2: { apply NoDup_cons_iff in NODUP. destruct NODUP. auto. }
      destruct H1 as [rmdeopt [UPDATE AGREE]].
      assert (GETA: exists va, rm ! a = Some va).
      { apply H. simpl. left. auto. }
      destruct GETA as [va GETA].
      exists (rmdeopt # a <- va). split.
      + simpl. constructor.
        * constructor. econstructor; eauto. constructor. eauto. constructor.
        * eapply udpate_more; eauto. apply NoDup_cons_iff in NODUP.
          destruct NODUP. auto.
      + intros r. specialize (AGREE r). poseq_destr r a.
        * rewrite PTree.gss. auto.
        * intros. rewrite PTree.gro in AGREE; auto. rewrite PTree.gso; auto.
          apply AGREE. simpl in H0.
          apply PositiveSet.add_spec in H0 as [contra | IN]; auto.
          apply HEQ in contra. destruct contra.
  }
  intros. specialize (H (PositiveSet.elements rs')).
  assert (NoDup (PositiveSet.elements rs')) by (apply nodup_elements).
  apply H with rm in H2.
  - destruct H2 as [rmdeopt [UPDATE AGREE]]. exists rmdeopt. split; auto.
    unfold agree. intros r IN. apply AGREE. apply fold_elements. auto.
  - unfold defined in H0. intro. rewrite <- PSin_in. intros IN. apply H0. auto.
Qed.

Lemma deopt_subset_agree:
  forall rm rs rs' newrm,
    defined rm (DefFlatRegset.Inj rs) ->
    PositiveSet.Subset rs' rs ->
    update_regmap (identity_varmap rs') rm newrm ->
    agree rm newrm rs'.
Proof.
  intros. apply defined_deopt_subset_agree with rm rs rs' in H; auto.
  destruct H as [rmdeopt [UPDATE AGREE]].
  eapply ir_properties.update_regmap_determ in UPDATE; eauto. subst. auto.
Qed.

(* If we apply update_regmap with the identity over a given regset, the 
   resulting regmap will be undefined outside of the regset *)
Lemma update_not_captured:
  forall rm newrm rs r,
    ~ PositiveSet.In r rs ->
    update_regmap (identity_varmap rs) rm newrm ->
    newrm ! r = None.
Proof.
  intros rm newrm rs r. rewrite PSin_in. 
  assert (forall l r rm newrm,
             ~ In r l ->
             update_regmap (map (fun r : reg => (r, Unexpr Assign (Reg r))) l) rm newrm ->
             newrm ! r = None).
  { induction l; intros.
    - inv H0. unfold empty_regmap. apply PTree.gempty.
    - inv H0. poseq_destr r0 a.
      + simpl in H. exfalso. apply H. left. auto.
      + rewrite PTree.gso; auto. eapply IHl.
        2: { apply UPDATE. }
        intros IN. apply H. simpl. right. auto. }
  apply H.
Qed.

(** * Properties of clean_label_list *)
Lemma nodup_clean:
  forall def l c,
    NoDup (clean_label_list def c l).
Proof.
  intros def l c. unfold clean_label_list.
  assert (ND: NoDup (remove_dup l)).
  { unfold remove_dup. apply NoDup_nodup. }
  unfold filter_unused.
  assert (P: forall X (li:list X) f, NoDup li -> NoDup (filter f li)).
  { intros X li f H. induction li; simpl. constructor.
    destruct (f a) eqn:FA.
    - constructor.
      + unfold not. intros. apply filter_In in H0. destruct H0. inv H. apply H4. auto.
      + apply IHli. inv H. auto.
    - apply IHli. inv H. auto. }
  apply P. auto.
Qed.

Definition used (l:list label) (c:code) :=
  forall lbl, In lbl l -> exists i, c ! lbl = Some i.

Lemma used_clean:
  forall def l c, used (clean_label_list def c l) c.
Proof.
  unfold used. intros def l c lbl IN. unfold clean_label_list in IN.
  apply filter_In in IN as [IN _]. apply filter_In in IN as [IN USED].
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

(** * Matching the stack and properties  *)
(* Matching stackframes: a version may have been replaced with its optimized version *)
Inductive match_stackframe (v:version) (fid:fun_id) (l:list label) (live:live_abs_state) (def:def_abs_state): stackframe -> stackframe -> Prop :=
| frame_same:              (* when doing a call from an unoptimized function *)
    forall r v' lbl rms,
      (match_stackframe v fid l live def) (Stackframe r v' lbl rms) (Stackframe r v' lbl rms)
| frame_deopt:             (* when doing a call after deoptimization *)
    forall r lbl rms rmo
      (AGREE: forall retval, agree (rms#r<-retval) (rmo#r<-retval) (live_dr_transf (ver_code v) lbl (live_absstate_get lbl live))),
      (match_stackframe v fid l live def) (Stackframe r v lbl rms) (Stackframe r v lbl rmo)
| frame_opt:               (* when doing a call from the optimized version *)
    forall r lbl rms vins
      (FS_INSERT: fs_insert_version v fid l live def = OK vins)
      (DEF: forall retval, defined (rms#r<-retval) (def_absstate_get lbl def)),
      (match_stackframe v fid l live def) (Stackframe r v lbl rms) (Stackframe r vins lbl rms).

(* Generalizing match_stackframe to the entire stack *)
Inductive match_stack (v:version) (fid:fun_id) (l:list label) (live:live_abs_state) (def:def_abs_state): stack -> stack -> Prop :=
| match_nil:
    (match_stack v fid l live def) nil nil
| match_cons:
    forall s s' sf sf'
      (MS: (match_stack v fid l live def) s s')
      (MSF: (match_stackframe v fid l live def) sf sf'),
      (match_stack v fid l live def) (sf::s) (sf'::s').

Lemma match_stackframe_same:
  forall v fid l live def sf,
    (match_stackframe v fid l live def) sf sf.
Proof.
  intros v fid l live def sf. destruct sf. apply frame_same.
Qed.

Lemma match_stack_same:
  forall s v fid l live def,
    (match_stack v fid l live def) s s.
Proof.
  intros s v fid l live def. induction s; constructor. auto. apply match_stackframe_same.
Qed.

Lemma match_app:
  forall synth s s' v fid l live def,
    (match_stack v fid l live def) s s' ->
    (match_stack v fid l live def) (synth++s) (synth++s').
Proof.
  intros. induction synth.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. apply match_cons. auto. apply match_stackframe_same.
Qed.

Lemma app_match:
  forall synth synthopt s s' v fid l live def,
    (match_stack v fid l live def) s s' ->
    (match_stack v fid l live def) synth synthopt ->
    (match_stack v fid l live def) (synth++s) (synthopt++s').
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

Inductive match_states (p:program) (v:version) (fid:fun_id) (lbllist:list label) (live:live_abs_state) (def:def_abs_state): fs_index -> specIR.state -> specIR.state -> Prop :=
| fs_match:                (* matching at a new Framestate in the optimized version *)
    forall vins s s' rms ms lbl
      (MATCHSTACK: (match_stack v fid lbllist live def) s s')
      (DEF: defined rms (def_absstate_get lbl def))
      (OPT: fs_insert_version v fid lbllist live def = OK vins)
      (IN: In lbl lbllist),
      (match_states p v fid lbllist live def) One (State s v lbl rms ms) (State s' vins lbl rms ms)

| shift_match:                     (* matching at a shifted instruction *)
    forall vins s s' rms ms lbl fresh
      (MATCHSTACK: (match_stack v fid lbllist live def) s s')
      (DEF: defined rms (def_absstate_get lbl def))
      (OPT: fs_insert_version v fid lbllist live def = OK vins)
      (NOT_IN: ~ In fresh lbllist)
      (SAME_CODE: (ver_code v) # lbl = (ver_code vins) # fresh),
      (match_states p v fid lbllist live def) Zero (State s v lbl rms ms) (State s' vins fresh rms ms)

| opt_match:                        (* matching inside the optimized version *)
    forall vins s s' lbl rms ms
      (MATCHSTACK: (match_stack v fid lbllist live def) s s')
      (DEF: defined rms (def_absstate_get lbl def))
      (OPT: fs_insert_version v fid lbllist live def = OK vins)
      (NOTIN: ~ In lbl lbllist),
      (match_states p v fid lbllist live def) Zero (State s v lbl rms ms) (State s' vins lbl rms ms)

| refl_match:                   (* matching outside of the optimized version *)
    forall v' s s' pc rms ms
      (MATCHSTACK: (match_stack v fid lbllist live def) s s'),
      (match_states p v fid lbllist live def) Zero (State s v' pc rms ms) (State s' v' pc rms ms)

| deopt_match:   (* matching after deoptimization at the inserted Framestates *)
    forall s s' pc rms rmo ms
      (MATCHSTACK: (match_stack v fid lbllist live def) s s')
      (AGREE: agree rms rmo (live_dr_transf (ver_code v) pc (live_absstate_get pc live))),
      (match_states p v fid lbllist live def) Zero (State s v pc rms ms) (State s' v pc rmo ms)

| final_match:                  (* matching final states *)
    forall retval ms,
      (match_states p v fid lbllist live def) One (Final retval ms) (Final retval ms).

(** * Code preservation properties  *)
Lemma code_preservation':        (* use at opt_match *)
  forall vbase vins fid l_fs lbl live def,
    fs_insert_version vbase fid l_fs live def = OK vins ->
    ~ In lbl l_fs ->
    forall iopt isrc,
      (ver_code vins) # lbl = Some iopt ->
      (ver_code vbase) # lbl = Some isrc ->
      iopt = isrc.
Proof.
  intros vbase vins fid l_fs lbl live def OPT NOTIN iopt isrc CODEOPT CODESRC.
  unfold fs_insert_version in OPT. repeat do_ok.
  assert (H: forall cs co, insert_list_framestate (ver_code vbase) cs fid l_fs live def = OK co ->
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
  forall p p' s s' rms rmo ms t news vbase vins fid l_fs lbl live def,
    fs_insert_version vbase fid l_fs live def = OK vins ->
    ~ In lbl l_fs ->
    safe (specir_sem p) (State s vbase lbl rms ms) ->
    Step (specir_sem p') (State s' vins lbl rmo ms) t news ->
    (ver_code vbase) # lbl = (ver_code vins) # lbl.
Proof.
  intros p p' s s' rms rmo ms t news vbase vins fid l_fs lbl live def H H0 H1 H2.
  apply safe_code in H1 as [isrc CODESRC]. apply step_code in H2 as [iopt CODEOPT].
  rewrite CODESRC. rewrite CODEOPT. f_equal. symmetry. eapply code_preservation'; eauto.
Qed.


(* The pass  cannot remove any code *)
Lemma more_code:
  forall vbase vins fid l_fs lbl live def,
    fs_insert_version vbase fid l_fs live def = OK vins ->
    (ver_code vins) # lbl = None ->
    (ver_code vbase) # lbl = None.
Proof.
  intros vbase vins fid l_fs lbl live def OPT CODE.
  unfold fs_insert_version in OPT. repeat do_ok.
  assert (H: forall cs co, insert_list_framestate (ver_code vbase) cs fid l_fs live def = OK co -> co ! lbl = None -> cs ! lbl = None).
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
  forall base_c cs co fid lbl fs_lbl live def,
    insert_single_framestate base_c cs fid fs_lbl live def = OK co ->
    co ! lbl = None ->
    cs ! lbl = None.
Proof.
  intros base_c cs co fid lbl fs_lbl live def H H0. unfold insert_single_framestate in H. repeat do_ok.
  poseq_destr fs_lbl lbl.
  - rewrite PTree.gss in H0. inv H0.
  - rewrite PTree.gso in H0; auto.
    poseq_destr (fresh_label (Pos.add fs_lbl spacing) cs) lbl.
    + rewrite PTree.gss in H0. eapply fresh_label_correct. eauto.
    + rewrite PTree.gso in H0; auto.
Qed.

(* The code is preserved outside of the list of labels *)
Lemma code_preserved:
  forall fid lbl i l live def base_c cs co,
    insert_list_framestate base_c cs fid l live def = OK co ->
    cs ! lbl = Some i ->
    ~ In lbl l ->
    co ! lbl = Some i.
Proof.
  intros fid lbl i l live def base_c. induction l; intros.
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
  forall l base_c cs co fid lbl live def,
    used l cs ->
    insert_single_framestate base_c cs fid lbl live def = OK co ->
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
  forall vbase vins fid l_fs lbl live def,
    fs_insert_version vbase fid l_fs live def = OK vins ->
    In lbl l_fs ->
    NoDup l_fs ->
    used l_fs (ver_code vbase) ->
    (exists freshlbl rs_def rs_live,
        def_absstate_get lbl def = DefFlatRegset.Inj rs_def /\
        live_dr_transf (ver_code vbase) lbl (live_absstate_get lbl live) = rs_live /\
        (ver_code vins) # lbl = Some (Framestate (fid,lbl) (identity_varmap (PositiveSet.inter rs_def rs_live)) nil freshlbl) /\
        (ver_code vbase) # freshlbl = None /\
        exists i, (ver_code vbase) # lbl = Some i /\ (ver_code vins) # freshlbl = Some i).
Proof.
  intros vbase vins fid l_fs lbl live def OPT IN NODUP DEF.
  unfold fs_insert_version in OPT. repeat do_ok.
  assert (forall cs co, insert_list_framestate (ver_code vbase) cs fid l_fs live def = OK co ->
                        In lbl l_fs -> used l_fs cs ->
                        exists freshlbl rs_def rs_live,
                          def_absstate_get lbl def = DefFlatRegset.Inj rs_def /\
                          live_dr_transf (ver_code vbase) lbl (live_absstate_get lbl live) = rs_live /\
                          co ! lbl = Some (Framestate (fid,lbl) (identity_varmap (PositiveSet.inter rs_def rs_live)) nil freshlbl) /\
                          cs ! freshlbl = None /\
                          exists i, cs ! lbl = Some i /\
                                    co ! freshlbl = Some i).
  { clear HDO IN. induction l_fs; intros.
    - simpl in H. inv H. inv H0.
    - simpl in H. repeat do_ok. apply nodup_cons_in in H0; auto.
      destruct H0 as [[EQ NOTIN] | [DIFF IN]].
      + subst. unfold insert_single_framestate in HDO. repeat do_ok.
        exists (fresh_label (Pos.add a spacing) cs). exists r.
        exists (live_dr_transf (ver_code vbase) a (live_absstate_get a live)).
        split; try split; auto. unfold defined_rs in HDO1. destruct (def_absstate_get a def); inv HDO1. auto. split.
        * eapply code_preserved; eauto. rewrite PTree.gss. auto.
        * split. { eapply fresh_label_correct. eauto. }
          exists i. split; auto. poseq_destr (fresh_label (Pos.add a spacing) cs) a.
          erewrite fresh_label_correct in HDO; eauto. inv HDO.
          eapply code_preserved; eauto. rewrite PTree.gso; auto. rewrite PTree.gss. auto.
          unfold not; intro. apply used_cons in H1. apply H1 in H. destruct H.
          erewrite fresh_label_correct in H; auto. inv H.
      + inv NODUP. apply used_cons in DEF as DEF'. apply used_cons in H1 as DEF''.
        assert (used l_fs c0) by (eapply used_insert_single_framestate; eauto).
        specialize (IHl_fs H4 DEF' c0 co H3 IN H). destruct IHl_fs as [freshlbl [rs_def [rs_live [GETDEF [GETLIVE [CO [FRESH [i [C0 CO']]]]]]]]].
        exists freshlbl. exists rs_def. exists rs_live.
        split; auto. split; auto. split; auto. split.
        { eapply more_code'; eauto. }
        exists i. split; auto.
        unfold insert_single_framestate in HDO. repeat do_ok. rewrite PTree.gso in C0; auto.
        poseq_destr (fresh_label (Pos.add a spacing) cs) lbl.
        * apply DEF'' in IN. destruct IN. erewrite fresh_label_correct in H0; eauto. inv H0.
        * rewrite PTree.gso in C0; auto. }
  apply H; auto.
Qed.

Lemma code_notfs:               (* for progress preservation *)
  forall vbase vins fid l_fs lbl live def,
    fs_insert_version vbase fid l_fs live def = OK vins ->
    ~ In lbl l_fs ->
    forall i, (ver_code vbase) # lbl = Some i ->
              (ver_code vins) # lbl = Some i.
Proof.
  assert (H: forall (l:list label) i lbl fid live def base_c cs co,
             insert_list_framestate base_c cs fid l live def = OK co ->
             ~ In lbl l ->
             cs # lbl = Some i ->
             co # lbl = Some i).
  { intros. generalize dependent cs.
    induction l; intros.
    - simpl in H. inv H. auto.
    - simpl in H. repeat do_ok. simpl in H0.
      assert (NOTIN: ~ In lbl l).
      { unfold not. intros. apply H0. right. auto. }
      assert (NOTA: a <> lbl).
      { unfold not. intros. apply H0. left. auto. }
      specialize (IHl NOTIN c H3). unfold insert_single_framestate in HDO.
      repeat do_ok. rewrite PTree.gso in IHl; auto.
      apply IHl. poseq_destr (fresh_label (Pos.add a spacing) cs) lbl.
      + erewrite fresh_label_correct in H1; auto. inv H1.
      + rewrite PTree.gso; auto. }
  intros vbase vins fid l_fs lbl live def H0 H1 i H2.
  unfold fs_insert_version in H0. repeat do_ok.
  eapply H in HDO; eauto.
Qed.


Ltac rmagreef :=
  match goal with
  | [H: eval_expr ?e ?rms ?v,
        H1: agree ?rms ?rmo ?live |- _] => eapply agree_eval_expr in H; eauto
  | [H: eval_list ?e ?rms ?v,
        H1: agree ?rms ?rmo ?live |- _] => eapply agree_eval_list in H; eauto
  | [H: eval_list_expr ?e ?rms ?v,
        H1: agree ?rms ?rmo ?live |- _] => eapply agree_eval_list_expr in H; eauto
  end.

Lemma progress_preserved:
  forall vbase vins fid l_fs live def s1 s2 p i,
    fs_insert_version vbase fid l_fs live def = OK vins ->
    find_base_version fid p = Some vbase ->
    match_states p vbase fid l_fs live def i s1 s2 ->
    safe (specir_sem p) s1 ->
    NoDup l_fs ->
    used l_fs (ver_code vbase) ->
    (exists r : value, final_state (set_version p fid vins) s2 r) \/
    (exists (t : trace) (s2' : Smallstep.state (specir_sem (set_version p fid vins))),
        Step (specir_sem (set_version p fid vins)) s2 t s2').
Proof.
  intros vbase vins fid l_fs live def s1 s2 p i OPTV FINDBASE MATCH SAFE NODUP DEF.
  inv MATCH.
  + rewrite OPT in OPTV. inv OPTV.
    right. exists E0. apply code_fs with (lbl:=lbl)in OPT as CODE; auto.
    destruct CODE as [freshlbl [rs_def [rs_live [GETDEF [GETLIVE [FSCODE [BASECODE [i SHIFTCODE]]]]]]]].
    rewrite GETDEF in DEF0. 
    exists (State s' vins freshlbl rms ms).
    assert (exists newrm,
               update_regmap (identity_varmap (PositiveSet.inter rs_def rs_live)) rms newrm /\
               agree rms newrm (PositiveSet.inter rs_def rs_live))
      as [newrm [UPDATE' AGREE]].
    { eapply defined_deopt_subset_agree; eauto.
      intros r IN'. apply PositiveSet.inter_spec in IN' as [IN' _]. auto. }
    eapply nd_exec_Framestate_go_on.
    econstructor; eauto; try constructor.
    simpl. rewrite <- base_version_unchanged. eauto.
  + apply safe_step in SAFE. destruct SAFE as [s'' [t STEP]].
    right. rewrite OPT in OPTV. inv OPTV. inv STEP.
    * exists t.
      { inv STEP0; rewrite SAME_CODE in CODE.
        + exists (State s' vins next rms ms).
          apply nd_exec_lowered. eapply exec_Nop. eauto.
        + exists (State s' vins next (rms#reg<-v) ms).
          apply nd_exec_lowered. eapply exec_Op; eauto.
        + exists (State s' vins next newrm ms).
          apply nd_exec_lowered. eapply exec_Move; eauto.
        + exists (State s' vins (pc_cond v iftrue iffalse) rms ms).
          apply nd_exec_lowered. eapply exec_Cond; eauto.
        + poseq_destr fid0 fid.
          * eapply find_function_same with (v:=vins) in FINDF.
            exists (State (Stackframe retreg vins next rms ::s') (current_version (set_version_function vins func)) (ver_entry (current_version (set_version_function vins func))) newrm ms).
            apply nd_exec_lowered. eapply exec_Call; eauto.
          * simpl in FINDF.
            eapply find_function_unchanged with (fid':=fid) (v:=vins) in HEQ.
            rewrite HEQ in FINDF.
            exists (State (Stackframe retreg vins next rms ::s') (current_version (func)) (ver_entry (current_version (func))) newrm ms).
            apply nd_exec_lowered. eapply exec_Call; eauto.
        + inv MATCHSTACK. inv MSF.
          * exists (State s'0 fprev next (rmprev#retreg<-retval) ms).
            apply nd_exec_lowered. eapply exec_Return; eauto.
          * exists (State s'0 fprev next (rmo#retreg<-retval) ms).
            apply nd_exec_lowered. eapply exec_Return; eauto.
          * exists (State s'0 vins0 next (rmprev#retreg<-retval) ms).
            apply nd_exec_lowered. eapply exec_Return; eauto.
        + inv MATCHSTACK. exists (Final retval ms).
          apply nd_exec_lowered. eapply exec_Return_Final; eauto.
        + exists (State s' vins next rms ms).
          apply nd_exec_lowered. eapply exec_Printexpr; eauto.
        + exists (State s' vins next rms ms).
          apply nd_exec_lowered. eapply exec_Printstring. auto.
        + exists (State s' vins next rms newms).
          apply nd_exec_lowered. eapply exec_Store; eauto.
        + exists (State s' vins next (rms#reg<-val) ms).
          apply nd_exec_lowered. eapply exec_Load; eauto.
        + exists (State s' vins next rms ms).
          apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
        + rewrite synth_frame_unchanged in SYNTH.
          erewrite base_version_unchanged in FINDF.
          exists (State (synth ++ s') newver la newrm ms).
          apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
          * simpl in FINDF. simpl. eauto.
          * simpl in SYNTH. simpl. eauto. }
    * exists E0. exists (State s' vins next rms ms). inv DEOPT_COND.
      rewrite synth_frame_unchanged in SYNTH.
      rewrite SAME_CODE in CODE. eapply nd_exec_Framestate_go_on.
      econstructor; eauto.
      ** simpl. rewrite <- base_version_unchanged. eauto.
      ** simpl in SYNTH. simpl. eauto.
    * exists E0. exists (State s' vins next rms ms). inv DEOPT_COND.
      rewrite synth_frame_unchanged in SYNTH.
      rewrite SAME_CODE in CODE.
      eapply nd_exec_Framestate_go_on.
      econstructor; eauto.
      ** simpl. rewrite <- base_version_unchanged. eauto.
      ** simpl in SYNTH. simpl. eauto.
  + rewrite OPT in OPTV. inv OPTV. apply safe_step in SAFE as SAFE'.
    destruct SAFE' as [s'' [t STEP]].
    specialize (code_notfs vbase vins fid l_fs lbl live def OPT NOTIN).
    intros SAME_CODE.
    assert ((ver_code vbase) ! lbl = (ver_code vins) ! lbl) as SAME_CODE'.
    {
      destruct ((ver_code vbase) ! lbl) eqn:Hbase.
      - symmetry. auto.
      - apply safe_code in SAFE as [i BASE]. rewrite BASE in Hbase. discriminate Hbase.
    }
    right. inv STEP.
    * exists t.
      { inv STEP0; apply SAME_CODE in CODE.
        + exists (State s' vins next rms ms).
          apply nd_exec_lowered. eapply exec_Nop. eauto.
        + exists (State s' vins next (rms#reg<-v) ms).
          apply nd_exec_lowered. eapply exec_Op; eauto.
        + exists (State s' vins next newrm ms).
          apply nd_exec_lowered. eapply exec_Move; eauto.
        + exists (State s' vins (pc_cond v iftrue iffalse) rms ms).
          apply nd_exec_lowered.
          eapply exec_Cond; eauto.
        + poseq_destr fid0 fid.
          * eapply find_function_same with (v:=vins) in FINDF.
            exists (State (Stackframe retreg vins next rms ::s') (current_version (set_version_function vins func)) (ver_entry (current_version (set_version_function vins func))) newrm ms).
            apply nd_exec_lowered. eapply exec_Call; eauto.
          * simpl in FINDF. eapply find_function_unchanged with (fid':=fid) (v:=vins) in HEQ.
            rewrite HEQ in FINDF.
            exists (State (Stackframe retreg vins next rms ::s') (current_version (func)) (ver_entry (current_version (func))) newrm ms).
            apply nd_exec_lowered. eapply exec_Call; eauto.
        + inv MATCHSTACK. inv MSF.
          * exists (State s'0 fprev next (rmprev#retreg<-retval) ms).
            apply nd_exec_lowered. eapply exec_Return; eauto.
          * exists (State s'0 fprev next (rmo#retreg<-retval) ms).
            apply nd_exec_lowered. eapply exec_Return; eauto.
          * exists (State s'0 vins0 next (rmprev#retreg<-retval) ms).
            apply nd_exec_lowered. eapply exec_Return; eauto.
        + inv MATCHSTACK. exists (Final retval ms).
          apply nd_exec_lowered. eapply exec_Return_Final; eauto.
        + exists (State s' vins next rms ms).
          apply nd_exec_lowered. eapply exec_Printexpr; eauto.
        + exists (State s' vins next rms ms).
          apply nd_exec_lowered. eapply exec_Printstring. auto.
        + exists (State s' vins next rms newms).
          apply nd_exec_lowered. eapply exec_Store; eauto.
        + exists (State s' vins next (rms#reg<-val) ms).
          apply nd_exec_lowered. eapply exec_Load; eauto.
        + exists (State s' vins next rms ms).
          apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
        + rewrite synth_frame_unchanged in SYNTH.
          erewrite base_version_unchanged in FINDF.
          exists (State (synth ++ s') newver la newrm ms).
          apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
          * simpl in FINDF. simpl. eauto.
          * apply SYNTH. }
    * exists E0. exists (State s' vins next rms ms). inv DEOPT_COND.
      rewrite synth_frame_unchanged in SYNTH. eapply nd_exec_Framestate_go_on.
      econstructor; eauto.
      ** simpl. rewrite <- base_version_unchanged. eauto.
      ** simpl in SYNTH. simpl. eauto.
    * exists E0. exists (State s' vins next rms ms). inv DEOPT_COND.
      rewrite synth_frame_unchanged in SYNTH. eapply nd_exec_Framestate_go_on.
      econstructor; eauto.
      ** simpl. rewrite <- base_version_unchanged. eauto.
      ** simpl in SYNTH. simpl. eauto.
  + right. apply safe_step in SAFE. destruct SAFE as [s'' [t STEP]].
    inv STEP.
    * exists t.
      { inv STEP0.
        + exists (State s' v' next rms ms).
          apply nd_exec_lowered. eapply exec_Nop. eauto.
        + exists (State s' v' next (rms#reg<-v) ms).
          apply nd_exec_lowered. eapply exec_Op; eauto.
        + exists (State s' v' next newrm ms).
          apply nd_exec_lowered. eapply exec_Move; eauto.
        + exists (State s' v' (pc_cond v iftrue iffalse) rms ms).
          apply nd_exec_lowered. eapply exec_Cond; eauto.
        + poseq_destr fid0 fid.
          * eapply find_function_same with (v:=vins) in FINDF.
            exists (State (Stackframe retreg v' next rms ::s') (current_version (set_version_function vins func)) (ver_entry (current_version (set_version_function vins func))) newrm ms).
            apply nd_exec_lowered. eapply exec_Call; eauto.
          * simpl in FINDF. eapply find_function_unchanged with (fid':=fid) (v:=vins) in HEQ.
            rewrite HEQ in FINDF.
            exists (State (Stackframe retreg v' next rms ::s') (current_version (func)) (ver_entry (current_version (func))) newrm ms).
            apply nd_exec_lowered. eapply exec_Call; eauto.
        + inv MATCHSTACK. inv MSF.
          * exists (State s'0 fprev next (rmprev#retreg<-retval) ms).
            apply nd_exec_lowered. eapply exec_Return; eauto.
          * exists (State s'0 fprev next (rmo#retreg<-retval) ms).
            apply nd_exec_lowered. eapply exec_Return; eauto.
          * exists (State s'0 vins0 next (rmprev#retreg<-retval) ms).
            apply nd_exec_lowered. eapply exec_Return; eauto.
        + inv MATCHSTACK. exists (Final retval ms).
          apply nd_exec_lowered. eapply exec_Return_Final; eauto.
        + exists (State s' v' next rms ms).
          apply nd_exec_lowered. eapply exec_Printexpr; eauto.
        + exists (State s' v' next rms ms).
          apply nd_exec_lowered. eapply exec_Printstring. auto.
        + exists (State s' v' next rms newms).
          apply nd_exec_lowered. eapply exec_Store; eauto.
        + exists (State s' v' next (rms#reg<-val) ms).
          apply nd_exec_lowered. eapply exec_Load; eauto.
        + exists (State s' v' next rms ms).
          apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
        + rewrite synth_frame_unchanged in SYNTH.
          erewrite base_version_unchanged in FINDF.
          exists (State (synth ++ s') newver la newrm ms).
          apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
          * simpl in FINDF. simpl. eauto.
          * apply SYNTH. }
    * exists E0. exists (State s' v' next rms ms). inv DEOPT_COND.
      rewrite synth_frame_unchanged in SYNTH.
      eapply nd_exec_Framestate_go_on.
      econstructor; eauto.
      ** simpl. rewrite <- base_version_unchanged. eauto.
      ** simpl in SYNTH. simpl. eauto.
    * exists E0. exists (State s' v' next rms ms). inv DEOPT_COND.
      rewrite synth_frame_unchanged in SYNTH.
      eapply nd_exec_Framestate_go_on.
      econstructor; eauto.
      ** simpl. rewrite <- base_version_unchanged. eauto.
      ** simpl in SYNTH. simpl. eauto.
  + right. apply safe_step in SAFE. destruct SAFE as [s'' [t STEP]].
    inv STEP.
    * exists t.
      { inv STEP0; unfold live_dr_transf in AGREE; rewrite CODE in AGREE.
        + exists (State s' vbase next rmo ms).
          apply nd_exec_lowered. eapply exec_Nop. eauto.
        + exists (State s' vbase next (rmo#reg<-v) ms). rmagreef.
          apply nd_exec_lowered. eapply exec_Op; eauto.
        + apply agree_sym in AGREE.
          eapply agree_update_movelist in UPDATE as [rm1u [UPDATE AGREE']]; eauto.
          exists (State s' vbase next rm1u ms).
          apply nd_exec_lowered. eapply exec_Move; eauto.
        + exists (State s' vbase (pc_cond v iftrue iffalse) rmo ms). rmagreef.
          apply nd_exec_lowered. eapply exec_Cond; eauto.
        + poseq_destr fid0 fid.
          * eapply find_function_same with (v:=vins) in FINDF.
            exists (State (Stackframe retreg vbase next rmo ::s') (current_version (set_version_function vins func)) (ver_entry (current_version (set_version_function vins func))) newrm ms).
            rmagreef. apply nd_exec_lowered. eapply exec_Call; eauto.
          * simpl in FINDF. eapply find_function_unchanged with (fid':=fid) (v:=vins) in HEQ.
            rewrite HEQ in FINDF.
            exists (State (Stackframe retreg vbase next rmo ::s') (current_version (func)) (ver_entry (current_version (func))) newrm ms).
            rmagreef. apply nd_exec_lowered. eapply exec_Call; eauto.
        + inv MATCHSTACK. inv MSF.
          * exists (State s'0 fprev next (rmprev#retreg<-retval) ms).
            rmagreef. apply nd_exec_lowered. eapply exec_Return; eauto.
          * exists (State s'0 fprev next (rmo0#retreg<-retval) ms).
            rmagreef. apply nd_exec_lowered. eapply exec_Return; eauto.
          * exists (State s'0 vins0 next (rmprev#retreg<-retval) ms).
            rmagreef. apply nd_exec_lowered. eapply exec_Return; eauto.
        + inv MATCHSTACK. exists (Final retval ms). rmagreef.
          apply nd_exec_lowered. eapply exec_Return_Final; eauto.
        + exists (State s' vbase next rmo ms). rmagreef.
          apply nd_exec_lowered. eapply exec_Printexpr; eauto.
        + exists (State s' vbase next rmo ms).
          apply nd_exec_lowered. eapply exec_Printstring. auto.
        + exists (State s' vbase next rmo newms).
          rmagreef. 2: { eapply expr_live_agree. eauto. }
          rmagreef. apply nd_exec_lowered. eapply exec_Store; eauto.          
        + exists (State s' vbase next (rmo#reg<-val) ms). rmagreef.
          apply nd_exec_lowered. eapply exec_Load; eauto.
        + exists (State s' vbase next rmo ms).
          rmagreef. 2: { destruct tgt. eauto. }
          apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
        + rmagreef. apply agree_sym in AGREE.
          eapply agree_synthesize_frame in SYNTH; eauto.
          2: { eapply varmap_live_agree. eapply expr_list_live_agree. eauto. }
          rewrite synth_frame_unchanged in SYNTH.
          erewrite base_version_unchanged in FINDF.
          exists (State (synth ++ s') newver la newrm ms).
          simpl in FINDF. simpl in SYNTH.
          apply nd_exec_lowered. eapply exec_Assume_fails; simpl; eauto.
          eapply agree_update_regmap; eauto.
          eapply expr_list_live_agree. eauto. }
    * exists E0. exists (State s' vbase next rmo ms). inv DEOPT_COND.
      unfold live_dr_transf in AGREE. rewrite CODE in AGREE.
      rewrite synth_frame_unchanged in SYNTH.
      apply agree_sym in AGREE. eapply agree_update_regmap in UPDATE; eauto.
      eapply agree_synthesize_frame in SYNTH; eauto.
      2: { eapply varmap_live_agree. eauto. }
      eapply nd_exec_Framestate_go_on.
      simpl in SYNTH. econstructor; simpl; eauto. 
      rewrite <- base_version_unchanged. eauto.
    * exists E0. exists (State s' vbase next rmo ms). inv DEOPT_COND.
      unfold live_dr_transf in AGREE. rewrite CODE in AGREE.
      rewrite synth_frame_unchanged in SYNTH.
      apply agree_sym in AGREE. eapply agree_update_regmap in UPDATE; eauto.
      eapply agree_synthesize_frame in SYNTH; eauto.
      2: { eapply varmap_live_agree. eauto. }
      eapply nd_exec_Framestate_go_on.
      simpl in SYNTH. econstructor; simpl; eauto. 
      rewrite <- base_version_unchanged. eauto.      
  + left. exists retval. constructor.
Qed.

Ltac def_ok :=
  match goal with
  | [CODE: (ver_code ?vsrc) ! ?lbl = Some ?i |- _] =>
    eapply def_analyze_correct; eauto; simpl; auto; unfold def_dr_transf; try rewrite CODE; auto
  end.

Ltac rmagreeb :=
  match goal with
  | [ |- agree (?rm1 # ?r <- ?v) (?rm2 # ?r <- ?v) ?rs] => apply agree_insert; auto
  | [H: eval_expr ?e ?rmo ?v,
        H1: agree ?rms ?rmo ?rs |- _] => eapply agree_eval_expr in H; apply agree_sym in H1; eauto
  | [H: eval_list ?e ?rmo ?v,
        H1: agree ?rms ?rmo ?rs |- _] => eapply agree_eval_list in H; apply agree_sym in H1; eauto
  | [H: eval_list_expr ?e ?rmo ?v,
        H1: agree ?rms ?rmo ?rs |- _] => eapply agree_eval_list_expr in H; apply agree_sym in H1; eauto
  end.

(* The diagram of a backward simulation for lowered steps *)
(* We only require the same code on both sides, and reuse this lemma for both opt_match and shift_match *)
Lemma lowered_diagram:
  forall p vbase fid l_fs live def vins lblsrc lblopt s s' rms ms t s2' f
         (OPT: fs_insert_version vbase fid l_fs live def = OK vins)
         (FINDF: find_function fid p = Some f)
         (NOOPT: fn_opt f = None)
         (BASE': fn_base f = vbase)
         (MATCHSTACK: match_stack vbase fid l_fs live def s s')
         (SAME_CODE: (ver_code vbase) ! lblsrc = (ver_code vins) ! lblopt)
         (DEFREGS: defined_regs_analysis (ver_code vbase) (fn_params f) (ver_entry vbase) = Some def)
         (LIVENESS: liveness_analyze vbase = Some live)
         (DEF: defined rms (def_absstate_get lblsrc def))
         (STEP: lowered_step (set_version p fid vins) (State s' vins lblopt rms ms) t s2')
         (SAFE: safe (specir_sem p) (State s vbase lblsrc rms ms)),
  exists (i: fs_index) (s1': Smallstep.state (specir_sem p)),
    (SPlus (specir_sem p) (State s vbase lblsrc rms ms) t s1' \/
     Star (specir_sem p) (State s vbase lblsrc rms ms) t s1' /\ fs_order i Zero) /\
    match_states p vbase fid l_fs live def i s1' s2'.
Proof.
  intros p vbase fid l_fs live def vins lblsrc lblopt s s' rms ms t s2' f OPT FINDF NOOPT BASE' MATCHSTACK SAME_CODE DEFREGS LIVENESS DEF STEP SAFE.
  assert (BASE: find_base_version fid p = Some vbase).
  { unfold find_base_version. rewrite FINDF. f_equal. auto. } clear BASE'.
  inv STEP; rewrite CODE in SAME_CODE.
  - destruct (in_or_not next l_fs) as [IN | NOTIN].
    + exists One. exists (State s vbase next rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Nop; eauto.
      * eapply fs_match; eauto. def_ok. rewrite SAME_CODE. auto.
    + exists Zero. exists (State s vbase next rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Nop; eauto.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.
  - destruct (in_or_not next l_fs) as [IN | NOTIN].
    + exists One. exists (State s vbase next (rms # reg <- v) ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Op; eauto.
      * eapply fs_match; auto. def_ok. rewrite SAME_CODE.
        apply define_insert. auto.
    + exists Zero. exists (State s vbase next (rms # reg <- v) ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Op; eauto.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE.
        apply define_insert. auto.
  - destruct (in_or_not next l_fs) as [IN | NOTIN].
    + exists One. exists (State s vbase next newrm ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Move; eauto.
      * eapply fs_match; auto. def_ok. rewrite SAME_CODE.
        eapply define_insert_list; eauto.
    + exists Zero. exists (State s vbase next newrm ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Move; eauto.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE.
        eapply define_insert_list; eauto.
  - destruct (in_or_not (pc_cond v iftrue iffalse) l_fs) as [IN | NOTIN].
    + exists One. exists (State s vbase (pc_cond v iftrue iffalse) rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Cond; eauto.
      * eapply fs_match; auto. def_ok. destruct v. destruct z; auto. rewrite SAME_CODE. auto.
    + exists Zero. exists (State s vbase (pc_cond v iftrue iffalse) rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Cond; eauto.
      * eapply opt_match; auto. def_ok. destruct v. destruct z; auto. rewrite SAME_CODE. auto.
  - poseq_destr fid fid0.
    +                           (* calling the optimized function *)
      assert (ISBASE: vbase = current_version f).
      { unfold find_base_version in BASE. rewrite FINDF in BASE. inv BASE.
        unfold current_version. rewrite NOOPT. auto. }
      assert (ISINS: vins = current_version func).
      { unfold current_version. eapply find_function_same in FINDF; eauto.
        rewrite FINDF0 in FINDF. inv FINDF. simpl. auto. }
      assert (SAME_ENTRY:ver_entry vbase = ver_entry vins).
      { unfold fs_insert_version in OPT. repeat do_ok. simpl. auto. }
      assert (SAME_PARAMS: fn_params f = fn_params func).
      { erewrite find_function_same in FINDF0; eauto. inv FINDF0.
        unfold set_version_function. auto. }
      destruct (in_or_not (ver_entry(current_version f)) l_fs) as [IN|NOTIN].
      * exists One. exists (State (Stackframe retreg vbase next rms :: s) (current_version f) (ver_entry (current_version f)) newrm ms). split.
        ** left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
           eapply same_params in FINDF0 as PARAMS; eauto. rewrite PARAMS. auto.
        ** rewrite <- ISBASE. rewrite <- ISINS.
           rewrite SAME_ENTRY. apply fs_match; auto.
           *** constructor; auto. constructor; auto.
               intro. def_ok. rewrite SAME_CODE. apply define_insert. auto.
           *** rewrite <- SAME_ENTRY. eapply def_analyze_init; eauto.
               rewrite SAME_PARAMS. eauto.
           *** rewrite <- ISBASE in IN. rewrite <- SAME_ENTRY. auto.
      * exists Zero. exists (State (Stackframe retreg vbase next rms :: s) (current_version f) (ver_entry (current_version f)) newrm ms). split.
        ** left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
           eapply same_params in FINDF0 as PARAMS; eauto. rewrite PARAMS. auto.
        ** rewrite <- ISBASE. rewrite <- ISINS.
           rewrite SAME_ENTRY. apply opt_match; auto.
           *** constructor; auto. constructor; auto.
               intro. def_ok. rewrite SAME_CODE. apply define_insert. auto.
           *** rewrite <- SAME_ENTRY. eapply def_analyze_init; eauto.
               rewrite SAME_PARAMS. eauto.
           *** rewrite <- ISBASE in NOTIN. rewrite <- SAME_ENTRY. auto.
    + exists Zero. exists (State (Stackframe retreg vbase next rms :: s) (current_version func) (ver_entry (current_version func)) newrm ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
        erewrite <- find_function_unchanged in FINDF0; auto.
      * apply refl_match; auto. constructor; auto. constructor; auto.
        intro. def_ok. rewrite SAME_CODE. apply define_insert. auto.
  - inv MATCHSTACK. inv MSF.
    + exists Zero. exists (State s1 fprev next (rmprev # retreg <- retval) ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
      * apply refl_match. auto.
    + exists Zero. exists (State s1 fprev next (rms0 # retreg <- retval) ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
      * apply deopt_match; auto.
    + rewrite FS_INSERT in OPT. inv OPT. (* returning into the optimized version *)
      destruct (in_or_not next l_fs).
      * exists One. exists (State s1 vbase next (rmprev#retreg<-retval) ms). split.
        ** left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
        ** eapply fs_match; eauto.
      * exists Zero. exists (State s1 vbase next (rmprev#retreg<-retval) ms). split.
        ** left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
        ** eapply opt_match; eauto.
  - inv MATCHSTACK. exists One. exists (Final retval ms). split.
    * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return_Final; eauto.
    * eapply final_match; eauto.
  - destruct (in_or_not next l_fs) as [IN | NOTIN].
    + exists One. exists (State s vbase next rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Printexpr; eauto.
      * eapply fs_match; auto. def_ok. rewrite SAME_CODE. auto.
    + exists Zero. exists (State s vbase next rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Printexpr; eauto.
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
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Store; eauto.
      * eapply fs_match; auto. def_ok. rewrite SAME_CODE. auto.
    + exists Zero. exists (State s vbase next rms newms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Store; eauto.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. auto.
  - destruct (in_or_not next l_fs) as [IN | NOTIN].
    + exists One. exists (State s vbase next (rms#reg<-val) ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Load; eauto.
      * eapply fs_match; eauto. def_ok. rewrite SAME_CODE.
        apply define_insert. auto.
    + exists Zero. exists (State s vbase next (rms#reg<-val) ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Load; eauto.
      * eapply opt_match; eauto. def_ok. rewrite SAME_CODE. apply define_insert. auto.
  - destruct (in_or_not next l_fs) as [IN | NOTIN].
    + exists One. exists (State s vbase next rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
      * eapply fs_match; auto. def_ok. rewrite SAME_CODE. auto.
    + exists Zero. exists (State s vbase next rms ms). split.
      * left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
      * eapply opt_match; auto. def_ok. rewrite SAME_CODE. auto.
  - apply <- synth_frame_unchanged in SYNTH. exists Zero.
    rewrite <- base_version_unchanged in FINDF0.
    exists (State (synth ++ s) newver la newrm ms). split.
    + left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
    + apply refl_match. apply match_app. auto.
Qed.

(* Proved directly with a backward simulation *)
Theorem framestate_insertion_correct:
  forall p fid lbllist newp,
    insert_framestate fid lbllist p = OK newp ->
    backward_internal_simulation p newp.
Proof.
  intros p fid lbllist newp OPT. unfold insert_framestate in OPT. repeat do_ok.
  rename HDO1 into FINDOPTF. rename d into def. rename l into live.
  set (l_fs := (clean_label_list def (ver_code (fn_base f)) lbllist)).
  rename v into vins. unfold check_no_opt in HDO0. destruct (fn_opt f) eqn:NO_OPT; inv HDO0.
  set (vbase := (fn_base f)). fold l_fs vbase in HDO2. rename v0 into vins.
  assert (OPTV: fs_insert_version vbase fid l_fs live def = OK vins) by auto.
  unfold fs_insert_version in HDO3. repeat do_ok.
  set (vins := {|ver_code := c; ver_entry := ver_entry vbase |}). fold vins in OPTV.
  apply Backward_internal_simulation with (bsim_order := fs_order) (bsim_match_states := match_states p vbase fid l_fs live def).
  - apply wfounded.
  - apply trans.

  - unfold reflexive_forge. intros synchro stack r1 s1 ms FORGE.
    destruct synchro; simpl in FORGE; repeat do_ok; simpl.
    + poseq_destr f0 fid.  (* is the called function the optimized one? *)
      * erewrite find_function_same; eauto. simpl. rewrite HDO1. simpl.
        rewrite FINDOPTF in HDO3. inv HDO3.
        assert (CURRENT:  vbase  = (current_version f1)).
        { unfold vbase. unfold current_version. rewrite NO_OPT. auto. }
        rewrite <- CURRENT.
        { destruct (in_or_not (ver_entry(current_version f1)) l_fs) as [IN|NOTIN]; repeat (esplit; eauto).
          - unfold vbase. eapply fs_match; eauto.
            + apply match_stack_same.
            + unfold clean_label_list in l_fs.
              apply interpreter_proof.init_regs_correct in HDO1.
              eapply def_analyze_init; eauto.
            + rewrite <- CURRENT in IN. unfold vbase in IN. auto.
          - eapply opt_match.
            + apply match_stack_same.
            + apply interpreter_proof.init_regs_correct in HDO1.
              eapply def_analyze_init; eauto.
            + auto.
            + rewrite <- CURRENT in NOTIN. auto.  }
      * erewrite <- find_function_unchanged; eauto. rewrite HDO3. simpl. rewrite HDO1. simpl.
        repeat (esplit; eauto). econstructor. apply match_stack_same.
    + destruct stack; try destruct s; inv FORGE.
      * repeat (esplit; eauto). constructor.
      * repeat (esplit; eauto). simpl. econstructor. apply match_stack_same.
    + destruct d. repeat do_ok. simpl. rewrite <- base_version_unchanged. rewrite HDO1. simpl.
      repeat (esplit; eauto). simpl. econstructor. apply match_stack_same.
    + inv FORGE. destruct r1; repeat (esplit; eauto).
      * simpl. eapply refl_match. apply match_stack_same.
      * simpl. eapply final_match.

  - intros i s1 s2 r MATCH SAFE FINAL. inv FINAL. inv MATCH. exists (Final r ms). split.
    apply star_refl. constructor.

  - intros. eapply progress_preserved; eauto. unfold find_base_version. rewrite FINDOPTF. eauto.
    apply nodup_clean. apply used_clean.

  - intros s2 t s2' STEP i s1 MATCH SAFE.
    assert (NODUP: NoDup l_fs) by apply nodup_clean.
    assert (DEF: used l_fs (ver_code vbase)) by apply used_clean.
    inv MATCH.

    + rewrite OPT in OPTV. inv OPTV. (* fs_match *)
      eapply code_fs in IN as [fresh [rs_def [rs_live [GETDEF [GETLIVE [FSCODE [FRESH [nextinstr [CODESRC CODEOPT]]]]]]]]]; eauto.
      inv STEP.
      { inv STEP0; rewrite CODE in FSCODE; inv FSCODE. }
      { exists Zero. exists (State s vbase lbl rms ms). split. (* stuttering, FS goes on  *)
        - right. split. 2:constructor. apply star_refl.
        - inv DEOPT_COND. rewrite CODE in FSCODE. inv FSCODE. inv SYNTH. eapply shift_match; auto.
          unfold not; intros. apply DEF in H as [i CODE']. rewrite CODE' in FRESH. inv FRESH.
          rewrite CODESRC. rewrite CODEOPT. auto. }
      { exists Zero. exists (State s vbase lbl rms ms). split. (* stuttering, FS deoptimizes *)
        - right. split. 2:constructor. apply star_refl.
        - inv DEOPT_COND. rewrite CODE in FSCODE. inv FSCODE. inv SYNTH. simpl.
          assert (BASE: vbase = newver).
          { simpl in FINDF. rewrite <- base_version_unchanged in FINDF. unfold find_base_version in FINDF.
            rewrite FINDOPTF in FINDF. inv FINDF. unfold vbase. auto. }
          rewrite <- BASE. eapply deopt_match; eauto.
          rewrite GETDEF in DEF0.
          eapply defined_deopt_subset_agree in DEF0 as DEF0'; eauto.
          2: { intros r IN. apply IN. }        
          destruct DEF0' as [rmdeopt [UPDATE' AGREE]].
          eapply deopt_subset_agree in UPDATE as AGREE'; eauto.
          2: { intros r IN. apply PositiveSet.inter_spec in IN as [IN _]. auto. }
          intros r IN.
          destruct (PositiveSet.mem r rs_def) eqn:Emem.
          + apply AGREE'. apply PositiveSet.inter_spec. split; auto.
          + assert (rms ! r = None).
            { unfold defined in DEF0. specialize (DEF0 r).
              rewrite <- PositiveSet.mem_spec in DEF0.
              rewrite Emem in DEF0. destruct (rms ! r) eqn:Er; auto.
              assert (exists v0, Some v = Some v0).
              { exists v. auto. }
              apply DEF0 in H. discriminate. }
            rewrite H. symmetry. eapply update_not_captured; eauto.
            intros IN'. apply PositiveSet.inter_spec in IN' as [IN' _].
            rewrite <- PositiveSet.mem_spec in IN'.
            rewrite IN' in Emem. discriminate. }
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
          + eapply refl_match; eauto.
        - exists Zero. exists (State s v' next (rms#reg<-v) ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Op; eauto.
          + apply refl_match; auto.
        - exists Zero. exists (State s v' next newrm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Move; eauto.
          + apply refl_match; auto.
        - exists Zero. exists (State s v' (pc_cond v iftrue iffalse) rms ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Cond; eauto.
          + apply refl_match; auto.
        - poseq_destr fid0 fid.
          + destruct (in_or_not (ver_entry vbase) l_fs) as [IN|NOTIN].
            * exists One. exists (State (Stackframe retreg v' next rms ::s) (current_version f) (ver_entry (current_version f)) newrm ms). split.
              ** left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
                 simpl in FINDF. eapply same_params in FINDOPTF; eauto.
                 rewrite FINDOPTF. auto.
              ** simpl in FINDF. erewrite find_function_same in FINDF; eauto. inv FINDF.
                 unfold current_version. rewrite NO_OPT. simpl.
                 apply fs_match; auto.
                 2: { eapply def_analyze_init; eauto. }
                 constructor; auto. eapply frame_same; eauto.
            * exists Zero. exists (State (Stackframe retreg v' next rms ::s) (current_version f) (ver_entry (current_version f)) newrm ms). split.
              ** left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
                 simpl in FINDF. eapply same_params in FINDOPTF; eauto.
                 rewrite FINDOPTF. auto.
              ** simpl in FINDF. erewrite find_function_same in FINDF; eauto. inv FINDF.
                 unfold current_version. rewrite NO_OPT. simpl.
                 apply opt_match; auto.
                 2: { eapply def_analyze_init; eauto. }
                 constructor; auto. constructor. 
          + simpl in FINDF. rewrite <- find_function_unchanged in FINDF; auto.
            exists Zero. exists (State (Stackframe retreg v' next rms :: s) (current_version func) (ver_entry (current_version func)) newrm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
            * apply refl_match; auto. constructor; auto. constructor.
        - inv MATCHSTACK. inv MSF.
          + exists Zero. exists (State s1 fprev next (rmprev#retreg<-retval) ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
            * apply refl_match; auto.
          + exists Zero. exists (State s1 vbase next (rms0#retreg<-retval) ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
            * apply deopt_match; auto.
          + destruct (in_or_not next l_fs).
            * exists One. exists (State s1 vbase next (rmprev#retreg<-retval) ms). split.
              ** left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
              ** apply fs_match; auto.
            * exists Zero. exists (State s1 vbase next (rmprev#retreg<-retval) ms). split.
              ** left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
              ** apply opt_match; auto.
        - inv MATCHSTACK. exists One. exists (Final retval ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Return_Final; eauto.
          + apply final_match; auto.
        - exists Zero. exists (State s v' next rms ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Printexpr; eauto.
          + apply refl_match; auto.
        - exists Zero. exists (State s v' next rms ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Printstring; eauto.
          + apply refl_match; auto.
        - exists Zero. exists (State s v' next rms newms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Store; eauto.
          + apply refl_match; auto.
        - exists Zero. exists (State s v' next (rms#reg<-val) ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Load; eauto.
          + apply refl_match; auto.
        - exists Zero. exists (State s v' next rms ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
          + apply refl_match; auto.
        - exists Zero. exists (State (synth++s) newver la newrm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
            erewrite base_version_unchanged; eauto.
            * apply FINDF.
            * apply synth_frame_unchanged in SYNTH. apply SYNTH.
          + apply refl_match; auto. apply match_app; auto. }
      * inv DEOPT_COND. simpl in FINDF. rewrite <- base_version_unchanged in FINDF.
        apply synth_frame_unchanged in SYNTH.
        exists Zero. exists (State s v' next rms ms). split.
        left. apply plus_one. eapply nd_exec_Framestate_go_on.
        econstructor; eauto. apply refl_match; auto.
      * inv DEOPT_COND. simpl in FINDF. rewrite <- base_version_unchanged in FINDF.
        apply synth_frame_unchanged in SYNTH.
        exists Zero. exists (State (synth ++ s) newver la newrm ms). split.
        left. apply plus_one. eapply nd_exec_Framestate_deopt.
        econstructor; eauto. apply refl_match; auto. apply match_app; auto.

    + inv STEP.                (* deopt_match *)
      { inv STEP0; unfold live_dr_transf in AGREE; rewrite CODE in AGREE.
        - exists Zero. exists (State s vbase next rms ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Nop; eauto.
          + apply deopt_match; auto.            
            eapply agree_transfer; eauto. simpl. left. auto.
        - exists Zero. exists (State s vbase next (rms#reg<-v) ms). split.
          + left. apply plus_one. apply nd_exec_lowered.
            eapply exec_Op; eauto. rmagreeb.
          + apply deopt_match; auto. eapply agree_transfer; eauto.
            2: { apply agree_insert_dead. eapply expr_live_agree. eauto. }
            simpl. left. auto.
        - eapply agree_update_movelist in UPDATE as UPDATE'; eauto.
          destruct UPDATE' as [rm1u [UPDATE' NEXT]]; eauto.
          exists Zero. exists (State s vbase next rm1u ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Move; eauto.
          + apply deopt_match; auto. eapply agree_transfer; eauto.
            2: { apply agree_movelist_dead with (ml := ml) (rms := rms) (rmo := rmo); auto. }
            simpl. left. auto.         
        - exists Zero. exists (State s vbase (pc_cond v iftrue iffalse) rms ms). split.
          + left. apply plus_one. apply nd_exec_lowered.
            eapply exec_Cond; eauto. rmagreeb.
          + apply deopt_match; auto. eapply agree_transfer; eauto.
            2: { eapply expr_live_agree. eauto. }
            simpl. destruct v; destruct z; simpl;
                     try (left; reflexivity); try (right; reflexivity);
                       try (right; left; reflexivity).
        - poseq_destr fid0 fid.
          + destruct (in_or_not (ver_entry vbase) l_fs) as [IN|NOTIN].
            * exists One. exists (State (Stackframe retreg vbase next rms ::s) (current_version f) (ver_entry (current_version f)) newrm ms). split.
              ** left. apply plus_one. apply nd_exec_lowered.
                 eapply exec_Call; eauto. rmagreeb.
                 simpl in FINDF. eapply same_params in FINDOPTF; eauto.
                 rewrite FINDOPTF. auto.
              ** simpl in FINDF. erewrite find_function_same in FINDF; eauto. inv FINDF.
                 unfold current_version. rewrite NO_OPT. simpl.
                 apply fs_match; auto.
                 2: { eapply def_analyze_init; eauto. }
                 constructor; auto. eapply frame_deopt; eauto.
                 intros. eapply agree_transfer; eauto. 
                 2: { apply agree_insert_dead.
                      eapply expr_list_live_agree. eauto. }
                 simpl. left. auto.
            * exists Zero. exists (State (Stackframe retreg vbase next rms ::s) (current_version f) (ver_entry (current_version f)) newrm ms). split.
              ** left. apply plus_one. apply nd_exec_lowered.
                 eapply exec_Call; eauto. rmagreeb.
                 simpl in FINDF. eapply same_params in FINDOPTF; eauto.
                 rewrite FINDOPTF. auto.
              ** simpl in FINDF. erewrite find_function_same in FINDF; eauto. inv FINDF.
                 unfold current_version. rewrite NO_OPT. simpl.
                 apply opt_match; auto.
                 2: { eapply def_analyze_init; eauto. }
                 constructor; auto. constructor.
                 intros. eapply agree_transfer; eauto. 
                 2: { apply agree_insert_dead.
                      eapply expr_list_live_agree. eauto. }
                 simpl. left. auto.
          + simpl in FINDF. rewrite <- find_function_unchanged in FINDF; auto. exists Zero.
            exists (State (Stackframe retreg vbase next rms :: s) (current_version func) (ver_entry (current_version func)) newrm ms). split.
            * left. apply plus_one. apply nd_exec_lowered.
              eapply exec_Call; eauto. rmagreeb.
            * apply refl_match; auto. constructor; auto. constructor.
              intros. eapply agree_transfer; eauto. 
              2: { apply agree_insert_dead.
                   eapply expr_list_live_agree. eauto. }
              simpl. left. auto.
        - inv MATCHSTACK. inv MSF.
          + exists Zero. exists (State s1 fprev next (rmprev#retreg<-retval) ms). split.
            * left. apply plus_one. apply nd_exec_lowered.
              eapply exec_Return; eauto. rmagreeb.
            * apply refl_match; auto.
          + exists Zero. exists (State s1 vbase next (rms0#retreg<-retval) ms). split.
            * left. apply plus_one. apply nd_exec_lowered.
              eapply exec_Return; eauto. rmagreeb.
            * apply deopt_match; auto. 
          + destruct (in_or_not next l_fs).
            * exists One. exists (State s1 vbase next (rmprev#retreg<-retval) ms). split.
              ** left. apply plus_one. apply nd_exec_lowered.
                 eapply exec_Return; eauto. rmagreeb.
              ** apply fs_match; auto. 
            * exists Zero. exists (State s1 vbase next (rmprev#retreg<-retval) ms). split.
              ** left. apply plus_one. apply nd_exec_lowered.
                 eapply exec_Return; eauto. rmagreeb.
              ** apply opt_match; auto. 
        - inv MATCHSTACK. exists One. exists (Final retval ms). split.
          + left. apply plus_one. apply nd_exec_lowered.
            eapply exec_Return_Final; eauto. rmagreeb.
          + apply final_match; auto.
        - exists Zero. exists (State s vbase next rms ms). split.
          + left. apply plus_one. apply nd_exec_lowered.
            eapply exec_Printexpr; eauto. rmagreeb.
          + apply deopt_match; auto. eapply agree_transfer; eauto.
            2: { eapply expr_live_agree. eauto. }
            simpl. left. auto.
        - exists Zero. exists (State s vbase next rms ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Printstring; eauto.
          + apply deopt_match; auto.
            eapply agree_transfer; eauto. simpl. left. auto.
        - exists Zero. exists (State s vbase next rms newms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Store; eauto.
            * clear EVAL_AD. rmagreeb.
            * clear EVAL_ST. rmagreeb.
              eapply expr_live_agree. eauto.
          + apply deopt_match; auto. eapply agree_transfer; eauto.
            simpl. left. auto.
            repeat (eapply expr_live_agree; eauto).
        - exists Zero. exists (State s vbase next (rms#reg<-val) ms). split.
          + left. apply plus_one. apply nd_exec_lowered.
            eapply exec_Load; eauto. rmagreeb.
          + apply deopt_match; auto. eapply agree_transfer; eauto. 
            2: { apply agree_insert_dead.
                 eapply expr_live_agree. eauto. }
            simpl. left. auto.
        - exists Zero. exists (State s vbase next rms ms). split.
          + left. apply plus_one. apply nd_exec_lowered. destruct tgt.
            eapply exec_Assume_holds; eauto. rmagreeb.
          + apply deopt_match; auto. eapply agree_transfer; eauto.
            2: { destruct tgt.
                 eapply synth_live_agree. eapply varmap_live_agree.
                 eapply expr_list_live_agree. eauto. }
            simpl. left. auto.
        - eapply agree_update_regmap in UPDATE; eauto.
          2: { eapply expr_list_live_agree. eauto. }
          eapply agree_synthesize_frame in SYNTH; eauto.
          2: { eapply varmap_live_agree. eapply expr_list_live_agree. eauto. }
          exists Zero. exists (State (synth++s) newver la newrm ms). split.
          + left. apply plus_one. apply nd_exec_lowered.
            eapply exec_Assume_fails; eauto; try rmagreeb.
            * erewrite base_version_unchanged; eauto. apply FINDF.
            * apply synth_frame_unchanged in SYNTH. eauto.
          + apply refl_match; auto. apply match_app; auto. }
      * inv DEOPT_COND. simpl in FINDF.
        rewrite <- base_version_unchanged in FINDF.
        unfold live_dr_transf in AGREE. rewrite CODE in AGREE.
        apply synth_frame_unchanged in SYNTH.
        eapply agree_update_regmap in UPDATE; eauto.
        eapply agree_synthesize_frame in SYNTH; eauto.
        2: { eapply varmap_live_agree. eauto. }
        exists Zero. exists (State s vbase next rms ms). split.
        ** left. apply plus_one. eapply nd_exec_Framestate_go_on.
           econstructor; eauto.
        ** apply deopt_match; auto.
           eapply agree_transfer; eauto. 
           2: { eapply synth_live_agree. eapply varmap_live_agree. eauto. }
           simpl. left. auto.
      * inv DEOPT_COND. simpl in FINDF.
        rewrite <- base_version_unchanged in FINDF.
        unfold live_dr_transf in AGREE. rewrite CODE in AGREE.
        apply synth_frame_unchanged in SYNTH.
        eapply agree_update_regmap in UPDATE; eauto.
        eapply agree_synthesize_frame in SYNTH; eauto.
        2: { eapply varmap_live_agree. eauto. }
        exists Zero. exists (State (synth ++ s) newver la newrm ms). split.
        ** left. apply plus_one. eapply nd_exec_Framestate_deopt.
           econstructor; eauto.
        ** apply refl_match; auto. apply match_app; auto. 

    + inv STEP. inv STEP0.      (* final_match *)
Qed.
