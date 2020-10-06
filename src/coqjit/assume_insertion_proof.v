(* Correctness of the Assume Insertion pass *)
(* A pass of the dynamic optimizer *)
(* Inserts an Assume insertion just after a Framestate *)

Require Export internal_simulations.
Require Export ir_properties.
Require Export assume_insertion.
Require Import Coq.MSets.MSetPositive.
Require Export def_regs.

(** * Matching the stack and properties  *)
(* Matching stackframes: a version may have been replaced with its optimized version *)
Inductive match_stackframe (v:version) (fid:fun_id) (guard:list expr) (fsl:label) (params:list reg): stackframe -> stackframe -> Prop :=
| frame_same:
    forall sf, (match_stackframe v fid guard fsl params) sf sf
| frame_opt:
    forall r lbl rm vins abs
      (AS_INSERT: insert_assume_version v fid guard fsl params = OK vins)
      (DEFREGS: defined_regs_analysis (ver_code v) params (ver_entry v) = Some abs)
      (DEF: forall retval, defined (rm#r<-retval) (absstate_get lbl abs)),
      (match_stackframe v fid guard fsl params) (Stackframe r v lbl rm) (Stackframe r vins lbl rm).

(* Generalizing match_stackframe to the entire stack *)
Inductive match_stack (v:version) (fid:fun_id) (guard:list expr) (fsl:label) (params:list reg): stack -> stack -> Prop :=
| match_nil:
    (match_stack v fid guard fsl params) nil nil
| match_cons:
    forall s s' sf sf'
      (MS: (match_stack v fid guard fsl params) s s')
      (MSF: (match_stackframe v fid guard fsl params) sf sf'),
      (match_stack v fid guard fsl params) (sf::s) (sf'::s').

Lemma match_stack_same:
  forall s v fid guard fsl params,
    (match_stack v fid guard fsl params) s s.
Proof.
  intros s v fid guard fsl. induction s; constructor. auto. constructor.
Qed.

Lemma match_app:
  forall synth s s' v fid guard fsl params,
    (match_stack v fid guard fsl params) s s' ->
    (match_stack v fid guard fsl params) (synth++s) (synth++s').
Proof.
  intros. induction synth.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. apply match_cons. auto. constructor.
Qed.

Lemma app_match:
  forall synth synthopt s s' v fid guard fsl params,
    (match_stack v fid guard fsl params) s s' ->
    (match_stack v fid guard fsl params) synth synthopt ->
    (match_stack v fid guard fsl params) (synth++s) (synthopt++s').
Proof.
  intros. induction H0.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. apply match_cons; auto.
Qed.

(** * Index and order used in the simulation *)
(* There is one stuttering step for each inserted Framestate *)
Inductive as_index: Type :=
| One : as_index
| Zero: as_index.

Inductive as_order: as_index -> as_index -> Type :=
| order: as_order Zero One.

Lemma wfounded: well_founded as_order.
Proof.
  unfold well_founded. intros a. constructor. intros y H. inv H. constructor. intros y H. inv H.
Qed.

Lemma trans: Relation_Definitions.transitive _ as_order.
Proof.
  unfold Relation_Definitions.transitive. intros x y z H H0. inv H. inv H0.
Qed.


(** * The match_states relation  *)
(* This proof is a backward internal simulation.
   At the Framestate instruction, we take a stuttering step if the Assume succeeds
   If it fails, we take a single step to the target version.

<<
                 
       st1 --------------- st2
        |                   |
       t|(1 or 2 steps)     |t
        |                   |
        v                   v
       st1'--------------- st2'
                 
>>
*)

Inductive match_states (p:program) (v:version) (fid:fun_id) (guard: list expr) (fsl:label) (params:list reg): as_index -> specIR.state -> specIR.state -> Prop :=
                                        
| assume_match:                     (* matching at the assume instruction *)
    forall vins s s' rm ms fresh fa la vm sl next synth newver newrm abs
      (MATCHSTACK: (match_stack v fid guard fsl params) s s')
      (OPT: insert_assume_version v fid guard fsl params = OK vins)
      (DEFREGS: defined_regs_analysis (ver_code v) params (ver_entry v) = Some abs)
      (DEF: defined rm (absstate_get fsl abs))
      (VALIDATE: validator v fsl guard params = OK tt)
      (FS_OPT: (ver_code vins) # fsl = Some (Framestate (fa,la) vm sl fresh))
      (AS_OPT: (ver_code vins) # fresh = Some (Assume guard (fa,la) vm sl next))
      (FS_SRC: (ver_code v) # fsl = Some (Framestate (fa,la) vm sl next))
      (SYNTH: synthesize_frame p rm sl synth)
      (FINDF: find_base_version fa p = Some newver)
      (UPDATE: update_regmap vm rm newrm),
      (match_states p v fid guard fsl params) Zero (State s v fsl rm ms) (State s' vins fresh rm ms)
      
| opt_match:           (* matching inside the optimized version *)
    forall vins s s' lbl rm ms abs
      (MATCHSTACK: (match_stack v fid guard fsl params) s s')
      (OPT: insert_assume_version v fid guard fsl params = OK vins)
      (DEFREGS: defined_regs_analysis (ver_code v) params (ver_entry v) = Some abs)
      (DEF: defined rm (absstate_get lbl abs)),
      (match_states p v fid guard fsl params) One (State s v lbl rm ms) (State s' vins lbl rm ms)
                                        
| refl_match:                   (* matching outside of the optimized version *)
    forall v' s s' pc rm ms
      (MATCHSTACK: (match_stack v fid guard fsl params) s s'),
      (match_states p v fid guard fsl params) Zero (State s v' pc rm ms) (State s' v' pc rm ms)
                                        
| final_match:                  (* matching final states *)
    forall retval ms,
      (match_states p v fid guard fsl params) One (Final retval ms) (Final retval ms).

(** * Code preservation properties  *)
Lemma code_preservation':
  forall vsrc vins fid guard fsl lbl params,
    insert_assume_version vsrc fid guard fsl params = OK vins ->
    lbl <> fsl ->
    forall iopt isrc,
      (ver_code vins) # lbl = Some iopt ->
      (ver_code vsrc) # lbl = Some isrc ->
      iopt = isrc.
Proof.
  intros vsrc vins fid guard fsl lbl params OPT NOTFS iopt isrc CODEOPT CODESRC.
  unfold insert_assume_version in OPT. repeat do_ok.
  destruct (c!fsl) eqn:CODEFS; inv H1. destruct i; inv H0. repeat do_ok. destruct u.
  simpl in CODEOPT. inv HDO.
  poseq_destr (fresh_label (Pos.succ fsl) (ver_code vsrc)) lbl.
  - erewrite fresh_label_correct in CODESRC; auto. inv CODESRC.
  - rewrite PTree.gso in CODEOPT; auto. rewrite PTree.gso in CODEOPT; auto.
    rewrite CODESRC in CODEOPT. inv CODEOPT. auto.
Qed.
        
Lemma code_preservation:        (* use at opt_match *)
  forall p p' s s' rm ms t news vsrc vins fid guard fsl lbl params,
    insert_assume_version vsrc fid guard fsl params = OK vins ->
    lbl <> fsl ->
    safe (specir_sem p) (State s vsrc lbl rm ms) ->
    Step (specir_sem p') (State s' vins lbl rm ms) t news ->
    (ver_code vsrc) # lbl = (ver_code vins) # lbl.
Proof.
  intros p p' s s' rm ms t news vsrc vins fid guard fsl lbl params H H0 H1 H2.
  apply safe_code in H1 as [isrc CODESRC]. apply step_code in H2 as [iopt CODEOPT].
  rewrite CODESRC. rewrite CODEOPT. f_equal. symmetry. eapply code_preservation'; eauto.
Qed.

(* The framestate instruction has been changed to point to the Assume *)
Lemma framestate_changed:
  forall vsrc fid guard vins fsl params,
    insert_assume_version vsrc fid guard fsl params = OK vins ->
    exists tgt vm sl fresh next,
      (ver_code vins) # fsl = Some (Framestate tgt vm sl fresh) /\
      (ver_code vsrc) # fsl = Some (Framestate tgt vm sl next) /\
      (ver_code vins) # fresh = Some (Assume guard tgt vm sl next).
Proof.
  intros vsrc fid guard vins fsl params OPT. unfold insert_assume_version in OPT. repeat do_ok.
  inv HDO. destruct ((ver_code vsrc)!fsl) eqn:FS_SRC; inv H1.
  destruct i; inv H0. repeat do_ok. exists d. exists v. exists l.
  exists (fresh_label (Pos.succ fsl) (ver_code vsrc)). exists l0. simpl.
  split; auto; try split; auto. 
  - poseq_destr (fresh_label (Pos.succ fsl) (ver_code vsrc)) fsl.
    + erewrite fresh_label_correct in FS_SRC; eauto. inv FS_SRC.
    + rewrite PTree.gso; auto. rewrite PTree.gss. auto.
  - rewrite PTree.gss. auto.
Qed.


Lemma preservation_code:
  forall vsrc vins fid guard fsl lbl params i,
    insert_assume_version vsrc fid guard fsl params = OK vins ->
    lbl <> fsl ->
    (ver_code vsrc) # lbl = Some i ->
    (ver_code vins) # lbl = Some i.
Proof.
  intros vsrc vins fid guard fsl lbl params i H H0 H1. unfold insert_assume_version in H. repeat do_ok.
  destruct (c!fsl) eqn:CODEFS. 2: inv H2. destruct i0; inv H2. repeat do_ok. simpl. inv HDO.
  rewrite PTree.gso. rewrite PTree.gso; auto. poseq_destr lbl (fresh_label (Pos.succ fsl) (ver_code vsrc)); auto.
  erewrite fresh_label_correct in H1; auto. inv H1.
Qed.
  

(** * Progress Preservation  *)
Lemma evaluate_op:
  forall rm rs op,
    defined rm (FlatRegset.Inj rs) ->
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
    defined rm (FlatRegset.Inj rs) ->
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

(* Evaluating a guard if it uses defined registers should be defined *)
Lemma evaluate_succeeds:
  forall rm guard rs,
    defined rm (FlatRegset.Inj rs) ->
    check_guard guard rs = true ->
    exists v, eval_list_expr guard rm v.
Proof.
  intros rm guard rs H H0. induction guard; intros.
  - exists true. constructor.
  - simpl in H0. apply andb_prop in H0. destruct H0. eapply evaluate_expr in H0; eauto.
    destruct H0. destruct x. apply IHguard in H1. destruct H1. destruct z.
    + esplit. eapply eval_cons_false; eauto.
    + esplit. eapply eval_cons_true; eauto. unfold Zne. unfold not. intro. inv H1; inv H2.
    + esplit. eapply eval_cons_true; eauto. unfold Zne. unfold not. intro. inv H1; inv H2.
Qed.

Ltac def_ok :=
  match goal with
  | [CODE: (ver_code ?vsrc) ! ?lbl = Some ?i |- _] =>
    eapply analyze_correct; eauto; simpl; auto; unfold dr_transf; try rewrite CODE; auto
  end.

Lemma progress_preserved:
  forall f vsrc vins fid guard fsl params s1 s2 p i,
    insert_assume_version vsrc fid guard fsl params = OK vins ->
    find_function fid p = Some f ->
    vsrc = current_version f ->
    match_states p vsrc fid guard fsl params i s1 s2 ->
    safe (specir_sem p) s1 ->
    (exists r : value, final_state (set_version p fid vins) s2 r) \/
    (exists (t : trace) (s2' : Smallstep.state (specir_sem (set_version p fid vins))),
        Step (specir_sem (set_version p fid vins)) s2 t s2').
Proof.
  intros f vsrc vins fid guard fsl params s1 s2 p i OPTV FINDOPT CURVER MATCH SAFE.
  inv MATCH.
  - unfold validator in VALIDATE. rewrite FS_SRC in VALIDATE. repeat do_ok.
    destruct (absstate_get fsl a) eqn:ABSDR; inv H0.
    destruct (check_guard guard r) eqn:CHECK; inv H1.
    inv DEFREGS. rewrite ABSDR in DEF. eapply evaluate_succeeds in CHECK as [v EVAL]; eauto.
    right. exists E0. rewrite OPT in OPTV. inv OPTV. destruct v.
    + exists (State s' vins next rm ms). apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
    + exists (State (synth++s') newver la newrm ms). eapply nd_exec_lowered. eapply exec_Assume_fails; eauto.
      simpl. rewrite <- base_version_unchanged. auto. simpl. apply synth_frame_unchanged. auto.
      
  - poseq_destr lbl fsl.
    + rewrite OPT in OPTV. inv OPTV. unfold insert_assume_version in OPT. repeat do_ok.
      destruct (c!fsl) eqn:CODEFS; inv H1. destruct i; inv H0.
      right. exists E0. exists (State s' vins (fresh_label (Pos.succ fsl) c) rm ms). 
      repeat do_ok. simpl. destruct d. apply safe_step in SAFE as STEP. destruct STEP as [s'' [t STEP]].
      inv STEP; inv HDO. inv STEP0; rewrite CODEFS in CODE; inv CODE.
      * inv DEOPT_COND. rewrite CODEFS in CODE. inv CODE.
        eapply nd_exec_Framestate_go_on. econstructor; eauto.
        simpl. rewrite PTree.gso; auto. rewrite PTree.gss. eauto.
        poseq_destr fsl (fresh_label (Pos.succ fsl) (ver_code (current_version f))); auto. erewrite fresh_label_correct in CODEFS; eauto. inv CODEFS.
        rewrite <- base_version_unchanged.  eauto. apply synth_frame_unchanged. eauto.
      * inv DEOPT_COND. rewrite CODEFS in CODE. inv CODE.
        eapply nd_exec_Framestate_go_on. econstructor; eauto.
        simpl. rewrite PTree.gso; auto. rewrite PTree.gss. eauto.
        poseq_destr fsl (fresh_label (Pos.succ fsl) (ver_code (current_version f))); auto. erewrite fresh_label_correct in CODEFS; eauto. inv CODEFS.
        rewrite <- base_version_unchanged.  eauto. apply synth_frame_unchanged. eauto.
      
    + apply safe_step in SAFE as STEP. destruct STEP as [s'' [t STEP]].
      right. rewrite OPT in OPTV. inv OPTV.
      apply safe_code in SAFE. destruct SAFE as [i CODESRC].
      eapply preservation_code in HEQ as SAME_CODE; eauto.
      inv STEP.
      * exists t. { inv STEP0; rewrite CODE in CODESRC; inv CODESRC. 
        + exists (State s' vins next rm ms). apply nd_exec_lowered. eapply exec_Nop. eauto.
        + exists (State s' vins next (rm#reg<-v) ms). apply nd_exec_lowered. eapply exec_Op; eauto.
        + exists (State s' vins next newrm ms). apply nd_exec_lowered. eapply exec_Move; eauto.
        + exists (State s' vins (pc_cond v iftrue iffalse) rm ms). apply nd_exec_lowered. eapply exec_Cond; eauto.
        + poseq_destr fid0 fid.
          * eapply find_function_same with (v:=vins) in FINDF.
            exists (State (Stackframe retreg vins next rm ::s') (current_version (set_version_function vins func)) (ver_entry (current_version (set_version_function vins func))) newrm ms).
            apply nd_exec_lowered. eapply exec_Call; eauto.
          * simpl in FINDF. eapply find_function_unchanged with (fid':=fid) (v:=vins) in HEQ0.
            rewrite HEQ0 in FINDF.
            exists (State (Stackframe retreg vins next rm ::s') (current_version (func)) (ver_entry (current_version (func))) newrm ms).
            apply nd_exec_lowered. eapply exec_Call; eauto.
        + inv MATCHSTACK. inv MSF.
          * exists (State s'0 fprev next (rmprev#retreg<-retval) ms).
            apply nd_exec_lowered. eapply exec_Return; eauto.
          * exists (State s'0 vins0 next (rmprev#retreg<-retval) ms). apply nd_exec_lowered.
            eapply exec_Return; eauto.
        + inv MATCHSTACK. exists (Final retval ms). apply nd_exec_lowered. eapply exec_Return_Final; eauto.
        + exists (State s' vins next rm ms). apply nd_exec_lowered. eapply exec_Printexpr; eauto.
        + exists (State s' vins next rm ms). apply nd_exec_lowered. eapply exec_Printstring. auto.
        + exists (State s' vins next rm newms). apply nd_exec_lowered. eapply exec_Store; eauto.
        + exists (State s' vins next (rm#reg<-val) ms). apply nd_exec_lowered. eapply exec_Load; eauto.
        + exists (State s' vins next rm ms). apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
        + rewrite synth_frame_unchanged in SYNTH. erewrite base_version_unchanged in FINDF.
          exists (State (synth ++ s') newver la newrm ms). apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
          simpl in FINDF. simpl. eauto. simpl in SYNTH. simpl. eauto. }
      * exists E0. exists (State s' vins next rm ms). inv DEOPT_COND. rewrite synth_frame_unchanged in SYNTH.
        rewrite CODE in CODESRC. inv CODESRC.  eapply nd_exec_Framestate_go_on. 
        econstructor; eauto. simpl. rewrite <- base_version_unchanged. eauto. simpl in SYNTH. simpl. eauto.
      * exists E0. exists (State s' vins next rm ms). inv DEOPT_COND. rewrite synth_frame_unchanged in SYNTH.
        rewrite CODE in CODESRC. inv CODESRC. eapply nd_exec_Framestate_go_on. 
        econstructor; eauto. simpl. rewrite <- base_version_unchanged. eauto. simpl in SYNTH. simpl. eauto.
                
  - apply safe_step in SAFE. destruct SAFE as [s'' [t STEP]].
    right. inv STEP.
    * exists t. { inv STEP0.
      + exists (State s' v' next rm ms). apply nd_exec_lowered. eapply exec_Nop. eauto.
      + exists (State s' v' next (rm#reg<-v) ms). apply nd_exec_lowered. eapply exec_Op; eauto.
      + exists (State s' v' next newrm ms). apply nd_exec_lowered. eapply exec_Move; eauto.
      + exists (State s' v' (pc_cond v iftrue iffalse) rm ms). apply nd_exec_lowered. eapply exec_Cond; eauto.
      + poseq_destr fid0 fid.
        * eapply find_function_same with (v:=vins) in FINDF.
          exists (State (Stackframe retreg v' next rm ::s') (current_version (set_version_function vins func)) (ver_entry (current_version (set_version_function vins func))) newrm ms).
          apply nd_exec_lowered. eapply exec_Call; eauto.
        * simpl in FINDF. eapply find_function_unchanged with (fid':=fid) (v:=vins) in HEQ.
          rewrite HEQ in FINDF.
          exists (State (Stackframe retreg v' next rm ::s') (current_version (func)) (ver_entry (current_version (func))) newrm ms).
          apply nd_exec_lowered. eapply exec_Call; eauto.
      + inv MATCHSTACK. inv MSF.
        * exists (State s'0 fprev next (rmprev#retreg<-retval) ms).
          apply nd_exec_lowered. eapply exec_Return; eauto.
        * exists (State s'0 vins0 next (rmprev#retreg<-retval) ms). apply nd_exec_lowered.
          eapply exec_Return; eauto.
      + inv MATCHSTACK. exists (Final retval ms). apply nd_exec_lowered. eapply exec_Return_Final; eauto.
      + exists (State s' v' next rm ms). apply nd_exec_lowered. eapply exec_Printexpr; eauto.
      + exists (State s' v' next rm ms). apply nd_exec_lowered. eapply exec_Printstring. auto.
      + exists (State s' v' next rm newms). apply nd_exec_lowered. eapply exec_Store; eauto.
      + exists (State s' v' next (rm#reg<-val) ms). apply nd_exec_lowered. eapply exec_Load; eauto.
      + exists (State s' v' next rm ms). apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
      + rewrite synth_frame_unchanged in SYNTH. erewrite base_version_unchanged in FINDF.
        exists (State (synth ++ s') newver la newrm ms). apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
        simpl in FINDF. simpl. eauto. simpl in SYNTH. simpl. eauto. }
    * exists E0. exists (State s' v' next rm ms). inv DEOPT_COND. rewrite synth_frame_unchanged in SYNTH.
      eapply nd_exec_Framestate_go_on. 
      econstructor; eauto. simpl. rewrite <- base_version_unchanged. eauto. simpl in SYNTH. simpl. eauto.
    * exists E0. exists (State s' v' next rm ms). inv DEOPT_COND. rewrite synth_frame_unchanged in SYNTH.
      eapply nd_exec_Framestate_go_on. 
      econstructor; eauto. simpl. rewrite <- base_version_unchanged. eauto. simpl in SYNTH. simpl. eauto. 
  - left. exists retval. constructor.
Qed.

(** * The Internal Backward Simulation  *)
Theorem assume_insertion_correct:
  forall p fid guard fs_lbl newp,
    insert_assume fid guard fs_lbl p = OK newp ->
    backward_internal_simulation p newp.
Proof.
  intros p fid guard fs_lbl newp OPT. unfold insert_assume in OPT. repeat do_ok.
  rename HDO1 into FINDOPTF. rename v into vins. set (vsrc:=current_version f).
  assert (OPTV: insert_assume_version vsrc fid guard fs_lbl (fn_params f) = OK vins) by auto.
  unfold insert_assume_version in HDO0. repeat do_ok. inv HDO. destruct u.
  set (c:=ver_code vsrc).  rename HDO0 into VALIDATE. fold vsrc in VALIDATE.
  fold vsrc in H1. fold c in H1. destruct (c!fs_lbl) eqn:CODE_FS; inv H1.
  destruct i; inv H0. repeat do_ok. rename d into tgt. rename v into vm_fs. rename l into sl_fs.
  rename l0 into next_fs. rename HDO0 into CODE_NEXT.
  set (vins := {| ver_code := (c # fs_lbl <- (Framestate tgt vm_fs sl_fs (fresh_label (Pos.succ fs_lbl) c))) #  (fresh_label (Pos.succ fs_lbl) c) <- (Assume guard tgt vm_fs sl_fs next_fs); ver_entry := ver_entry vsrc |}). fold vins in OPTV.
  apply Backward_internal_simulation with (bsim_order:=as_order) (bsim_match_states:=match_states p vsrc fid guard fs_lbl (fn_params f)).
  - apply wfounded.
  - apply trans.

  - unfold reflexive_forge. intros synchro stack r1 s1 ms FORGE.
    destruct synchro; simpl in FORGE; repeat do_ok; simpl.
    + poseq_destr f0 fid.  (* is the called function the optimized one? *)
      * unfold validator in VALIDATE. fold c in VALIDATE. rewrite CODE_FS in VALIDATE. repeat do_ok.        
        erewrite find_function_same; eauto. simpl. rewrite HDO0. simpl.
        apply interpreter_proof.init_regs_correct in HDO0.
        rewrite FINDOPTF in HDO1. inv HDO1. repeat (esplit; eauto).
        eapply opt_match; auto. apply match_stack_same.
        fold vsrc. fold c. eauto. eapply analyze_init; eauto.
      * erewrite <- find_function_unchanged; eauto. rewrite HDO1. simpl. rewrite HDO0. simpl.
        repeat (esplit; eauto). constructor. apply match_stack_same.
    + destruct stack; try destruct s; inv FORGE.
      * repeat (esplit; eauto). constructor.
      * repeat (esplit; eauto). simpl. constructor. apply match_stack_same.
    + destruct d. repeat do_ok. simpl. rewrite <- base_version_unchanged. rewrite HDO0. simpl.
      repeat (esplit; eauto). simpl. constructor. apply match_stack_same.
    + inv FORGE. destruct r1; repeat (esplit; eauto). 
      * simpl. apply refl_match. apply match_stack_same.
      * simpl. apply final_match.

  - intros. inv H1. inv H. exists (Final r ms). split. apply star_refl. constructor.

  - intros. eapply progress_preserved; eauto. 

  - intros s2 t s2' STEP i0 s1 MATCH SAFE.
    inv MATCH.

    + rewrite OPT in OPTV. inv OPTV. (* assume_match *)
      inv STEP; try solve[inv DEOPT_COND; rewrite CODE in AS_OPT; inv AS_OPT].
      inv STEP0; rewrite CODE in AS_OPT; inv AS_OPT.
      * exists One. exists (State s vsrc next rm ms). (* Assume holds *)
        split. left. apply plus_one. eapply nd_exec_Framestate_go_on. simpl.
        econstructor; eauto. eapply opt_match; eauto.
        eapply analyze_correct; eauto. simpl; auto.  unfold dr_transf. rewrite FS_SRC. auto.
      * exists Zero. exists (State (synth++s) newver la newrm ms). (* Assume fails *)
        split. left. apply plus_one. eapply nd_exec_Framestate_deopt.
        econstructor; eauto.
        simpl in FINDF0. rewrite <- base_version_unchanged in FINDF0. rewrite FINDF0 in FINDF. inv FINDF.
        eapply update_regmap_determ in UPDATE; eauto. subst.
        apply synth_frame_unchanged in SYNTH0. eapply synthesize_frame_determ in SYNTH; eauto. subst.
        constructor; auto. apply app_match; auto. apply match_stack_same. 
        
    + rewrite OPT in OPTV. inv OPTV. (* opt_match *)
      poseq_destr lbl fs_lbl.
      (* We are at the framestate used for insertion*)
      { assert (OPT': insert_assume_version vsrc fid guard fs_lbl (fn_params f)= OK vins) by auto.
        apply framestate_changed in OPT as [[fa la][vm [sl [fresh [next [CODE_INS_FS [CODE_SRC_FS CODE_INS_AS]]]]]]].
        unfold c in CODE_FS. rewrite CODE_FS in CODE_SRC_FS. inv CODE_SRC_FS. inv STEP.
        - inv STEP0; rewrite CODE in CODE_INS_FS; inv CODE_INS_FS.
        - inv DEOPT_COND. rewrite CODE in CODE_INS_FS. inv CODE_INS_FS.
          (* The Framestate goes on in OPT. In SRC, it will depend on how the Assume evaluates *)
          (* So we take a stuttering step in the SRC *)
          exists Zero. exists (State s vsrc fs_lbl rm ms). split.
          right. split. apply star_refl. constructor.
          eapply assume_match; eauto. apply synth_frame_unchanged in SYNTH. eauto.
          simpl in FINDF. rewrite <- base_version_unchanged in FINDF. apply FINDF.
        - inv DEOPT_COND. rewrite CODE in CODE_INS_FS. inv CODE_INS_FS.
          (* The Framestate deopts in both OPT and SRC *)
          exists Zero. exists (State (synth++s) newver la newrm ms). split.
          left. apply plus_one. eapply nd_exec_Framestate_deopt. econstructor; eauto.
          simpl in FINDF. rewrite <- base_version_unchanged in FINDF. apply FINDF.
          apply synth_frame_unchanged in SYNTH. apply SYNTH.
          apply refl_match; auto. apply app_match; auto. apply match_stack_same. }
      
      (* We are not at the Framestate used for insertion *)
      { eapply code_preservation in OPT as SAME_CODE; eauto.
        inv STEP.
        - inv STEP0; rewrite <- SAME_CODE in CODE.
          + exists One. exists (State s vsrc next rm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Nop; eauto.
            * econstructor; eauto. def_ok.
          + exists One. exists (State s vsrc next (rm#reg<-v) ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Op; eauto.
            * econstructor; eauto. def_ok. apply define_insert; auto.
          + exists One. exists (State s vsrc next newrm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Move; eauto.
            * econstructor; eauto. def_ok. eapply define_insert_list; eauto.
          + exists One. exists (State s vsrc (pc_cond v iftrue iffalse) rm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Cond; eauto.
            * econstructor; eauto. def_ok. destruct v; destruct z; auto.
          + poseq_destr fid fid0.
            * simpl in FINDF. erewrite find_function_same in FINDF; eauto. inv FINDF.
              rewrite current_version_same.
              exists One. exists (State (Stackframe retreg vsrc next rm :: s) vsrc (ver_entry vsrc) newrm ms). split.
              left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
              econstructor; eauto. constructor; auto. econstructor; eauto.
              intro. def_ok. apply define_insert; auto.
              unfold vins. simpl. eapply analyze_init; eauto.
            * simpl in FINDF. erewrite <- find_function_unchanged in FINDF; eauto.
              exists Zero. exists (State (Stackframe retreg vsrc next rm :: s) (current_version func) (ver_entry (current_version func)) newrm ms). split.
              left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
              constructor; auto. constructor; auto. econstructor; eauto.
              intro. def_ok. apply define_insert; auto.
          + inv MATCHSTACK. inv MSF.
            * exists Zero. exists (State s1 fprev next (rmprev#retreg<-retval) ms). split.
              left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
              constructor; auto.
            * exists One. exists (State s1 vsrc next (rmprev#retreg<-retval) ms). split.
              left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
              econstructor; eauto. 
          + inv MATCHSTACK. exists One. exists (Final retval ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return_Final; eauto.
            * constructor; auto.
          + exists One. exists (State s vsrc next rm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Printexpr; eauto.
            * econstructor; eauto. def_ok.
          + exists One. exists (State s vsrc next rm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Printstring; eauto.
            * econstructor; eauto. def_ok.
          + exists One. exists (State s vsrc next rm newms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Store; eauto.
            * econstructor; eauto. def_ok.
          + exists One. exists (State s vsrc next (rm#reg<-val) ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Load; eauto.
            * econstructor; eauto. def_ok. apply define_insert; auto.
          + exists One. exists (State s vsrc next rm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
            * econstructor; eauto. def_ok.
          + exists Zero. exists (State (synth++s) newver la newrm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
              simpl in FINDF. rewrite <- base_version_unchanged in FINDF. auto.
              apply synth_frame_unchanged in SYNTH. auto.
            * constructor; auto. apply app_match; auto. apply match_stack_same.
            
        - exists One. exists (State s vsrc next rm ms).
          inv DEOPT_COND. rewrite <- SAME_CODE in CODE. split.
          left. apply plus_one. eapply nd_exec_Framestate_go_on. econstructor; eauto.
          simpl in FINDF. rewrite <- base_version_unchanged in FINDF. apply FINDF.
          apply synth_frame_unchanged in SYNTH. apply SYNTH.
          eapply opt_match; eauto. def_ok. 
        - exists Zero. exists (State (synth++s) newver la newrm ms). split.
          left. inv DEOPT_COND. apply plus_one. eapply nd_exec_Framestate_deopt. econstructor; eauto.
          rewrite SAME_CODE. apply CODE.
          simpl in FINDF. rewrite <- base_version_unchanged in FINDF. apply FINDF.
          apply synth_frame_unchanged in SYNTH. apply SYNTH.
          apply refl_match; auto. apply app_match; auto. apply match_stack_same. }

    + inv STEP.                 (* refl_match *)
      { inv STEP0.
        - exists Zero. exists (State s v' next rm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Nop; eauto.
          + apply refl_match; auto.
        - exists Zero. exists (State s v' next (rm#reg<-v) ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Op; eauto.
          + apply refl_match; auto.
        - exists Zero. exists (State s v' next newrm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Move; eauto.
          + apply refl_match; auto.
        - exists Zero. exists (State s v' (pc_cond v iftrue iffalse) rm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Cond; eauto.
          + apply refl_match; auto.
        - poseq_destr fid fid0.
          + simpl in FINDF. erewrite find_function_same in FINDF; eauto. inv FINDF.
            rewrite current_version_same.
            exists One. exists (State (Stackframe retreg v' next rm :: s) vsrc (ver_entry vsrc) newrm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
            * unfold validator in VALIDATE. fold c in VALIDATE. rewrite CODE_FS in VALIDATE. repeat do_ok.
              econstructor; eauto. constructor; auto. constructor; auto.
              unfold vins. simpl. eapply analyze_init; eauto. 
          + simpl in FINDF. erewrite <- find_function_unchanged in FINDF; eauto.
            exists Zero. exists (State (Stackframe retreg v' next rm :: s) (current_version func) (ver_entry (current_version func)) newrm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
            * constructor; auto. constructor; auto. constructor; auto.
        - inv MATCHSTACK. inv MSF.
          + exists Zero. exists (State s1 fprev next (rmprev#retreg<-retval) ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
            * apply refl_match; auto.
          + exists One. exists (State s1 vsrc next (rmprev#retreg<-retval) ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
            * unfold validator in VALIDATE. fold c in VALIDATE. rewrite CODE_FS in VALIDATE. repeat do_ok.
              eapply opt_match; eauto. 
        - inv MATCHSTACK. exists One. exists (Final retval ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Return_Final; eauto.
          + apply final_match; auto.
        - exists Zero. exists (State s v' next rm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Printexpr; eauto.
          + apply refl_match; auto.
        - exists Zero. exists (State s v' next rm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Printstring; eauto.
          + apply refl_match; auto.
        - exists Zero. exists (State s v' next rm newms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Store; eauto.
          + apply refl_match; auto.
        - exists Zero. exists (State s v' next (rm#reg<-val) ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Load; eauto.
          + apply refl_match; auto.
        - exists Zero. exists (State s v' next rm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
          + apply refl_match; auto.
        - exists Zero. exists (State (synth++s) newver la newrm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
            erewrite base_version_unchanged; eauto. apply FINDF. apply synth_frame_unchanged in SYNTH. auto.
          + apply refl_match; auto. apply match_app; auto. }
      * exists Zero. exists (State s v' next rm ms). split.
        left. apply plus_one. eapply nd_exec_Framestate_go_on. inv DEOPT_COND.
        econstructor; eauto. simpl in FINDF. rewrite <- base_version_unchanged in FINDF. simpl. eauto.
        apply synth_frame_unchanged in SYNTH. eauto.
        apply refl_match. auto.
      * exists Zero. exists (State (synth ++ s) newver la newrm ms). split.
        left. apply plus_one. eapply nd_exec_Framestate_deopt. inv DEOPT_COND.
        econstructor; eauto. simpl in FINDF. rewrite <- base_version_unchanged in FINDF. simpl. auto.
        apply synth_frame_unchanged in SYNTH. eauto.
        apply refl_match. apply match_app; auto.
        
    + inv STEP. inv STEP0.
Qed.
