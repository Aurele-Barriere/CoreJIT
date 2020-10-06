(* Correctness of the Assume Insertion with Delay pass *)
(* A pass of the dynamic optimizer *)
(* Inserts a new Assume after a Condition instruction, which is itself after a Framestate *)

Require Export assume_insertion_proof.
Require Export interpreter_proof.
Require Export specIR.
Require Export ir_properties.
Require Export internal_simulations.
Require Export inlining.
Require Export assume_insertion_delay.
Require Export def_regs.

(** * Matching the stack and properties  *)
(* Matching stackframes: a version may have been replaced with its optimized version *)
Inductive match_stackframe (v:version) (fid:fun_id) (guard:list expr) (fsl:label) (condl:label) (params:list reg): stackframe -> stackframe -> Prop :=
| frame_same:
    forall sf, (match_stackframe v fid guard fsl condl params) sf sf
| frame_opt:
    forall r lbl rm vins abs
      (AS_INSERT: insert_assume_version v fid guard fsl params = OK vins)
      (DEFREGS: defined_regs_analysis (ver_code v) params (ver_entry v) = Some abs)
      (DEF: forall retval, defined (rm#r<-retval) (absstate_get lbl abs))
      (RET_COND: lbl <> condl),
      (match_stackframe v fid guard fsl condl params) (Stackframe r v lbl rm) (Stackframe r vins lbl rm).

(* Generalizing match_stackframe to the entire stack *)
Inductive match_stack (v:version) (fid:fun_id) (guard:list expr) (fsl:label) (condl:label) (params:list reg): stack -> stack -> Prop :=
| match_nil:
    (match_stack v fid guard fsl condl params) nil nil
| match_cons:
    forall s s' sf sf'
      (MS: (match_stack v fid guard fsl condl params) s s')
      (MSF: (match_stackframe v fid guard fsl condl params) sf sf'),
      (match_stack v fid guard fsl condl params) (sf::s) (sf'::s').

Lemma match_stack_same:
  forall s v fid guard fsl condl params,
    (match_stack v fid guard fsl condl params) s s.
Proof.
  intros s v fid guard fsl. induction s; constructor. auto. constructor.
Qed.

Lemma match_app:
  forall synth s s' v fid guard fsl condl params,
    (match_stack v fid guard fsl condl params) s s' ->
    (match_stack v fid guard fsl condl params) (synth++s) (synth++s').
Proof.
  intros. induction synth.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. apply match_cons. auto. constructor.
Qed.

Lemma app_match:
  forall synth synthopt s s' v fid guard fsl condl params,
    (match_stack v fid guard fsl condl params) s s' ->
    (match_stack v fid guard fsl condl params) synth synthopt ->
    (match_stack v fid guard fsl condl params) (synth++s) (synthopt++s').
Proof.
  intros. induction H0.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. apply match_cons; auto.
Qed.

(** * Index and order used in the simulation *)
(* There is one stuttering step for each inserted Framestate *)
Inductive as_index: Type :=
| Two : as_index
| One : as_index
| Zero: as_index.

Inductive as_order: as_index -> as_index -> Prop :=
| order10: as_order Zero One
| order21: as_order One Two
| order20: as_order Zero Two.

Lemma wfounded: well_founded as_order.
Proof.
  unfold well_founded. intros a. constructor. intros y H. inv H.
  - constructor. intros y H. inv H.
  - constructor. intros y H. inv H. constructor. intros y H. inv H.
  - constructor. intros y H. inv H.
Qed.

Lemma trans: Relation_Definitions.transitive _ as_order.
Proof.
  unfold Relation_Definitions.transitive. intros x y z H H0. inv H; inv H0. constructor.
Qed.

(** * The match_states relation  *)
(* This proof is a backward internal simulation.
   At the Framestate and the Condition, we take stuttering steps.
   During these stuttering steps, the invariant contains enough information
   for the source program to catch up the delay if we're not going to deoptimize
   (either because we don't take the true branch, or because the guard succeeds)

<<
                 
       st1 --------------- st2
        |                   |
       t|(1, 2 or 3 steps)  |t
        |                   |
        v                   v
       st1'--------------- st2'
                 
>>
*)


Inductive match_states (p:program) (v:version) (fid:fun_id) (guard: list expr) (fsl:label) (condl:label) (params:list reg): as_index -> specIR.state -> specIR.state -> Prop :=

  | assume_match:                     (* matching at the assume instruction *)
    forall vins s s' rm ms fa la vm sl synth newver newrm iftrue iffalse condexpr vcond abs
      (MATCHSTACK: (match_stack v fid guard fsl condl params) s s')
      (OPT: insert_assume_version v fid guard fsl params = OK vins)
      (COND: eval_expr condexpr rm (Vint vcond)) (* We only do this match if the condition holds *)
      (TRUE: vcond <> 0)

      (DEFREGS: defined_regs_analysis (ver_code v) params (ver_entry v) = Some abs)
      (DEF: defined rm (absstate_get fsl abs))
      (VALIDATE: validator v fsl guard params = OK tt)
      
      (FS_SRC: (ver_code v) # fsl = Some (Framestate (fa,la) vm sl condl))
      (CO_SRC: (ver_code v) # condl = Some (Cond condexpr iftrue iffalse))
      (FS_OPT: (ver_code vins) # fsl = Some (Framestate (fa,la) vm sl condl))
      (CO_OPT: (ver_code vins) # condl = Some (Cond condexpr (fresh_label (Pos.succ condl) (ver_code v)) iffalse))
      (AS_OPT: (ver_code vins) # (fresh_label (Pos.succ condl) (ver_code v)) = Some (Assume guard (fa,la) vm sl iftrue))
      
      (SYNTH: synthesize_frame p rm sl synth)
      (FINDF: find_base_version fa p = Some newver)
      (UPDATE: update_regmap vm rm newrm),
      (match_states p v fid guard fsl condl params) Zero (State s v fsl rm ms) (State s' vins (fresh_label (Pos.succ condl) (ver_code v)) rm ms)
  
| cond_match_delay:
    forall vins s s' rm ms fa la vm sl synth newver newrm iftrue iffalse condexpr abs
      (MATCHSTACK: (match_stack v fid guard fsl condl params) s s')
      (OPT: insert_assume_version v fid guard fsl params = OK vins)

      (DEFREGS: defined_regs_analysis (ver_code v) params (ver_entry v) = Some abs)
      (DEF: defined rm (absstate_get fsl abs))

      (FS_SRC: (ver_code v) # fsl = Some (Framestate (fa,la) vm sl condl))
      (CO_SRC: (ver_code v) # condl = Some (Cond condexpr iftrue iffalse))
      (FS_OPT: (ver_code vins) # fsl = Some (Framestate (fa,la) vm sl condl))
      (CO_OPT: (ver_code vins) # condl = Some (Cond condexpr (fresh_label (Pos.succ condl) (ver_code v)) iffalse))
      (AS_OPT: (ver_code vins) # (fresh_label (Pos.succ condl) (ver_code v)) = Some (Assume guard (fa,la) vm sl iftrue))

      (SYNTH: synthesize_frame p rm sl synth)
      (FINDF: find_base_version fa p = Some newver)
      (UPDATE: update_regmap vm rm newrm),
      (match_states p v fid guard fsl condl params) One (State s v fsl rm ms) (State s' vins condl rm ms)
  
| opt_match:           (* matching inside the optimized version *)
    forall vins s s' lbl rm ms abs
      (MATCHSTACK: (match_stack v fid guard fsl condl params) s s')
      (OPT: insert_assume_version v fid guard fsl params = OK vins)

      (DEFREGS: defined_regs_analysis (ver_code v) params (ver_entry v) = Some abs)
      (DEF: defined rm (absstate_get lbl abs))
      
      (NOCOND: lbl <> condl),    (* the condition is matched with delay *)
      (match_states p v fid guard fsl condl params) Two (State s v lbl rm ms) (State s' vins lbl rm ms)
                                        
| refl_match:                   (* matching outside of the optimized version *)
    forall v' s s' pc rm ms
      (MATCHSTACK: (match_stack v fid guard fsl condl params) s s'),
      (match_states p v fid guard fsl condl params) Zero (State s v' pc rm ms) (State s' v' pc rm ms)
                                        
| final_match:                  (* matching final states *)
    forall retval ms,
      (match_states p v fid guard fsl condl params) Zero (Final retval ms) (Final retval ms).

(** * Code Preservation Properties  *)

Lemma code_preservation':
  forall vsrc vins fid guard fsl lbl tgt vm sl condl params,
    insert_assume_version vsrc fid guard fsl params = OK vins ->
    (ver_code vsrc) ! fsl = Some (Framestate tgt vm sl condl) ->
    lbl <> fsl ->
    lbl <> condl ->
    forall iopt isrc,
      (ver_code vins) # lbl = Some iopt ->
      (ver_code vsrc) # lbl = Some isrc ->
      iopt = isrc.
Proof.
  intros vsrc vins fid guard fsl lbl tgt vm sl condl params OPT CODEFS NOTFS NOTCOND iopt isrc CODEOPT CODESRC.
  unfold insert_assume_version in OPT. repeat do_ok. inv HDO.
  rewrite CODEFS in H1.
  destruct ((ver_code vsrc)!condl) eqn:CODECOND; inv H1. destruct i; inv H0.
  repeat do_ok. destruct u.
  simpl in CODEOPT. rewrite PTree.gso in CODEOPT; auto. rewrite PTree.gso in CODEOPT; auto.
  rewrite CODEOPT in CODESRC. inv CODESRC. auto.
  poseq_destr lbl (fresh_label (Pos.succ condl) (ver_code vsrc)); auto. erewrite fresh_label_correct in CODESRC; auto.
  inv CODESRC.
Qed.
        
Lemma code_preservation:        (* use at opt_match *)
  forall p p' s s' rm ms t news vsrc vins fid guard fsl lbl tgt vm sl condl params,
    insert_assume_version vsrc fid guard fsl params = OK vins ->
    (ver_code vsrc) ! fsl = Some (Framestate tgt vm sl condl) ->
    lbl <> fsl ->
    lbl <> condl ->
    safe (specir_sem p) (State s vsrc lbl rm ms) ->
    Step (specir_sem p') (State s' vins lbl rm ms) t news ->
    (ver_code vsrc) # lbl = (ver_code vins) # lbl.
Proof.
  intros p p' s s' rm ms t news vsrc vins fid guard fsl lbl tgt vm sl condl params H H0 H1 H2 H3 H4.
  apply safe_code in H3 as [isrc CODESRC]. apply step_code in H4 as [iopt CODEOPT].
  rewrite CODESRC. rewrite CODEOPT. f_equal. symmetry. eapply code_preservation'; eauto.
Qed.


(** * Validator Dominance Properties  *)
(* The Skipped Condition is not the entry of the version *)
Lemma no_entry:
  forall vsrc fsl guard params tgt vm_fs sl_fs condl condexpr iftrue iffalse,
    validator vsrc fsl guard params = OK tt ->
    (ver_code vsrc) ! fsl = Some (Framestate tgt vm_fs sl_fs condl) ->
    (ver_code vsrc) ! condl = Some (Cond condexpr iftrue iffalse) ->
    condl <> (ver_entry vsrc).
Proof.
  intros vsrc fsl guard params tgt vm_fs sl_fs condl condexpr iftrue iffalse VALID FS_CODE CO_CODE.
  unfold validator in VALID. rewrite FS_CODE in VALID. rewrite CO_CODE in VALID.
  destruct (only_pred (ver_code vsrc) condl fsl) eqn:ONLYPRED; inv VALID.
  poseq_destr condl (ver_entry vsrc); auto. inv H0.
Qed.

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

Lemma only_pred_correct:
  forall c next pred,
    only_pred c next pred = true ->
    forall lbl i,
      lbl <> pred ->
      c ! lbl = Some i ->
      not_in_list (instr_succ i) next = true.
Proof.
  intros c next pred ONLYPRED lbl i NOTPRED CODE.
  apply PTree.elements_correct in CODE. 
  unfold only_pred in ONLYPRED. rewrite PTree.fold_spec in ONLYPRED.
  eapply in_fold_and in ONLYPRED; eauto. simpl in ONLYPRED.
  poseq_destr lbl pred. contradiction. auto.
Qed.

(* If you're not at the Framestate, you can't get into the Condition *)
Lemma no_cond:
  forall vsrc fsl guard params tgt vm_fs sl_fs condl,
    validator vsrc fsl guard params = OK tt ->
    (ver_code vsrc) ! fsl = Some (Framestate tgt vm_fs sl_fs condl) ->
    forall lbl i,
      lbl <> fsl ->
      (ver_code vsrc) ! lbl = Some i ->
      not_in_list (instr_succ i) condl = true.
Proof.
  intros vsrc fsl guard params tgt vm_fs sl_fs condl VALID CODE_FS lbl i NOTFS CODE.
  unfold validator in VALID. rewrite CODE_FS in VALID.
  destruct ((ver_code vsrc)!condl) eqn:CODE_COND; inv VALID. destruct i0; inv H0.
  destruct (only_pred (ver_code vsrc) condl fsl) eqn:ONLY_PRED; inv H1.
  eapply only_pred_correct; eauto.
Qed.


Lemma preservation_code:
  forall vsrc vins fid guard fsl lbl params i tgt vm sl condl,
    insert_assume_version vsrc fid guard fsl params = OK vins ->
    (ver_code vsrc) # fsl = Some (Framestate tgt vm sl condl) ->
    lbl <> fsl -> lbl <> condl ->
    (ver_code vsrc) # lbl = Some i ->
    (ver_code vins) # lbl = Some i.
Proof.
  intros vsrc vins fid guard fsl lbl params i tgt vm sl condl H H0 H1 H2 H3.
  unfold insert_assume_version in H. repeat do_ok. inv HDO. rewrite H0 in H4.
  destruct ((ver_code vsrc)!condl) eqn:CONDCODE; inv H4. destruct i0; inv H5. repeat do_ok.
  simpl. rewrite PTree.gso; auto. rewrite PTree.gso; auto.
  poseq_destr lbl (fresh_label (Pos.succ condl) (ver_code vsrc)); auto.
  erewrite fresh_label_correct in H3; auto. inv H3.
Qed.


(** * Progress Preservation  *)
Lemma progress_preserved:
  forall f vsrc vins fid guard fsl condl params s1 s2 p i tgt vm sl,
    insert_assume_version vsrc fid guard fsl params = OK vins ->
    find_function fid p = Some f ->
    vsrc = current_version f ->
    match_states p vsrc fid guard fsl condl params i s1 s2 ->
    safe (specir_sem p) s1 ->
    (ver_code vsrc) ! fsl = Some (Framestate tgt vm sl condl) ->
    (exists r : value, final_state (set_version p fid vins) s2 r) \/
    (exists (t : trace) (s2' : Smallstep.state (specir_sem (set_version p fid vins))),
        Step (specir_sem (set_version p fid vins)) s2 t s2').
Proof.
  intros f vsrc vins fid guard fsl condl params s1 s2 p i tgt vm sl OPTV FINDOPT CURVER MATCH SAFE FS_CODE.
  inv MATCH.
  - unfold validator in VALIDATE. rewrite FS_SRC in VALIDATE. rewrite CO_SRC in VALIDATE.
    destruct (only_pred (ver_code (current_version f)) condl fsl) eqn:ONLY; inv VALIDATE.
    poseq_destr condl (ver_entry (current_version f)). inv H0. repeat do_ok.
    destruct (absstate_get condl a) eqn:ABSDR; inv H1.
    destruct (check_guard guard r) eqn:CHECK; inv H0.
    inv DEFREGS. assert (DEF': defined rm (absstate_get condl abs)).
    { def_ok. rewrite FS_SRC. auto. }
    rewrite ABSDR in DEF'. eapply evaluate_succeeds in CHECK as [v EVAL]; eauto.
    right. exists E0. rewrite OPT in OPTV. inv OPTV. destruct v.
    + exists (State s' vins iftrue rm ms). apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
    + exists (State (synth++s') newver la newrm ms). eapply nd_exec_lowered. eapply exec_Assume_fails; eauto.
      simpl. rewrite <- base_version_unchanged. auto. simpl. apply synth_frame_unchanged. auto.

  - rewrite OPT in OPTV. inv OPTV. right. exists E0.
    assert (SAFE': safe (specir_sem p) (State s (current_version f) condl rm ms)).
    { eapply star_safe; eauto. apply plus_star. apply plus_one. eapply nd_exec_Framestate_go_on.
      econstructor; eauto. }
    assert (exists v, eval_expr condexpr rm v).
    { apply safe_step in SAFE'. destruct SAFE' as [s'' [t CONDSTEP]]. inv CONDSTEP.
      inv STEP; rewrite CODE in CO_SRC; inv CO_SRC. eauto.
      inv DEOPT_COND; rewrite CODE in CO_SRC; inv CO_SRC.
      inv DEOPT_COND; rewrite CODE in CO_SRC; inv CO_SRC. }
    destruct H as [v EVAL]. destruct v. destruct z.
    + exists (State s' vins iffalse rm ms). apply nd_exec_lowered. eapply exec_Cond; eauto.
    + exists (State s' vins (fresh_label (Pos.succ condl) (ver_code (current_version f))) rm ms). apply nd_exec_lowered.
      eapply exec_Cond; eauto.
    + exists (State s' vins (fresh_label (Pos.succ condl) (ver_code (current_version f))) rm ms). apply nd_exec_lowered.
      eapply exec_Cond; eauto.
      
  - poseq_destr lbl fsl.
    + rewrite OPT in OPTV. inv OPTV. unfold insert_assume_version in OPT. repeat do_ok.
      destruct (c!fsl) eqn:CODEFS; inv H1. destruct i; inv H0.
      destruct (c!l0) eqn:CODECOND; inv H1. destruct i; inv H0.
      right. exists E0. exists (State s' vins l0 rm ms).
      repeat do_ok. simpl. destruct d. apply safe_step in SAFE as STEP. destruct STEP as [s'' [t STEP]].
      inv HDO. inv STEP.
      * inv STEP0; rewrite CODEFS in CODE; inv CODE.
      * inv DEOPT_COND. rewrite CODEFS in CODE. inv CODE. destruct tgt.
        eapply nd_exec_Framestate_go_on. econstructor; eauto. simpl. rewrite PTree.gso; auto.
        rewrite PTree.gso; auto. eauto. rewrite CODEFS in FS_CODE. inv FS_CODE. auto.
        poseq_destr fsl (fresh_label (Pos.succ next) (ver_code (current_version f))); auto.
        erewrite fresh_label_correct in CODEFS; eauto. inv CODEFS. eauto.
        simpl. rewrite <- base_version_unchanged. eauto. apply synth_frame_unchanged. eauto.
      * inv DEOPT_COND. rewrite CODEFS in CODE. inv CODE. destruct tgt.
        eapply nd_exec_Framestate_go_on. econstructor; eauto. simpl. rewrite PTree.gso; auto.
        rewrite PTree.gso; auto. eauto. rewrite CODEFS in FS_CODE. inv FS_CODE. auto.
        poseq_destr fsl (fresh_label (Pos.succ next) (ver_code (current_version f))); auto.
        erewrite fresh_label_correct in CODEFS; eauto. inv CODEFS. auto.
        simpl. rewrite <- base_version_unchanged. eauto. apply synth_frame_unchanged. eauto.
      
    + apply safe_step in SAFE as STEP. destruct STEP as [s'' [t STEP]].
      right. rewrite OPT in OPTV. inv OPTV.
      apply safe_code in SAFE. destruct SAFE as [i CODESRC].
      eapply preservation_code in NOCOND as SAME_CODE; eauto.
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


(** * Destructing the Condition  *)
Lemma pc_cond_disj:
  forall v ift iff,
    pc_cond v ift iff = ift \/ pc_cond v ift iff = iff.
Proof.
  intros. destruct v. destruct z; simpl.
  right. auto.
  left. auto.
  left. auto.
Qed.

Ltac def_ok :=
  match goal with
  | [CODE: (ver_code ?vsrc) ! ?lbl = Some ?i |- _] =>
    eapply analyze_correct; eauto; simpl; auto; unfold dr_transf; try rewrite CODE; auto
  end.


(** * The Internal Backward Simulation  *)
Theorem assume_delay_correct:
  forall p fid guard fs_lbl newp,
    insert_assume_delay fid guard fs_lbl p = OK newp ->
    backward_internal_simulation p newp.
Proof.
  intros p fid guard fs_lbl newp OPT. unfold insert_assume_delay in OPT. repeat do_ok.
  rename HDO1 into FINDOPTF. rename v into vins. set (vsrc:=current_version f).
  assert (OPTV: insert_assume_version vsrc fid guard fs_lbl (fn_params f)= OK vins) by auto.
  unfold insert_assume_version in HDO0. repeat do_ok. inv HDO. destruct u.
  set (c:=ver_code vsrc).  rename HDO0 into VALIDATE. fold vsrc in VALIDATE.
  fold vsrc in H1. fold c in H1. destruct (c!fs_lbl) eqn:SRC_FS; inv H1.
  destruct i; inv H0. destruct (c!l0) eqn:SRC_COND; inv H1. destruct i; inv H0. repeat do_ok.
  rename d into tgt. rename v into vm_fs. rename l into sl_fs. rename l0 into condl.
  rename e into condexpr. rename l1 into iftrue. rename l2 into iffalse. rename HDO0 into CODE_TRUE.
  set (vins:={|ver_code := (c # condl <- (Cond condexpr (fresh_label (Pos.succ condl) c) iffalse)) # (fresh_label (Pos.succ condl) c) <- (Assume guard tgt vm_fs sl_fs iftrue); ver_entry := ver_entry vsrc |}). fold vins in OPTV.
  apply Backward_internal_simulation with (bsim_order:=as_order) (bsim_match_states:=match_states p vsrc fid guard fs_lbl condl (fn_params f)).
  - apply wfounded.
  - apply trans.

  - unfold reflexive_forge. intros synchro stack r1 s1 ms FORGE.
    destruct synchro; simpl in FORGE; repeat do_ok; simpl.
    + poseq_destr f0 fid.  (* is the called function the optimized one? *)
      * unfold validator in VALIDATE. fold c in VALIDATE. rewrite SRC_FS in VALIDATE.
        rewrite SRC_COND in VALIDATE. destruct (only_pred c condl fs_lbl) eqn:ONLY; inv VALIDATE.
        poseq_destr condl (ver_entry vsrc); inv H0. repeat do_ok.
        erewrite find_function_same; eauto. simpl. rewrite HDO0. simpl.
        rewrite FINDOPTF in HDO1. inv HDO1. apply interpreter_proof.init_regs_correct in HDO0.
        repeat (esplit; eauto).
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
    eapply no_entry in VALIDATE as NO_ENTRY; eauto.
    assert (NO_LOOP: fs_lbl <> condl).
    { poseq_destr fs_lbl condl; auto. rewrite SRC_COND in SRC_FS. inv SRC_FS. }
    assert (NO_FRESH: fs_lbl <> fresh_label (Pos.succ condl) c).
    { poseq_destr fs_lbl (fresh_label (Pos.succ condl) c); auto. erewrite fresh_label_correct in SRC_FS; auto. inv SRC_FS. }
    assert (NO_FRESH_COND: condl <> fresh_label (Pos.succ condl) c).
    { poseq_destr condl (fresh_label (Pos.succ condl) c); auto. erewrite fresh_label_correct in SRC_COND; eauto. inv SRC_COND. }
    inv MATCH.

    + rewrite OPT in OPTV. inv OPTV. (* assume_match *)
      unfold c in SRC_FS. rewrite FS_SRC in SRC_FS. inv SRC_FS.
      unfold c in SRC_COND. rewrite CO_SRC in SRC_COND. inv SRC_COND.
      eapply no_cond in CO_SRC as NO_COND; eauto. 
      inv STEP.
      { inv STEP0; rewrite CODE in AS_OPT; inv AS_OPT.
        - exists Two. exists (State s vsrc iftrue rm ms). split. (* Assume holds: we catch-up the delay *)
          + left. eapply plus_two with (s2:=(State s vsrc condl rm ms)).
            * eapply nd_exec_Framestate_go_on. econstructor; eauto.
            * apply nd_exec_lowered. eapply exec_Cond; eauto. simpl.
              destruct vcond; auto. contradiction.
            * auto.
          + eapply opt_match; eauto. poseq_destr iftrue condl. simpl in NO_COND.
            rewrite Pos.eqb_refl in NO_COND. inv NO_COND. auto.
            eapply analyze_correct. eauto. eapply CO_SRC. simpl. auto. unfold dr_transf.
            rewrite CO_SRC. eapply analyze_correct. eauto. apply FS_SRC. simpl; auto.
            unfold dr_transf. rewrite FS_SRC. auto. intro. subst. simpl in NO_COND.
            rewrite Pos.eqb_refl in NO_COND. inv NO_COND.
        - simpl in FINDF0. rewrite <- base_version_unchanged in FINDF0. rewrite FINDF0 in FINDF. inv FINDF.
          apply synth_frame_unchanged in SYNTH0. synth_determ; auto.          
          exists Zero. exists (State (synth++s) newver la newrm0 ms). (* Assume fails: we deoptimize at the src FS *)
          split.
          + left. apply plus_one. eapply nd_exec_Framestate_deopt. econstructor; eauto.
          + eapply refl_match; eauto. apply app_match; auto. apply match_stack_same.
      }
      * inv DEOPT_COND. rewrite CODE in AS_OPT. inv AS_OPT.
      * inv DEOPT_COND. rewrite CODE in AS_OPT. inv AS_OPT.

    + rewrite OPT in OPTV. inv OPTV. (* cond_match_delay *)
      unfold c in SRC_FS. rewrite FS_SRC in SRC_FS. inv SRC_FS.
      unfold c in SRC_COND. rewrite CO_SRC in SRC_COND. inv SRC_COND.
      eapply no_cond in CO_SRC as NO_COND; eauto. 
      inv STEP.
      { inv STEP0; rewrite CODE in CO_OPT; inv CO_OPT. destruct v as [v]. destruct v; simpl.
        - exists Two. exists (State s vsrc iffalse rm ms). split. (* We go to the branch without Assume *)
          + left. eapply plus_two with (s2:=(State s vsrc condl rm ms)).
            (* we take 2 steps to catch up the delay*)
            * eapply nd_exec_Framestate_go_on. econstructor; eauto.
            * eapply nd_exec_lowered. eapply exec_Cond; eauto.
            * auto.
          + poseq_destr iffalse condl. simpl in NO_COND. rewrite Pos.eqb_refl in NO_COND.
            poseq_destr iftrue condl; inv NO_COND. econstructor; eauto.
            eapply analyze_correct. eauto. apply CO_SRC. simpl; auto. unfold dr_transf. rewrite CO_SRC.
            eapply analyze_correct. eauto. apply FS_SRC. simpl; auto. unfold dr_transf. rewrite FS_SRC.
            auto.
        - exists Zero. exists (State s vsrc fs_lbl rm ms). split. (* We delay one more step *)
          + right. split. apply star_refl. constructor.
          + eapply assume_match; eauto. unfold not. intros. inv H.
        - exists Zero. exists (State s vsrc fs_lbl rm ms). split. (* We delay one more step *)
          + right. split. apply star_refl. constructor.
          + eapply assume_match; eauto. unfold not. intros. inv H. }
      * inv DEOPT_COND. rewrite CODE in CO_OPT. inv CO_OPT.
      * inv DEOPT_COND. rewrite CODE in CO_OPT. inv CO_OPT.

    + rewrite OPT in OPTV. inv OPTV. (* opt_match *)
      poseq_destr lbl fs_lbl.
      { inv STEP.               (* At the Framestate used for insertion *)
        - inv STEP0; unfold vins in CODE; simpl in CODE; rewrite PTree.gso in CODE; auto;
            rewrite PTree.gso in CODE; auto; rewrite CODE in SRC_FS; inv SRC_FS.
        - exists One. exists (State s vsrc fs_lbl rm ms). split. (* OPT_FS goes on: we delay match with cond *)
            * right. split. apply star_refl. constructor.
            * destruct tgt. inv DEOPT_COND. (* apply eval_expr_correct in EVAL. *)
              unfold vins in CODE. simpl in CODE. rewrite PTree.gso in CODE; auto.
              apply synth_frame_unchanged in SYNTH. simpl in FINDF. rewrite <- base_version_unchanged in FINDF.
              rewrite PTree.gso in CODE; auto. rewrite CODE in SRC_FS. inv SRC_FS.
              eapply cond_match_delay; fold c; eauto.
              unfold vins. simpl. rewrite PTree.gso; auto. rewrite PTree.gso; auto.
              unfold vins. simpl. rewrite PTree.gso; auto. rewrite PTree.gss; auto.
              unfold vins. simpl. rewrite PTree.gss; auto.
        - exists Zero. exists (State (synth++s) newver la newrm ms). split. (* OPT FS deopt: SRC FS also deopts *)
          + destruct tgt as [ftgt ltgt]. left. apply plus_one. eapply nd_exec_Framestate_deopt; eauto.
            inv DEOPT_COND. unfold vins in CODE. simpl in CODE. rewrite PTree.gso in CODE; auto.
            rewrite PTree.gso in CODE; auto. simpl in FINDF. rewrite <- base_version_unchanged in FINDF.
            apply synth_frame_unchanged in SYNTH. econstructor; fold c; eauto. 
          + apply refl_match; auto. apply app_match; auto. apply match_stack_same. }

      { eapply code_preservation in OPT as SAME_CODE; eauto.
        assert (SOME_CODE: exists i, (ver_code vsrc)!lbl = Some i) by (eapply safe_code; eauto).
        destruct SOME_CODE as [isrc SOME_CODE].
        assert (NO_COND: not_in_list (instr_succ isrc) condl = true) by (eapply no_cond; eauto).
        inv STEP.               (* not at the Framestate used for insertion *)
        - inv STEP0; rewrite <- SAME_CODE in CODE; rewrite CODE in SOME_CODE; inv SOME_CODE; simpl in NO_COND.
          + exists Two. exists (State s vsrc next rm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Nop; eauto.
            * econstructor; eauto. def_ok. poseq_destr next condl; auto. inv NO_COND. 
          + exists Two. exists (State s vsrc next (rm#reg<-v) ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Op; eauto.
            * econstructor; eauto. def_ok. apply define_insert. auto.
              poseq_destr next condl; auto. inv NO_COND.
          + exists Two. exists (State s vsrc next newrm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Move; eauto.
            * econstructor; eauto. def_ok. eapply define_insert_list; eauto.
              poseq_destr next condl; auto. inv NO_COND.
          + exists Two. exists (State s vsrc (pc_cond v iftrue0 iffalse0) rm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Cond; eauto.
            * econstructor; eauto. def_ok. destruct v; destruct z; eauto.
              destruct pc_cond_disj with (v:=v) (ift:=iftrue0) (iff:=iffalse0); rewrite H.
              poseq_destr iftrue0 condl; auto. inv NO_COND. poseq_destr iffalse0 condl; auto.
              poseq_destr iftrue0 condl; auto; inv NO_COND.
          + poseq_destr fid fid0.
            * simpl in FINDF. erewrite find_function_same in FINDF; eauto. inv FINDF.
              rewrite current_version_same.
              exists Two. exists (State (Stackframe retreg vsrc next rm :: s) vsrc (ver_entry vsrc) newrm ms). split.
              left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
              econstructor; eauto. constructor; auto. econstructor; eauto.
              intro. def_ok. apply define_insert; auto.
              poseq_destr next condl; auto. inv NO_COND.
              unfold vins. simpl. eapply analyze_init; eauto.
            * simpl in FINDF. erewrite <- find_function_unchanged in FINDF; eauto.
              exists Zero. exists (State (Stackframe retreg vsrc next rm :: s) (current_version func) (ver_entry (current_version func)) newrm ms). split.
              left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
              constructor; auto. constructor; auto. econstructor; eauto.
              intro. def_ok. apply define_insert; auto.
              poseq_destr next condl; auto. inv NO_COND.
          + inv MATCHSTACK. inv MSF.
            * exists Zero. exists (State s1 fprev next (rmprev#retreg<-retval) ms). split.
              left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
              constructor; auto.
            * exists Two. exists (State s1 vsrc next (rmprev#retreg<-retval) ms). split.
              left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
              econstructor; eauto.
          + inv MATCHSTACK. exists Zero. exists (Final retval ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return_Final; eauto.
            * constructor; auto.
          + exists Two. exists (State s vsrc next rm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Printexpr; eauto.
            * econstructor; eauto. def_ok. poseq_destr next condl; auto. inv NO_COND.
          + exists Two. exists (State s vsrc next rm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Printstring; eauto.
            * econstructor; eauto. def_ok. poseq_destr next condl; auto. inv NO_COND.
          + exists Two. exists (State s vsrc next rm newms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Store; eauto.
            * econstructor; eauto. def_ok. poseq_destr next condl; auto. inv NO_COND.
          + exists Two. exists (State s vsrc next (rm#reg<-val) ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Load; eauto.
            * econstructor; eauto. def_ok. apply define_insert; auto.
              poseq_destr next condl; auto. inv NO_COND.
          + exists Two. exists (State s vsrc next rm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
            * econstructor; eauto. def_ok. poseq_destr next condl; auto. inv NO_COND.
          + exists Zero. exists (State (synth++s) newver la newrm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
              simpl in FINDF. rewrite <- base_version_unchanged in FINDF. auto.
              apply synth_frame_unchanged in SYNTH. auto.
            * constructor; auto. apply app_match; auto. apply match_stack_same.
        - exists Two. destruct tgt. inv DEOPT_COND. simpl in FINDF. rewrite <- base_version_unchanged in FINDF.
          apply synth_frame_unchanged in SYNTH. exists (State s vsrc next rm ms). split.
          + left. apply plus_one. eapply nd_exec_Framestate_go_on. econstructor; eauto.
            rewrite CODE in SAME_CODE. eauto.
          + rewrite <- SAME_CODE in CODE. rewrite CODE in SOME_CODE. inv SOME_CODE.
            eapply opt_match; eauto. def_ok.
            simpl in NO_COND. poseq_destr next condl; auto. inv NO_COND.
        - exists Zero. destruct tgt. inv DEOPT_COND. simpl in FINDF. rewrite <- base_version_unchanged in FINDF.
          apply synth_frame_unchanged in SYNTH. exists (State (synth++s) newver la newrm ms). split.
          + left. apply plus_one. eapply nd_exec_Framestate_deopt. econstructor; eauto.
            rewrite CODE in SAME_CODE. eauto.
          + apply refl_match; auto. apply app_match; auto. apply match_stack_same. }

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
        - exists Zero. exists (State s v' (pc_cond v iftrue0 iffalse0) rm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Cond; eauto.
          + apply refl_match; auto.
        - poseq_destr fid fid0.
          + simpl in FINDF. erewrite find_function_same in FINDF; eauto. inv FINDF.
            rewrite current_version_same. destruct tgt.
            exists Two. exists (State (Stackframe retreg v' next rm :: s) vsrc (ver_entry vsrc) newrm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
            * unfold validator in VALIDATE. fold c in VALIDATE. rewrite SRC_FS in VALIDATE.
              rewrite SRC_COND in VALIDATE. destruct (only_pred c condl fs_lbl) eqn:ONLY; inv VALIDATE.
              poseq_destr condl (ver_entry vsrc); inv H0. repeat do_ok.
              eapply opt_match; fold c; eauto. constructor; auto. constructor; auto.
              unfold vins. simpl. eapply analyze_init; eauto.
          + simpl in FINDF. erewrite <- find_function_unchanged in FINDF; eauto.
            exists Zero. exists (State (Stackframe retreg v' next rm :: s) (current_version func) (ver_entry (current_version func)) newrm ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Call; eauto.
            * constructor; auto. constructor; auto. constructor; auto.
        - inv MATCHSTACK. inv MSF.
          + exists Zero. exists (State s1 fprev next (rmprev#retreg<-retval) ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
            * apply refl_match; auto.
          + destruct tgt. exists Two. exists (State s1 vsrc next (rmprev#retreg<-retval) ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
            * rewrite AS_INSERT in OPTV. inv OPTV. eapply opt_match; fold c; eauto. 
        - inv MATCHSTACK. exists Zero. exists (Final retval ms). split.
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
