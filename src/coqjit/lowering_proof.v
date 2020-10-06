(* Correctness proof of the lowering pass *)

Require Export specIR.
Require Export lowering.
Require Export ir_properties.
Require Export internal_simulations.

(* Matching stackframes: a version may have been replaced with its lowered version *)
Inductive match_stackframe: stackframe -> stackframe -> Prop :=
| frame_same: forall sf, match_stackframe sf sf
| frame_lowered:
    forall r v lbl rm vlow
      (LOW: lowering_version v = vlow),
      match_stackframe (Stackframe r v lbl rm) (Stackframe r vlow lbl rm).

(* Generalizing match_stackframe to the entire stack *)
Inductive match_stack: stack -> stack -> Prop :=
| match_nil:
    match_stack nil nil
| match_cons:
    forall s s' sf sf'
      (MS: match_stack s s')
      (MSF: match_stackframe sf sf'),
      match_stack (sf::s) (sf'::s').

Lemma match_stack_same:
  forall s, match_stack s s.
Proof.
  intros. induction s; constructor. auto. apply frame_same.
Qed.

(** * Lowering Properties *)
Lemma base_low_refl_code:
  forall c,
    base_code c ->
    lowering_code c = c.
Proof.
  intros c H. unfold base_code in H. unfold lowering_code.
  unfold PTree.map1. induction c; auto.
  rewrite IHc2. 2: { intros. eapply H with (pc:=(pc~1)%positive). simpl. auto. }
  rewrite IHc1. 2: { intros. eapply H with (pc:=(pc~0)%positive). simpl. auto. }
  destruct o; simpl; auto.
  assert (~is_spec i). { apply H with (pc:=1%positive). simpl. auto. }
  assert (transf_instr i = i). { destruct i; auto. exfalso. apply H0. constructor. }
  rewrite H1. auto.
Qed.

Lemma fn_base_low:
  forall f,
    lowering_version (fn_base f) = fn_base f.
Proof.
  intros f. unfold lowering_version. rewrite base_low_refl_code.
  destruct f; simpl; auto. destruct fn_base; simpl; auto.
  destruct f. simpl. unfold base_version in base_no_spec. auto.
Qed.

Lemma base_low_refl:
  forall v,
    base_version v ->
    lowering_version v = v.
Proof.
  intros v H. unfold lowering_version. unfold base_version in H. rewrite base_low_refl_code; auto.
  destruct v. simpl. auto.
Qed.  

Lemma same_params:
  forall f,
    (fn_params f) = (fn_params (lowering_function f)).
Proof.
  intros. unfold lowering_function. destruct (fn_opt f); simpl; auto.
Qed.

Lemma same_entry:
  forall f,
    ver_entry (current_version f) = ver_entry (current_version (lowering_function f)).
Proof.
  intros f. unfold lowering_function. destruct (fn_opt f) eqn:OPT; simpl; auto.
  unfold current_version. rewrite OPT. auto.
Qed.

Lemma lowering_current:
  forall f, lowering_version (current_version f) = current_version (lowering_function f).
Proof.
  intros f. unfold lowering_function. destruct (fn_opt f) eqn:OPT; simpl; auto.
  unfold current_version. rewrite OPT. simpl. auto.
  unfold current_version. rewrite OPT. apply fn_base_low.
Qed.

(** * Match states invariant  *)
(* This proof is a lockstep backward internal simulation.
   Each step of the optimized program is matched with a step of the source.
   No index is needed for the match_states invariant.
   Framestate steps are matched with Nop steps.

<<
                 
       st1 --------------- st2
        |                   |
       t|                   |t
        |                   |
        v                   v
       st1'--------------- st2'
                 
>>
*)

Inductive match_states (p:program) : unit -> specIR.state -> specIR.state -> Prop :=
| lowered_match:
    forall s s' v vlow pc rm ms
      (LOW: lowering_version v = vlow)
      (MATCHSTACK: match_stack s s'),
      (match_states p) tt (State s v pc rm ms) (State s' vlow pc rm ms)
| refl_match:
    forall s s' v pc rm ms
      (MATCHSTACK: match_stack s s'),
      (match_states p) tt (State s v pc rm ms) (State s' v pc rm ms)
| final_match:
    forall retval ms,
      (match_states p) tt (Final retval ms) (Final retval ms).

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

(** * Code preservation properties  *)
Lemma preserved_code:
  forall v vlow i pc,
    lowering_version v = vlow ->  
    (ver_code vlow) # pc = Some i ->
    exists i', (ver_code v) # pc = Some i' /\ transf_instr i' = i.
Proof.
  intros v vlow i pc LOW CODE. unfold lowering_version in LOW. rewrite <- LOW in CODE.
  simpl in CODE. unfold lowering_code in CODE.
  rewrite PTree.gmap1 in CODE. unfold option_map in CODE.
  destruct ((ver_code v)!pc); inv CODE.
  exists i0. split; auto.
Qed.

Lemma code_preserved:
  forall v vlow i pc,
    lowering_version v = vlow ->  
    (ver_code v) # pc = Some i ->
    (ver_code vlow) # pc = Some (transf_instr i).
Proof.
  intros v vlow i pc LOW CODE. unfold lowering_version in LOW. rewrite <- LOW. simpl.
  unfold lowering_code. rewrite PTree.gmap1. unfold option_map. rewrite CODE. auto.
Qed.

Lemma base_version_unchanged:
  forall p fid,
    find_base_version fid p = find_base_version fid (lowering p).
Proof.
  intros. unfold find_base_version, lowering, find_function, find_function_list.
  simpl. rewrite PTree.gmap1. unfold option_map.
  destruct ((prog_funlist p)!fid) eqn:FINDF; auto.
  unfold lowering_function. destruct (fn_opt f); auto.
Qed.

Lemma find_function_lowered:
  forall p fid f,
    find_function fid (lowering p) = Some f ->
    exists f', find_function fid p = Some f' /\ lowering_function f' = f.
Proof.
  intros p fid f H. unfold find_function, find_function_list in *. unfold lowering in H. simpl in H.
  rewrite PTree.gmap1 in H. unfold option_map in H.
  destruct ((prog_funlist p)!fid) eqn:FINDF; inv H.
  exists f0. split; auto.
Qed.

Lemma lowered_find_function:
  forall p fid f,
    find_function fid p = Some f ->
    find_function fid (lowering p) = Some (lowering_function f).
Proof.
  unfold find_function, find_function_list, lowering. intros p fid f FINDF. simpl.
  rewrite PTree.gmap1. unfold option_map. rewrite FINDF. auto.
Qed.

(** * Invariant preservation  *)
Lemma match_synth:
  forall p rm sl synthlow p0,
    p0 = lowering p ->
    specIR.synthesize_frame p0 rm sl synthlow ->
    exists synthsrc, specIR.synthesize_frame p rm sl synthsrc /\ match_stack synthsrc synthlow.
Proof.
  intros p rm sl synthlow p0 LOW SYNTH.
  induction SYNTH; intros.
  - exists nil. split; constructor.
  - specialize (IHSYNTH LOW). destruct IHSYNTH as [synthsrc [SYNTH' MATCH]]. exists ((Stackframe r version l update)::synthsrc).
    split. constructor; auto.
    rewrite LOW in FINDV. rewrite <- base_version_unchanged in FINDV. rewrite FINDV. auto.
    constructor; auto. constructor; auto.
Qed.

Lemma synth_match:
  forall p rm sl synth,
    specIR.synthesize_frame p rm sl synth ->
    exists synthlow, specIR.synthesize_frame (lowering p) rm sl synthlow.
Proof.
  intros p rm sl synth SYNTH. induction SYNTH.
  - exists nil. constructor.
  - destruct IHSYNTH as [sylow IHSYNTH].
    rewrite base_version_unchanged in FINDV.
    exists (Stackframe r version l update::sylow). constructor; auto.
Qed.

Lemma app_match:
  forall synth synthlow s slow,
    match_stack s slow ->
    match_stack synth synthlow ->
    match_stack (synth++s) (synthlow++slow).
Proof.
  intros. induction H0.
  - simpl. auto.
  - repeat rewrite <- app_comm_cons. apply match_cons; auto.
Qed.


(* for backward simulations, safety of the source must be shown to be preserved *)
Lemma safe_preserved_state:
  forall p i s v pc rm ms s2,
    match_states p i (State s v pc rm ms) s2 ->
    safe (specir_sem p) (State s v pc rm ms) ->
    exists t, exists s2', specir_step (lowering p) s2 t s2'.
Proof.
  intros p i s v pc rm ms s2 MATCH SAFE. inv MATCH.
  { apply safe_step in SAFE as [nexts [t STEP]]. exists t.
    inv STEP.
    - inv STEP0; eapply code_preserved in CODE; eauto; simpl in CODE; simpl; eauto.
      + exists (State s' (lowering_version v) next rm ms). apply nd_exec_lowered. eapply exec_Nop. eauto.
      + exists (State s' (lowering_version v) next (rm#reg<-v0) ms). apply nd_exec_lowered. eapply exec_Op; eauto.
      + exists (State s' (lowering_version v) next newrm ms). apply nd_exec_lowered. eapply exec_Move; eauto.
      + exists (State s' (lowering_version v) (pc_cond v0 iftrue iffalse) rm ms). apply nd_exec_lowered.
        eapply exec_Cond; eauto.
      + apply lowered_find_function in FINDF. simpl in FINDF.
        exists (State (Stackframe retreg (lowering_version v) next rm ::s') (current_version (lowering_function func)) (ver_entry (current_version (lowering_function func))) newrm ms).
        apply nd_exec_lowered. eapply exec_Call; eauto. unfold lowering_function.
        destruct (fn_opt func); simpl; auto.      
      + inv MATCHSTACK. inv MSF.
        * exists (State s'0 fprev next (rmprev#retreg<-retval) ms).
          apply nd_exec_lowered. eapply exec_Return; eauto.
        * exists (State s'0 (lowering_version fprev) next (rmprev#retreg<-retval) ms).
          apply nd_exec_lowered. eapply exec_Return; eauto.
      + inv MATCHSTACK. exists (Final retval ms). apply nd_exec_lowered. eapply exec_Return_Final; eauto.
      + exists (State s' (lowering_version v) next rm ms). apply nd_exec_lowered. eapply exec_Printexpr; eauto.
      + exists (State s' (lowering_version v) next rm ms). apply nd_exec_lowered. eapply exec_Printstring. auto.
      + exists (State s' (lowering_version v) next rm newms). apply nd_exec_lowered. eapply exec_Store; eauto.
      + exists (State s' (lowering_version v) next (rm#reg<-val) ms). apply nd_exec_lowered. eapply exec_Load; eauto.
      + exists (State s' (lowering_version v) next rm ms). apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
      + apply synth_match in SYNTH as [synthlow SYNTH]. rewrite base_version_unchanged in FINDF.
        exists (State (synthlow ++ s') newver la newrm ms). apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
    - exists (State s' (lowering_version v) next rm ms). apply nd_exec_lowered. eapply exec_Nop. inv DEOPT_COND.
      eapply code_preserved in CODE; eauto.
    - exists (State s' (lowering_version v) next rm ms). apply nd_exec_lowered. eapply exec_Nop. inv DEOPT_COND.
      eapply code_preserved in CODE; eauto. }
  { apply safe_step in SAFE as [nexts [t STEP]]. exists t.
    inv STEP.
    - inv STEP0. 
      + exists (State s' v next rm ms). apply nd_exec_lowered. eapply exec_Nop. eauto.
      + exists (State s' v next (rm#reg<-v0) ms). apply nd_exec_lowered. eapply exec_Op; eauto.
      + exists (State s' v next newrm ms). apply nd_exec_lowered. eapply exec_Move; eauto.
      + exists (State s' v (pc_cond v0 iftrue iffalse) rm ms). apply nd_exec_lowered. eapply exec_Cond; eauto.
      + apply lowered_find_function in FINDF. simpl in FINDF.
        exists (State (Stackframe retreg v next rm ::s') (current_version (lowering_function func)) (ver_entry (current_version (lowering_function func))) newrm ms).
        apply nd_exec_lowered. eapply exec_Call; eauto. unfold lowering_function.
        destruct (fn_opt func); simpl; auto.      
      + inv MATCHSTACK. inv MSF.
        * exists (State s'0 fprev next (rmprev#retreg<-retval) ms).
          apply nd_exec_lowered. eapply exec_Return; eauto.
        * exists (State s'0 (lowering_version fprev) next (rmprev#retreg<-retval) ms).
          apply nd_exec_lowered. eapply exec_Return; eauto.
      + inv MATCHSTACK. exists (Final retval ms). apply nd_exec_lowered. eapply exec_Return_Final; eauto.
      + exists (State s' v next rm ms). apply nd_exec_lowered. eapply exec_Printexpr; eauto.
      + exists (State s' v next rm ms). apply nd_exec_lowered. eapply exec_Printstring. auto.
      + exists (State s' v next rm newms). apply nd_exec_lowered. eapply exec_Store; eauto.
      + exists (State s' v next (rm#reg<-val) ms). apply nd_exec_lowered. eapply exec_Load; eauto.
      + exists (State s' v next rm ms). apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
      + apply synth_match in SYNTH as [synthlow SYNTH]. rewrite base_version_unchanged in FINDF.
        exists (State (synthlow ++ s') newver la newrm ms). apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
    - exists (State s' v next rm ms). inv DEOPT_COND. apply synth_match in SYNTH as [sl' SYNTH].
      eapply nd_exec_Framestate_go_on. 
      econstructor; eauto. rewrite <- base_version_unchanged. eauto. 
    - exists (State s' v next rm ms). inv DEOPT_COND. apply synth_match in SYNTH as [sl' SYNTH].
      eapply nd_exec_Framestate_go_on. 
      econstructor; eauto. rewrite <- base_version_unchanged. eauto. }
Qed.

Lemma safe_preserved_final:
  forall p i v ms s2,
    match_states p i (Final v ms) s2 ->
    exists r, final_state (lowering p) s2 r.
Proof.
  intros p i v ms s2 MATCH. inv MATCH. exists v. constructor.
Qed.


(* Proved directly with a backward simulation *)
Theorem lowering_correct:
  forall p newp,
    lowering p = newp ->
    backward_internal_simulation p newp.
Proof.
  intros. apply Backward_internal_simulation with (bsim_match_states:=match_states p) (bsim_order:=order).
  - apply wfounded.
  - apply trans.
  - unfold reflexive_forge. intros synchro stack r1 s1 ms FORGE.
    destruct synchro; simpl in FORGE; repeat do_ok; simpl.
    + erewrite lowered_find_function; eauto. simpl. rewrite <- same_params. rewrite HDO0. simpl.
      repeat (esplit; eauto). simpl. rewrite <- same_entry. apply lowered_match.
      apply lowering_current. apply match_stack_same.
    + destruct stack; try destruct s; inv FORGE.
      * repeat (esplit; eauto). constructor.
      * repeat (esplit; eauto). simpl. apply refl_match. apply match_stack_same.
    + destruct d. repeat do_ok. simpl. rewrite <- base_version_unchanged. rewrite HDO0. simpl.
      repeat (esplit; eauto). simpl. apply refl_match. apply match_stack_same.
    + inv FORGE. exists r1. exists s1. split; auto. exists tt. destruct r1; simpl.
      * apply refl_match. apply match_stack_same.
      * apply final_match.
  - intros i s1 s2 r MATCH SAFE FINAL.
    inv FINAL. inv MATCH. exists (Final r ms). split. apply star_refl. constructor.

  - intros i s1 s2 MATCH SAFE.  (* safe preserved *)
    inv MATCH.
    + eapply safe_preserved_state in SAFE as [t [s2' STEP]]. 2: constructor; eauto.
      right. exists t. exists s2'. auto.
    + eapply safe_preserved_state in SAFE as [t [s2' STEP]]. 
      right. exists t. exists s2'. apply STEP. apply refl_match. auto.
    + left. simpl. eapply safe_preserved_final. constructor.

  - intros s2 t s2' STEP i s1 MATCH SAFE. exists tt. inv MATCH.
    +                           (* lowered_match *)
      inv STEP.
      { inv STEP0; eapply preserved_code in CODE as [i' [CODE TRANSF]]; eauto; destruct i'; inv TRANSF.
        - exists (State s v next rm ms). split. (* When Nop in the target comes from Nop in the source *)
            left. apply plus_one. apply nd_exec_lowered. eapply exec_Nop; eauto.
            constructor; auto.
        - exists (State s v next rm ms). split. (* Nop in the target comes from Framestate in the source *)
          left. apply plus_one. apply safe_step in SAFE as [s'' [t STEP]].
          { inv STEP.
            + inv STEP0; rewrite CODE0 in CODE; inv CODE.
            + inv DEOPT_COND. rewrite CODE0 in CODE. inv CODE.
              eapply nd_exec_Framestate_go_on. econstructor; eauto.
            + inv DEOPT_COND. rewrite CODE0 in CODE. inv CODE.
              eapply nd_exec_Framestate_go_on. econstructor; eauto. }
          constructor; auto.
        - exists (State s v next (rm#reg<-v0) ms). split.
          left. apply plus_one. apply nd_exec_lowered. eapply exec_Op; eauto.
          constructor; auto.
        - exists (State s v next newrm ms). split.
          left. apply plus_one. apply nd_exec_lowered. eapply exec_Move; eauto.
          constructor; auto.
        - exists (State s v (pc_cond v0 iftrue iffalse) rm ms). split.
          left. apply plus_one. apply nd_exec_lowered. eapply exec_Cond; eauto.
          constructor; auto.
        - destruct (fn_opt func) eqn:OPT.
          + apply find_function_lowered in FINDF as [f' [FINDF LOW]].
            exists (State (Stackframe retreg v next rm::s) (current_version f') (ver_entry (current_version f')) newrm ms).
            split.
            left. apply plus_one. apply nd_exec_lowered.
            { eapply exec_Call.
              - apply CODE.
              - apply FINDF.
              - auto.
              - apply EVALL.
              - rewrite <- LOW in INIT_REGS. unfold lowering_function in INIT_REGS.
                destruct (fn_opt f'); simpl in INIT_REGS; auto. }
            assert (ver_entry (current_version f') = ver_entry (current_version func)).
            { rewrite <- LOW. unfold lowering_function, current_version.
              destruct (fn_opt f') eqn:OPT'; simpl; auto.
              rewrite OPT'. auto. }
            rewrite H. constructor; auto.
            * rewrite <- LOW. unfold current_version, lowering_function.
              destruct (fn_opt f') eqn:OPT'; simpl; try rewrite OPT'; auto.
              apply fn_base_low.
            * constructor; auto. constructor; auto.
          + exists (State (Stackframe retreg v next rm::s) (current_version func) (ver_entry (current_version func)) newrm ms). split.
            left. apply plus_one. apply nd_exec_lowered.
            unfold find_function, find_function_list, lowering in *. simpl in FINDF.
            rewrite PTree.gmap1 in FINDF. unfold option_map in FINDF. simpl.
            destruct ((prog_funlist p)! fid) eqn:FIND; inv FINDF.
            destruct (fn_opt f) eqn:OPT'. { unfold lowering_function in OPT. rewrite OPT' in OPT. inv OPT. }
            { eapply exec_Call.
              - apply CODE.
              - unfold find_function, find_function_list. rewrite FIND. auto.
              - unfold current_version. unfold lowering_function. rewrite OPT'. rewrite OPT'. auto.
              - apply EVALL.
              - unfold lowering_function in INIT_REGS. rewrite OPT' in INIT_REGS. auto. }
            constructor; auto.
            * unfold current_version. rewrite OPT. apply fn_base_low.
            * constructor; auto. constructor; auto.
        - inv MATCHSTACK. inv MSF.
          + exists (State s1 fprev next (rmprev#retreg<-retval) ms). split.
            left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
            apply refl_match. auto.
          + exists (State s1 v0 next (rmprev#retreg<-retval) ms). split.
            left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
            constructor; auto.
        - inv MATCHSTACK. exists (Final retval ms). split.
          left. apply plus_one. apply nd_exec_lowered. eapply exec_Return_Final; eauto.
          constructor; auto.
        - exists (State s v next rm ms). split.
          left. apply plus_one. apply nd_exec_lowered. eapply exec_Printexpr; eauto.
          constructor; auto.
        - exists (State s v next rm ms). split.
          left. apply plus_one. apply nd_exec_lowered. eapply exec_Printstring; eauto.
          constructor; eauto.
        - exists (State s v next rm newms). split.
          left. apply plus_one. apply nd_exec_lowered. eapply exec_Store; eauto.
          constructor; auto.
        - exists (State s v next (rm#reg<-val) ms). split.
          left. apply plus_one. apply nd_exec_lowered. eapply exec_Load; eauto.
          constructor; auto.
        - exists (State s v next rm ms). split.
          left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
          constructor; auto.
        - eapply match_synth in SYNTH as [synthsrc [SYNTH MATCH]]; simpl; eauto.
          exists (State (synthsrc++s) newver la newrm ms). split.
          left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
          rewrite base_version_unchanged. auto.
          constructor; auto. unfold find_base_version in FINDF. simpl in FINDF.
          destruct (find_function fa (lowering p)) eqn:FINDF'; inv FINDF. apply fn_base_low.
          apply app_match; auto. }
      * inv DEOPT_COND. unfold lowering_version, lowering_code in CODE. simpl in CODE.
        rewrite PTree.gmap1 in CODE. unfold option_map in CODE.
        destruct ((ver_code v)!pc); inv CODE. destruct i; inv H0.
      * inv DEOPT_COND. unfold lowering_version, lowering_code in CODE. simpl in CODE.
        rewrite PTree.gmap1 in CODE. unfold option_map in CODE.
        destruct ((ver_code v)!pc); inv CODE. destruct i; inv H0.
    + inv STEP.                 (* refl match *)
      { inv STEP0.
        - exists (State s v next rm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Nop; eauto.
          + apply refl_match; auto.
        - exists (State s v next (rm#reg<-v0) ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Op; eauto.
          + apply refl_match; auto.
        - exists (State s v next newrm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Move; eauto.
          + apply refl_match; auto.
        - exists (State s v (pc_cond v0 iftrue iffalse) rm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Cond; eauto.
          + apply refl_match; auto.
        - destruct (fn_opt func) eqn:OPT.
          + apply find_function_lowered in FINDF as [f' [FINDF LOW]].
            exists (State (Stackframe retreg v next rm::s) (current_version f') (ver_entry (current_version f')) newrm ms).
            split.
            left. apply plus_one. apply nd_exec_lowered.
            { eapply exec_Call.
              - apply CODE.
              - apply FINDF.
              - auto.
              - apply EVALL.
              - rewrite <- LOW in INIT_REGS. unfold lowering_function in INIT_REGS.
                destruct (fn_opt f'); simpl in INIT_REGS; auto. }
            assert (ver_entry (current_version f') = ver_entry (current_version func)).
            { rewrite <- LOW. unfold lowering_function, current_version.
              destruct (fn_opt f') eqn:OPT'; simpl; auto.
              rewrite OPT'. auto. }
            rewrite H. constructor; auto.
            * rewrite <- LOW. unfold current_version, lowering_function.
              destruct (fn_opt f') eqn:OPT'; simpl; try rewrite OPT'; auto.
              apply fn_base_low.
            * constructor; auto. constructor; auto.
          + exists (State (Stackframe retreg v next rm::s) (current_version func) (ver_entry (current_version func)) newrm ms). split.
            left. apply plus_one. apply nd_exec_lowered.
            unfold find_function, find_function_list, lowering in *. simpl in FINDF.
            rewrite PTree.gmap1 in FINDF. unfold option_map in FINDF. simpl.
            destruct ((prog_funlist p)! fid) eqn:FIND; inv FINDF.
            destruct (fn_opt f) eqn:OPT'. { unfold lowering_function in OPT. rewrite OPT' in OPT. inv OPT. }
            { eapply exec_Call.
              - apply CODE.
              - unfold find_function, find_function_list. rewrite FIND. auto.
              - unfold current_version. unfold lowering_function. rewrite OPT'. rewrite OPT'. auto.
              - apply EVALL.
              - unfold lowering_function in INIT_REGS. rewrite OPT' in INIT_REGS. auto. }
            constructor; auto.
            * unfold current_version. rewrite OPT. apply fn_base_low.
            * constructor; auto. constructor; auto.          
        - inv MATCHSTACK. inv MSF.
          + exists (State s1 fprev next (rmprev#retreg<-retval) ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
            * apply refl_match. auto.
          + exists (State s1 v0 next (rmprev#retreg<-retval) ms). split.
            * left. apply plus_one. apply nd_exec_lowered. eapply exec_Return; eauto.
            * constructor; auto.
        - inv MATCHSTACK. exists (Final retval ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Return_Final; eauto.
          + apply final_match; auto.
        - exists (State s v next rm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Printexpr; eauto.
          + apply refl_match; auto.
        - exists (State s v next rm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Printstring; eauto.
          + apply refl_match; auto.
        - exists (State s v next rm newms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Store; eauto.
          + apply refl_match; auto.
        - exists (State s v next (rm#reg<-val) ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Load; eauto.
          + apply refl_match; auto.
        - exists (State s v next rm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_holds; eauto.
          + apply refl_match; auto.
        - simpl in SYNTH. eapply match_synth with (p:=p) in SYNTH as [synthsrc [SYNTH MS]].
          exists (State (synthsrc++s) newver la newrm ms). split.
          + left. apply plus_one. apply nd_exec_lowered. eapply exec_Assume_fails; eauto.
            rewrite base_version_unchanged; auto. 
          + apply refl_match; auto. apply app_match; auto.
          + auto. }
      { inv DEOPT_COND. eapply match_synth in SYNTH as [synthsrc [SYNTH MS]].
        exists (State s v next rm ms). split.
        - left. apply plus_one. eapply nd_exec_Framestate_go_on. econstructor; eauto.
          rewrite base_version_unchanged. eauto.
        - apply refl_match; auto.
        - simpl. auto. }
      { inv DEOPT_COND. eapply match_synth in SYNTH as [synthsrc [SYNTH MS]].
        exists (State (synthsrc++s) newver la newrm ms). split.
        - left. apply plus_one. eapply nd_exec_Framestate_deopt. econstructor; eauto.
          rewrite base_version_unchanged. eauto.
        - apply refl_match; auto. apply app_match; auto.
        - simpl. auto. }
          
    +                           (* final_match *) 
      inv STEP. inv STEP0.
Qed.
