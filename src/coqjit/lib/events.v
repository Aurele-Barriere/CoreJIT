(* Observable Behaviors of our programs *)
Require Export String.
Require Export List.
Require Export Maps.
Require Export Coqlib.
Require Export values.

(* Right now we only send as debug the fuction optimized *)
Inductive debug_info:Type :=
| DebugOpt : positive -> debug_info
| DebugString : string -> debug_info.

(* No event, some debug information, or some printed value *)
Inductive event:Type :=
| Debug: debug_info -> event
| Valprint: value -> event
| Stringprint: string -> event
| Loud_Deopt : event                 (* used for the loud semantics *)
| Loud_Go_on : event.

(* Traces *)
Definition trace:Type := list event.
Definition E0:trace := nil.

(* Silent traces. Debug information is also silent: not part of the output *)
Inductive silent: trace -> Prop :=
| silent_E0: silent E0
| silent_debug: forall s t, silent t -> silent ((Debug s)::t).

(* The rest comes from the CompCert Events file *)
Definition Eapp (t1 t2: trace) : trace := t1 ++ t2.

CoInductive traceinf : Type :=
  | Econsinf: event -> traceinf -> traceinf.

Fixpoint Eappinf (t: trace) (T: traceinf) {struct t} : traceinf :=
  match t with
  | nil => T
  | ev :: t' => Econsinf ev (Eappinf t' T)
  end.

(** Concatenation of traces is written [**] in the finite case
  or [***] in the infinite case. *)

Infix "**" := Eapp (at level 60, right associativity).
Infix "***" := Eappinf (at level 60, right associativity).

Lemma E0_left: forall t, E0 ** t = t.
Proof. auto. Qed.

Lemma E0_right: forall t, t ** E0 = t.
Proof. intros. unfold E0, Eapp. rewrite <- app_nil_end. auto. Qed.

Lemma Eapp_assoc: forall t1 t2 t3, (t1 ** t2) ** t3 = t1 ** (t2 ** t3).
Proof. intros. unfold Eapp, trace. apply app_ass. Qed.

Lemma Eapp_E0_inv: forall t1 t2, t1 ** t2 = E0 -> t1 = E0 /\ t2 = E0.
Proof (@app_eq_nil event).

Lemma E0_left_inf: forall T, E0 *** T = T.
Proof. auto. Qed.

Lemma Eappinf_assoc: forall t1 t2 T, (t1 ** t2) *** T = t1 *** (t2 *** T).
Proof.
  induction t1; intros; simpl. auto. decEq; auto.
Qed.

Hint Rewrite E0_left E0_right Eapp_assoc
             E0_left_inf Eappinf_assoc: trace_rewrite.

Opaque trace E0 Eapp Eappinf.

(** The following [traceEq] tactic proves equalities between traces
  or infinite traces. *)

Ltac substTraceHyp :=
  match goal with
  | [ H: (@eq trace ?x ?y) |- _ ] =>
       subst x || clear H
  end.

Ltac decomposeTraceEq :=
  match goal with
  | [ |- (_ ** _) = (_ ** _) ] =>
      apply (f_equal2 Eapp); auto; decomposeTraceEq
  | _ =>
      auto
  end.

Ltac traceEq :=
  repeat substTraceHyp; autorewrite with trace_rewrite; decomposeTraceEq.

(** Bisimilarity between infinite traces. *)

CoInductive traceinf_sim: traceinf -> traceinf -> Prop :=
  | traceinf_sim_cons: forall e T1 T2,
      traceinf_sim T1 T2 ->
      traceinf_sim (Econsinf e T1) (Econsinf e T2).

Lemma traceinf_sim_refl:
  forall T, traceinf_sim T T.
Proof.
  cofix COINDHYP; intros.
  destruct T. constructor. apply COINDHYP.
Qed.

Lemma traceinf_sim_sym:
  forall T1 T2, traceinf_sim T1 T2 -> traceinf_sim T2 T1.
Proof.
  cofix COINDHYP; intros. inv H; constructor; auto.
Qed.

Lemma traceinf_sim_trans:
  forall T1 T2 T3,
  traceinf_sim T1 T2 -> traceinf_sim T2 T3 -> traceinf_sim T1 T3.
Proof.
  cofix COINDHYP;intros. inv H; inv H0; constructor; eauto.
Qed.

CoInductive traceinf_sim': traceinf -> traceinf -> Prop :=
  | traceinf_sim'_cons: forall t T1 T2,
      t <> E0 -> traceinf_sim' T1 T2 -> traceinf_sim' (t *** T1) (t *** T2).

Lemma traceinf_sim'_sim:
  forall T1 T2, traceinf_sim' T1 T2 -> traceinf_sim T1 T2.
Proof.
  cofix COINDHYP; intros. inv H.
  destruct t. elim H0; auto.
Transparent Eappinf.
Transparent E0.
  simpl.
  destruct t. simpl. constructor. apply COINDHYP; auto.
  constructor. apply COINDHYP.
  constructor. unfold E0; congruence. auto.
Qed.

(** An alternate presentation of infinite traces as
  infinite concatenations of nonempty finite traces. *)

CoInductive traceinf': Type :=
  | Econsinf': forall (t: trace) (T: traceinf'), t <> E0 -> traceinf'.

Program Definition split_traceinf' (t: trace) (T: traceinf') (NE: t <> E0): event * traceinf' :=
  match t with
  | nil => _
  | e :: nil => (e, T)
  | e :: t' => (e, Econsinf' t' T _)
  end.
Next Obligation.
  elimtype False. elim NE. auto.
Qed.
Next Obligation.
  red; intro. elim (H e). rewrite H0. auto.
Qed.

CoFixpoint traceinf_of_traceinf' (T': traceinf') : traceinf :=
  match T' with
  | Econsinf' t T'' NOTEMPTY =>
      let (e, tl) := split_traceinf' t T'' NOTEMPTY in
      Econsinf e (traceinf_of_traceinf' tl)
  end.

Remark unroll_traceinf':
  forall T, T = match T with Econsinf' t T' NE => Econsinf' t T' NE end.
Proof.
  intros. destruct T; auto.
Qed.

Remark unroll_traceinf:
  forall T, T = match T with Econsinf t T' => Econsinf t T' end.
Proof.
  intros. destruct T; auto.
Qed.

Lemma traceinf_traceinf'_app:
  forall t T NE,
  traceinf_of_traceinf' (Econsinf' t T NE) = t *** traceinf_of_traceinf' T.
Proof.
  induction t.
  intros. elim NE. auto.
  intros. simpl.
  rewrite (unroll_traceinf (traceinf_of_traceinf' (Econsinf' (a :: t) T NE))).
  simpl. destruct t. auto.
Transparent Eappinf.
  simpl. f_equal. apply IHt.
Qed.

(** Prefixes of traces. *)

Definition trace_prefix (t1 t2: trace) :=
  exists t3, t2 = t1 ** t3.

Definition traceinf_prefix (t1: trace) (T2: traceinf) :=
  exists T3, T2 = t1 *** T3.

Lemma trace_prefix_app:
  forall t1 t2 t,
  trace_prefix t1 t2 ->
  trace_prefix (t ** t1) (t ** t2).
Proof.
  intros. destruct H as [t3 EQ]. exists t3. traceEq.
Qed.

Lemma traceinf_prefix_app:
  forall t1 T2 t,
  traceinf_prefix t1 T2 ->
  traceinf_prefix (t ** t1) (t *** T2).
Proof.
  intros. destruct H as [T3 EQ]. exists T3. subst T2. traceEq.
Qed.

(* match_traces *)
(* without external worlds, this is just equality *)
(* to allow determinacy, you would need another definition *)
(* This should correspond to traces of single transitions -> from CompCert *)
(* This only used for the fwd to bwd proof, for loud semantics *)
Inductive match_traces: trace -> trace -> Prop :=
| match_traces_E0:
    match_traces nil nil
| match_traces_same:
    forall e,
      match_traces (e::nil) (e::nil)
| match_traces_loud:
    match_traces (Loud_Go_on::nil) (Loud_Deopt::nil)
| match_traces_loud2:
    match_traces (Loud_Deopt::nil) (Loud_Go_on::nil).


(** An output trace is a trace composed only of output events,
  that is, events that do not take any result from the outside world. *)

Definition output_event (ev: event) : Prop :=
  match ev with
  | Valprint _ => True
  | Stringprint _ => True
  | Debug _ => True
  | Loud_Deopt => True
  | Loud_Go_on => True
  end.

Fixpoint output_trace (t: trace) : Prop :=
  match t with
  | nil => True
  | ev :: t' => output_event ev /\ output_trace t'
  end.
