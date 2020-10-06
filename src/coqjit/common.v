(* Common definitions for the JIT compiler *)

Require Export Coqlib.
Require Export String.
Require Export Maps.

(* Notations for maps *)
Notation "a # b" := (PTree.get b a) (at level 1).
Notation "a # b <- c" := (PTree.set b c a) (at level 1, b at next level).

(* Some functions can return an error. These functions return something of type [res A], *)
(* either a value of type [A], or an error *)
Inductive res (A:Type): Type :=
| OK: A -> res A
| Error: string -> res A.

Arguments OK [A].
Arguments Error [A].

(* To perform [f] on a value of type [res A] *)
Definition bind {A B: Type} (v: res A) (f: A -> res B): res B :=
  match v with
  | Error s => Error s
  | OK v => f v
  end.

(* perform [f] on a type [res(A*B)]  *)
Definition bind2 {A B C: Type} (v: res (A * B)) (f: A -> B -> res C) : res C :=
  bind v (fun xy => f (fst xy) (snd xy)).

Definition bind3 {A B C D: Type} (v: res (A * B * C)) (f: A -> B -> C -> res D) : res D :=
  bind v (fun xyz => f (fst (fst xyz)) (snd(fst xyz)) (snd(xyz))).

Definition bind4 {A B C D E: Type} (v: res (A * B * C * D)) (f: A -> B -> C -> D -> res E) : res E :=
  bind v (fun abcd => f (fst (fst (fst abcd))) (snd (fst (fst abcd))) (snd (fst abcd)) (snd abcd)).


Notation "'do' X <- A ; B" := (bind A (fun X => B))
                                (at level 200, X ident, A at level 100, B at level 200).
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200).
Notation "'do' ( X , Y , Z ) <- A ; B" := (bind3 A (fun X Y Z => B))
   (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200).
Notation "'do' ( W , X , Y , Z ) <- A ; B" := (bind4 A (fun W X Y Z => B))
   (at level 200, W ident, X ident, Y ident, Z ident, A at level 100, B at level 200).


(* Some functions return an option. *)
(* [try_op v s] returns the corresponding [OK], or fails with [Error s] *)
Definition try_op {A:Type} (o:option A) (s:string): res A :=
  match o with
  | None => Error s
  | Some v => OK v
  end.

Lemma try_op_rewrite:
  forall A (e:option A) r s,
    try_op e s = OK r -> e = Some r.
Proof.
  intros A e r s H. destruct e; inv H. auto.
Qed.

(* With f a function that transforms x, return (f x) or in case of an error, x unchanged *)
Definition safe_res {A:Type} (f:A -> res A) (x:A) :=
  match f x with
  | Error _ => x
  | OK y => y
  end.

(* A JIT execution is a serie of optimization or execution steps *)
(* jit_status represents these two types of steps *)
Inductive jit_status: Type :=
| Exe                           (* execution *)
| Opt.                          (* optimization *)

(* Tactics to reason about monads *)
Ltac ok_do:=
  match goal with
  | [ H: ?e = OK ?v |- context[?e]] => try rewrite H; simpl
  | [ H: ?e = Some ?v |- context[try_op ?e ?m]] => try rewrite H; simpl
  end.

Ltac do_ok:=
  let HDO := fresh "HDO" in
  match goal with
  | [ H: (do V <- ?e; ?c) = OK ?r |- _ ] => try destruct e eqn:HDO; inv H
  | [ H: (do (A,B) <- ?e; ?c) = OK ?r |- _ ] => try destruct e eqn:HDO; inv H
  | [ H: (do (A,B,C) <- ?e; ?c) = OK ?r |- _ ] => try destruct e eqn:HDO; inv H
  | [ H: try_op ?e ?m = OK ?r |- _ ] => try destruct e eqn:HDO; inv H
  end.

(* Tactics to reason about options *)
Ltac match_some:=
  match goal with
  | [ H: ?e = Some ?i,
      H1: ?e = Some ?ii |- _ ] =>
    try (rewrite H in H1; inv H1)
  end.

Ltac match_ok:=
  match goal with
  | [H: OK ?a = OK ?b |- _ ] =>
    assert(HMATCHOK: a = b) by (inv H; auto); clear H; rename HMATCHOK into H
  end.

(* Destructing on the equality of two ppositives *)
Ltac poseq_destr b1 b2 :=
  let HEQ := fresh "HEQ" in
  destruct (Pos.eqb b1 b2) eqn:HEQ; [apply Pos.eqb_eq in HEQ; subst | apply Pos.eqb_neq in HEQ].

(** * Optimization hints  *)
(* We allow annotations in our program, to help the dynamic optimizer *)
(* A Frontend can use this for instance to guide speculation *)
Parameter hint: Type.
