(** Formal definition of a use case. *)
Require Import Coq.Logic.JMeq.
Require Import Io.All.

Record t {E : Effect.t} {A : Type} (x : C.t E A) : Type := New {
  parameter : Type;
  result : parameter -> A;
  run : forall p, Run.t x (result p) }.
Arguments New {E A x} _ _ _.
Arguments parameter {E A x} _.
Arguments result {E A x} _ _.
Arguments run {E A x} _ _.

Module Le.
  Definition t {E A} {x : C.t E A} (u1 u2 : UseCase.t x) : Prop :=
    forall (p1 : parameter u1), exists (p2 : parameter u2),
      JMeq (run u1 p1) (run u2 p2).

  Lemma reflexive {E A} {x : C.t E A} (u : UseCase.t x) : t u u.
    intro p; exists p.
    apply JMeq_refl.
  Qed.

  Lemma transitivity {E A} {x : C.t E A} {u1 u2 u3 : UseCase.t x}
    (H12 : t u1 u2) (H23 : t u2 u3) : t u1 u3.
    intro p1.
    destruct (H12 p1) as [p2 Heq12].
    destruct (H23 p2) as [p3 Heq23].
    exists p3.
    now apply JMeq_trans with (y := run u2 p2).
  Qed.
End Le.

Module Eq.
  Definition t {E A} {x : C.t E A} (u1 u2 : UseCase.t x) : Prop :=
    Le.t u1 u2 /\ Le.t u2 u1.
End Eq.

Module Join.
  Definition t {E A} {x : C.t E A} (u1 u2 : UseCase.t x) : UseCase.t x := {|
    parameter := parameter u1 + parameter u2;
    result := fun p =>
      match p with
      | inl p1 => result u1 p1
      | inr p2 => result u2 p2
      end;
    run := fun p =>
      match p with
      | inl p1 => run u1 p1
      | inr p2 => run u2 p2
      end |}.

  Lemma le_left {E A} {x : C.t E A} (u1 u2 : UseCase.t x)
    : Le.t u1 (t u1 u2).
    intro p1; exists (inl p1).
    apply JMeq_refl.
  Qed.

  Lemma le_right {E A} {x : C.t E A} (u1 u2 : UseCase.t x)
    : Le.t u2 (t u1 u2).
    intro p2; exists (inr p2).
    apply JMeq_refl.
  Qed.

  Lemma smallest {E A} {x : C.t E A} (u1 u2 u3 : UseCase.t x)
    (H1 : Le.t u1 u3) (H2 : Le.t u2 u3) : Le.t (t u1 u2) u3.
    intro p.
    destruct p as [p1 | p2].
    - destruct (H1 p1) as [p3 H1'].
      now exists p3.
    - destruct (H2 p2) as [p3 H2'].
      now exists p3.
  Qed.
End Join.

Module Bottom.
  Definition bottom {E A} (x : C.t E A) : UseCase.t x := {|
    parameter := Empty_set;
    result := fun p => match p with end;
    run := fun p => match p with end |}.

  Lemma smallest {E A} {x : C.t E A} (u : UseCase.t x) : Le.t (bottom x) u.
    intro p.
    destruct p.
  Qed.
End Bottom.
