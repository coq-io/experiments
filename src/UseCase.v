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

  Definition reflexive {E A} {x : C.t E A} (u : UseCase.t x) : t u u.
    intro p; exists p.
    apply JMeq_refl.
  Qed.

  Definition transitivity {E A} {x : C.t E A} {u1 u2 u3 : UseCase.t x}
    (H12 : t u1 u2) (H23 : t u2 u3) : t u1 u3.
    intro p1.
    destruct (H12 p1) as [p2 Heq12].
    destruct (H23 p2) as [p3 Heq23].
    exists p3.
    now apply JMeq_trans with (y := run u2 p2).
  Qed.
End Le.
