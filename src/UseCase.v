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
  Definition t {E A} (x : C.t E A) (u1 u2 : t x) : Prop :=
    forall (p1 : parameter u1), exists (p2 : parameter u2),
      JMeq (run u1 p1) (run u2 p2).
End Le.
