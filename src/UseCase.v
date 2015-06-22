(** Formal definition of a use case. *)
Require Import Io.All.

Record t {E : Effect.t} {A : Type} (x : C.t E A) : Type := New {
  parameter : Type;
  result : parameter -> A;
  run : forall p, Run.t x (result p) }.
