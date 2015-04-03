(** A small-steps semantics for computations. *)
Require Import Io.All.

Module Small.
  Inductive t {E : Effect.t} : forall {A : Type}, C.t E A -> C.t E A + A -> Prop :=
  | Ret : forall (A : Type) (x : A), t (C.Ret E x) (inr x)
  | Call : forall (c : Effect.command E) (a : Effect.answer E c),
    t (C.Call c) (inr a).
End Small.
