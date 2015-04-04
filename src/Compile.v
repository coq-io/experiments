(** Compilation of the join operator. *)
Require Import Coq.Lists.List.

Import ListNotations.

Module Effect.
  Record t := New {
    command : Type;
    answer : command -> Type }.
End Effect.

(** A tree of handlers. *)
Module Handlers.
  Inductive t : list Type -> list Type -> Type :=
  | Ret : forall (G : list Type), t [] G
  | Spawn : forall (G1 G2 : list Type), t [] G1 -> t G1 G2 -> t [] G2
  | Wait : forall (A : Type) (G1 G2 : list Type), (A -> t G1 G2) -> t (A :: G1) G2
  | Answer : forall (G1 : list Type) (A : Type) (G2 : list Type), A -> t [] (G1 ++ A :: G2).

  (*Definition let_ (A B : Type) (x : A) (f : A -> unit) :=
    .*)
End Handlers.
