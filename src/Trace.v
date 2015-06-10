(** A trace defined without the description of a computation, with a property in
    [Prop] to assert correspondance with a computation. *)
Require Import Io.All.

Inductive t (E : Effect.t) : Type -> Type :=
| Ret : forall A, t E A
| Call : forall c, t E (Effect.answer E c)
| Let : forall A B, t E A -> t E B -> t E B
| Choose : forall A, t E A + t E A -> t E A
| Join : forall A B, t E A -> t E B -> t E (A * B).
