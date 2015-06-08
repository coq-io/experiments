Require Import Io.All.

Module Session.
  Inductive t (E : Effect.t) : Type -> Type :=
  | Ret : forall (A : Type), t E A
  | Call : forall (c : Effect.command E), t E (Effect.answer E c)
  | Let : forall (A B : Type), t E A -> (A -> t E B) -> t E B
  | Choose : forall (A : Type), t E A + t E A -> t E A
  | Join : forall (A B : Type), t E A -> t E B -> t E (A * B).
End Session.
