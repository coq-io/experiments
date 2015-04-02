Require Import Io.All.

Module C.
  Inductive t (E : Effect.t) : Type -> Type :=
  | Ret : forall (A : Type), A -> t E A
  | Call : forall (A : Type) (c : Effect.command E),
    (Effect.answer E c -> t E A) -> t E A
  | Join : forall (A B C : Type), t E A -> t E B -> (A -> B -> t E C) -> t E C.
  Arguments Ret {E A} _.
  Arguments Call {E A} _ _.
  Arguments Join {E A B C} _ _ _.
End C.
