Require Import Io.All.

Module C.
  Inductive t (E : Effect.t) : Type -> Type :=
  | Ret : forall (A : Type), A -> t E A
  | Call : forall (A : Type) (c : Effect.command E),
    (Effect.answer E c -> t E A) -> t E A
  | Join : forall (A B C : Type), t E A -> t E B -> (A -> B -> t E C) -> t E C
  | First : forall (A B C : Type), t E A -> t E B -> (A + B -> t E C) -> t E C.
  Arguments Ret {E A} _.
  Arguments Call {E A} _ _.
  Arguments Join {E A B C} _ _ _.
  Arguments First {E A B C} _ _ _.

  Fixpoint compile {E : Effect.t} {A B : Type} (x : Io.C.t E A) (k : A -> t E B)
    {struct x} : t E B.
    destruct x.
    - exact (k x).
    - exact (Call command k).
    - exact (compile _ _ _ x (fun x => compile _ _ _ (t0 x) k)).
    - exact (Join (compile _ _ _ x1 Ret) (compile _ _ _ x2 Ret) (fun x y => k (x, y))).
    - exact (First (compile _ _ _ x1 Ret) (compile _ _ _ x2 Ret) (fun xy => k xy)).
  Defined.
End C.
