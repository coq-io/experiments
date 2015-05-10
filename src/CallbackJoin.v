(** Callbacks with a join. But the join is stronger than the let ... *)
Require Import Io.All.

(*Module C.
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

  Fixpoint compile {E : Effect.t} {A B : Type} (x : Io.C.t E A)
    : (A -> t E B) -> t E B :=
    match x with
    | Io.C.Ret _ x => fun k => k x
    | Io.C.Call c => fun k => Call c k
    | Io.C.Let _ _ x f => fun k => compile x (fun x => compile (f x) k)
    | Io.C.Join _ _ x y => fun k =>
      Join (compile x Ret) (compile y Ret) (fun x y => k (x, y))
    | Io.C.First _ _ x y => fun k =>
      First (compile x Ret) (compile y Ret) (fun xy => k xy)
    end.
End C.*)
