(** A small-steps semantics for computations. *)
Require Import Io.All.

Module Small.
  Inductive t {E : Effect.t} : forall {A : Type}, C.t E A -> C.t E A -> Prop :=
  | Call : forall (c : Effect.command E) (a : Effect.answer E c),
    t (C.Call c) (C.Ret _ a)
  | LetLeft : forall (A B : Type) (x : C.t E A) (f : A -> C.t E B)
    (x' : C.t E A), t x x' -> t (C.Let _ _ x f) (C.Let _ _ x' f)
  | Let : forall (A B : Type) (x : C.t E A) (f : A -> C.t E B) (v_x : A),
    t (C.Let _ _ (C.Ret _ v_x) f) (f v_x)
  | JoinLeft : forall (A B : Type) (x : C.t E A) (y : C.t E B) (x' : C.t E A),
    t x x' -> t (C.Join _ _ x y) (C.Join _ _ x' y)
  | JoinRight : forall (A B : Type) (x : C.t E A) (y : C.t E B) (y' : C.t E B),
    t y y' -> t (C.Join _ _ x y) (C.Join _ _ x y')
  | Join : forall (A B : Type) (v_x : A) (v_y : B),
    t (C.Join _ _ (C.Ret _ v_x) (C.Ret _ v_y)) (C.Ret _ (v_x, v_y))
  | FirstLeft : forall (A B : Type) (x : C.t E A) (y : C.t E B) (x' : C.t E A),
    t x x' -> t (C.First _ _ x y) (C.First _ _ x' y)
  | FirstRight : forall (A B : Type) (x : C.t E A) (y : C.t E B) (y' : C.t E B),
    t y y' -> t (C.First _ _ x y) (C.First _ _ x y')
  | FirstInl : forall (A B : Type) (v_x : A) (y : C.t E B),
    t (C.First _ _ (C.Ret _ v_x) y) (C.Ret _ (inl v_x))
  | FirstInr : forall (A B : Type) (x : C.t E A) (v_y : B),
    t (C.First _ _ x (C.Ret _ v_y)) (C.Ret _ (inr v_y)).
End Small.
