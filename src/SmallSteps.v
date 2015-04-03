(** A small-steps semantics for computations. *)
Require Import Io.All.

Module SmallStep.
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
End SmallStep.

Module NonValue.
  Fixpoint non_blocking {E : Effect.t} (a : forall c, Effect.answer E c)
    {A : Type} (x : C.t E A)
    : (exists v_x : A, x = C.Ret _ v_x) \/
      (exists x' : C.t E A, SmallStep.t x x').
    destruct x as [A v_x | c | A B x f | A B x y | A B x y].
    - left.
      now exists v_x.
    - right.
      exists (C.Ret _ (a c)).
      apply SmallStep.Call.
    - right.
      destruct (non_blocking _ a _ x) as [H | H].
      + destruct H as [v_x H]; rewrite H.
        exists (f v_x).
        now apply SmallStep.Let.
      + destruct H as [x' H].
        exists (C.Let _ _ x' f).
        now apply SmallStep.LetLeft.
    - right.
      destruct (non_blocking _ a _ x) as [H_x | H_x].
      + destruct H_x as [v_x H_x].
        destruct (non_blocking _ a _ y) as [H_y | H_y].
        * destruct H_y as [v_y H_y].
          exists (C.Ret _ (v_x, v_y)).
          rewrite H_x; rewrite H_y.
          apply SmallStep.Join.
        * destruct H_y as [y' H_y].
          exists (C.Join _ _ x y').
          now apply SmallStep.JoinRight.
      + destruct H_x as [x' H_x].
        exists (C.Join _ _ x' y).
        now apply SmallStep.JoinLeft.
    - right.
      destruct (non_blocking _ a _ x) as [H_x | H_x].
      + destruct H_x as [v_x H_x].
        exists (C.Ret _ (inl v_x)).
        rewrite H_x.
        apply SmallStep.FirstInl.
      + destruct H_x as [x' H_x].
        exists (C.First _ _ x' y).
        now apply SmallStep.FirstLeft.
  Qed.
End NonValue.
