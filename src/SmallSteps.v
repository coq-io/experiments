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
  Inductive t {E : Effect.t} : forall {A : Type}, C.t E A -> Prop :=
  | Call : forall (c : Effect.command E) (a : Effect.answer E c), t (C.Call c)
  | Let : forall (A B : Type) (x : C.t E A) (f : A -> C.t E B),
    t (C.Let _ _ x f)
  | Join : forall (A B : Type) (x : C.t E A) (y : C.t E B), t (C.Join _ _ x y)
  | First : forall (A B : Type) (x : C.t E A) (y : C.t E B),
    t (C.First _ _ x y).

  Lemma non_value_or_value {E : Effect.t} {A : Type} (x : C.t E A)
    : t x \/ exists v_x : A, x = C.Ret _ v_x.
  Admitted.

  Fixpoint non_blocking {E : Effect.t} {A : Type} {x : C.t E A} (H : t x)
    {struct H} : exists x' : C.t E A, SmallStep.t x x'.
    destruct H.
    - exists (C.Ret _ a).
      apply SmallStep.Call.
    - destruct (non_value_or_value x) as [H | H].
      + destruct (non_blocking _ _ _ H) as [x' H'].
        exists (C.Let _ _ x' f).
        now apply SmallStep.LetLeft.
      + destruct H as [v_x H].
        exists (f v_x).
        rewrite H.
        now apply SmallStep.Let.
    - destruct (non_value_or_value x) as [H_x | H_x].
      + destruct (non_blocking _ _ _ H_x) as [x' H'].
        exists (C.Join _ _ x' y).
        now apply SmallStep.JoinLeft.
      + destruct (non_value_or_value y) as [H_y | H_y].
        * destruct (non_blocking _ _ _ H_y) as [y' H'].
          exists (C.Join _ _ x y').
          now apply SmallStep.JoinRight.
        * destruct H_x as [v_x H_x]; destruct H_y as [v_y H_y].
          rewrite H_x; rewrite H_y.
          exists (C.Ret _ (v_x, v_y)).
          apply SmallStep.Join.
    - destruct (non_value_or_value x) as [H_x | H_x].
      + destruct (non_blocking _ _ _ H_x) as [x' H'].
        exists (C.First _ _ x' y).
        now apply SmallStep.FirstLeft.
      + destruct H_x as [v_x H_x].
        rewrite H_x.
        exists (C.Ret _ (inl v_x)).
        apply SmallStep.FirstInl.
  Qed.
End NonValue.
