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

  Fixpoint non_blocking {E : Effect.t} (a : forall c, Effect.answer E c)
    {A : Type} (x : C.t E A)
    : (exists v_x : A, x = C.Ret _ v_x) \/ (exists x' : C.t E A, t x x').
    destruct x as [A v_x | c | A B x f | A B x y | A B x y].
    - left.
      now exists v_x.
    - right.
      exists (C.Ret _ (a c)).
      apply Call.
    - right.
      destruct (non_blocking _ a _ x) as [H | H].
      + destruct H as [v_x H]; rewrite H.
        exists (f v_x).
        now apply Let.
      + destruct H as [x' H].
        exists (C.Let _ _ x' f).
        now apply LetLeft.
    - right.
      destruct (non_blocking _ a _ x) as [H_x | H_x].
      + destruct H_x as [v_x H_x].
        destruct (non_blocking _ a _ y) as [H_y | H_y].
        * destruct H_y as [v_y H_y].
          exists (C.Ret _ (v_x, v_y)).
          rewrite H_x; rewrite H_y.
          apply Join.
        * destruct H_y as [y' H_y].
          exists (C.Join _ _ x y').
          now apply JoinRight.
      + destruct H_x as [x' H_x].
        exists (C.Join _ _ x' y).
        now apply JoinLeft.
    - right.
      destruct (non_blocking _ a _ x) as [H_x | H_x].
      + destruct H_x as [v_x H_x].
        exists (C.Ret _ (inl v_x)).
        rewrite H_x.
        apply FirstInl.
      + destruct H_x as [x' H_x].
        exists (C.First _ _ x' y).
        now apply FirstLeft.
  Qed.
End SmallStep.


Module State.
  Module SmallStep.
    Inductive t {E : Effect.t} {S : Type}
      (answer : forall c, S -> Effect.answer E c)
      (state : Effect.command E -> S -> S) : forall {A : Type},
      C.t E A -> S -> C.t E A -> S -> Prop :=
    | Call : forall (c : Effect.command E) (s : S),
      t answer state (C.Call c) s (C.Ret _ (answer c s)) (state c s)
    | LetLeft : forall (A B : Type) (x : C.t E A) (f : A -> C.t E B)
      (x' : C.t E A) (s s' : S),
      t answer state x s x' s' ->
      t answer state (C.Let _ _ x f) s (C.Let _ _ x' f) s'
    | Let : forall (A B : Type) (x : C.t E A) (f : A -> C.t E B) (v_x : A)
      (s : S),
      t answer state (C.Let _ _ (C.Ret _ v_x) f) s (f v_x) s
    | JoinLeft : forall (A B : Type) (x : C.t E A) (y : C.t E B) (x' : C.t E A)
      (s s' : S),
      t answer state x s x' s' ->
      t answer state (C.Join _ _ x y) s (C.Join _ _ x' y) s'
    | JoinRight : forall (A B : Type) (x : C.t E A) (y : C.t E B) (y' : C.t E B)
      (s s' : S),
      t answer state y s y' s' ->
      t answer state (C.Join _ _ x y) s (C.Join _ _ x y') s'
    | Join : forall (A B : Type) (v_x : A) (v_y : B) (s : S),
      t answer state (C.Join _ _ (C.Ret _ v_x) (C.Ret _ v_y)) s (C.Ret _ (v_x, v_y)) s
    | FirstLeft : forall (A B : Type) (x : C.t E A) (y : C.t E B) (x' : C.t E A)
      (s s' : S),
      t answer state x s x' s' ->
      t answer state (C.First _ _ x y) s (C.First _ _ x' y) s'
    | FirstRight : forall (A B : Type) (x : C.t E A) (y : C.t E B) (y' : C.t E B)
      (s s' : S),
      t answer state y s y' s' ->
      t answer state (C.First _ _ x y) s (C.First _ _ x y') s'
    | FirstInl : forall (A B : Type) (v_x : A) (y : C.t E B) (s : S),
      t answer state (C.First _ _ (C.Ret _ v_x) y) s (C.Ret _ (inl v_x)) s
    | FirstInr : forall (A B : Type) (x : C.t E A) (v_y : B) (s : S),
      t answer state (C.First _ _ x (C.Ret _ v_y)) s (C.Ret _ (inr v_y)) s.
  End SmallStep.
End State.
