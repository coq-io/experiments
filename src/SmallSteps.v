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
  | ChooseLeft : forall (A : Type) (x : C.t E A) (y : C.t E A) (x' : C.t E A),
    t x x' -> t (C.Choose _ x y) (C.Choose _ x' y)
  | ChooseRight : forall (A : Type) (x : C.t E A) (y : C.t E A) (y' : C.t E A),
    t y y' -> t (C.Choose _ x y) (C.Choose _ x y')
  | ChooseInl : forall (A : Type) (v_x : A) (y : C.t E A),
    t (C.Choose _ (C.Ret _ v_x) y) (C.Ret _ v_x)
  | ChooseInr : forall (A : Type) (x : C.t E A) (v_y : A),
    t (C.Choose _ x (C.Ret _ v_y)) (C.Ret _ v_y).

  (*Fixpoint non_blocking {E : Effect.t} (a : forall c, Effect.answer E c)
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
        apply ChooseInl.
      + destruct H_x as [x' H_x].
        exists (C.Choose _ x' y).
        now apply ChooseLeft.
  Qed.*)
End SmallStep.

Module StateSmallStep.
  Inductive t {E : Effect.t} {S : Type}
    (answer : forall c, S -> Effect.answer E c)
    (state : Effect.command E -> S -> S)
    : forall {A : Type}, C.t E A -> S -> C.t E A -> S -> Prop :=
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
  | ChooseLeft : forall (A : Type) (x : C.t E A) (y : C.t E A) (x' : C.t E A)
    (s s' : S),
    t answer state x s x' s' ->
    t answer state (C.Choose _ x y) s (C.Choose _ x' y) s'
  | ChooseRight : forall (A : Type) (x : C.t E A) (y : C.t E A) (y' : C.t E A)
    (s s' : S),
    t answer state y s y' s' ->
    t answer state (C.Choose _ x y) s (C.Choose _ x y') s'
  | ChooseInl : forall (A : Type) (v_x : A) (y : C.t E A) (s : S),
    t answer state (C.Choose _ (C.Ret _ v_x) y) s (C.Ret _ v_x) s
  | ChooseInr : forall (A : Type) (x : C.t E A) (v_y : A) (s : S),
    t answer state (C.Choose _ x (C.Ret _ v_y)) s (C.Ret _ v_y) s.

  (*Fixpoint non_blocking {E : Effect.t} {S : Type}
    (answer : forall c, S -> Effect.answer E c)
    (state : Effect.command E -> S -> S) {A : Type} (x : C.t E A) (s : S)
    {struct x} : (exists v_x : A, x = C.Ret _ v_x) \/
      (exists x' : C.t E A, exists s' : S, t answer state x s x' s').
    destruct x as [A v_x | c | A B x f | A B x y | A B x y].
    - left.
      now exists v_x.
    - right.
      exists (C.Ret _ (answer c s)).
      exists (state c s).
      apply Call.
    - right.
      destruct (non_blocking _ _ answer state _ x s) as [H | H].
      + destruct H as [v_x H]; rewrite H.
        exists (f v_x).
        exists s.
        now apply Let.
      + destruct H as [x' H]; destruct H as [s' H].
        exists (C.Let _ _ x' f).
        exists s'.
        now apply LetLeft.
    - right.
      destruct (non_blocking _ _ answer state _ x s) as [H_x | H_x].
      + destruct H_x as [v_x H_x].
        destruct (non_blocking _ _ answer state _ y s) as [H_y | H_y].
        * destruct H_y as [v_y H_y].
          exists (C.Ret _ (v_x, v_y)).
          exists s.
          rewrite H_x; rewrite H_y.
          apply Join.
        * destruct H_y as [y' H_y]; destruct H_y as [s' H_y].
          exists (C.Join _ _ x y').
          exists s'.
          now apply JoinRight.
      + destruct H_x as [x' H_x]; destruct H_x as [s' H_x].
        exists (C.Join _ _ x' y).
        exists s'.
        now apply JoinLeft.
    - right.
      destruct (non_blocking _ _ answer state _ x s) as [H_x | H_x].
      + destruct H_x as [v_x H_x].
        exists (C.Ret _ (inl v_x)).
        exists s.
        rewrite H_x.
        apply ChooseInl.
      + destruct H_x as [x' H_x]; destruct H_x as [s' H_x].
        exists (C.Choose _ x' y).
        exists s'.
        now apply ChooseLeft.
  Qed.*)
End StateSmallStep.
