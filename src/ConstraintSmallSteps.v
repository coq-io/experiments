(** A small-steps semantics for computations with constraints on the model. *)
Require Import Io.All.

Import C.Notations.

(*Module Model.
  Record t (E : Effect.t) (S : Type) := New {
    answer : forall c, S -> Effect.answer E c;
    state : Effect.command E -> S -> S;
    invariant : S -> S -> Prop }.
  Arguments New {E S} _ _ _.
  Arguments answer {E S} _ _ _.
  Arguments state {E S} _ _ _.
  Arguments invariant {E S} _ _ _.
End Model.

Module Step.
  Inductive t {E : Effect.t} {S : Type} (m : Model.t E S)
    : forall {A : Type}, C.t E A -> S -> C.t E A -> S -> Prop :=
  | Call : forall (c : Effect.command E) (s : S),
    Model.invariant m s (Model.state m c s) ->
    t m (C.Call c) s (C.Ret _ (Model.answer m c s)) (Model.state m c s)
  | LetLeft : forall (A B : Type) (x : C.t E A) (f : A -> C.t E B)
    (x' : C.t E A) (s s' : S),
    t m x s x' s' ->
    t m (C.Let _ _ x f) s (C.Let _ _ x' f) s'
  | Let : forall (A B : Type) (x : C.t E A) (f : A -> C.t E B) (v_x : A)
    (s : S),
    t m (C.Let _ _ (C.Ret _ v_x) f) s (f v_x) s
  | JoinLeft : forall (A B : Type) (x : C.t E A) (y : C.t E B) (x' : C.t E A)
    (s s' : S),
    t m x s x' s' ->
    t m (C.Join _ _ x y) s (C.Join _ _ x' y) s'
  | JoinRight : forall (A B : Type) (x : C.t E A) (y : C.t E B) (y' : C.t E B)
    (s s' : S),
    t m y s y' s' ->
    t m (C.Join _ _ x y) s (C.Join _ _ x y') s'
  | Join : forall (A B : Type) (v_x : A) (v_y : B) (s : S),
    t m (C.Join _ _ (C.Ret _ v_x) (C.Ret _ v_y)) s (C.Ret _ (v_x, v_y)) s
  | FirstLeft : forall (A B : Type) (x : C.t E A) (y : C.t E B) (x' : C.t E A)
    (s s' : S),
    t m x s x' s' ->
    t m (C.First _ _ x y) s (C.First _ _ x' y) s'
  | FirstRight : forall (A B : Type) (x : C.t E A) (y : C.t E B) (y' : C.t E B)
    (s s' : S),
    t m y s y' s' ->
    t m (C.First _ _ x y) s (C.First _ _ x y') s'
  | FirstInl : forall (A B : Type) (v_x : A) (y : C.t E B) (s : S),
    t m (C.First _ _ (C.Ret _ v_x) y) s (C.Ret _ (inl v_x)) s
  | FirstInr : forall (A B : Type) (x : C.t E A) (v_y : B) (s : S),
    t m (C.First _ _ x (C.Ret _ v_y)) s (C.Ret _ (inr v_y)) s.

  Fixpoint non_blocking {E : Effect.t} {S : Type} (m : Model.t E S)
    (progress : forall c s, Model.invariant m s (Model.state m c s))
    {A : Type} (x : C.t E A) (s : S)
    {struct x} : (exists v_x : A, x = C.Ret _ v_x) \/
      (exists x' : C.t E A, exists s' : S, t m x s x' s').
    destruct x as [A v_x | c | A B x f | A B x y | A B x y].
    - left.
      now exists v_x.
    - right.
      exists (C.Ret _ (Model.answer m c s)).
      exists (Model.state m c s).
      apply Call.
      apply progress.
    - right.
      destruct (non_blocking _ _ m progress _ x s) as [H | H].
      + destruct H as [v_x H]; rewrite H.
        exists (f v_x).
        exists s.
        now apply Let.
      + destruct H as [x' H]; destruct H as [s' H].
        exists (C.Let _ _ x' f).
        exists s'.
        now apply LetLeft.
    - right.
      destruct (non_blocking _ _ m progress _ x s) as [H_x | H_x].
      + destruct H_x as [v_x H_x].
        destruct (non_blocking _ _ m progress _ y s) as [H_y | H_y].
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
      destruct (non_blocking _ _ m progress _ x s) as [H_x | H_x].
      + destruct H_x as [v_x H_x].
        exists (C.Ret _ (inl v_x)).
        exists s.
        rewrite H_x.
        apply FirstInl.
      + destruct H_x as [x' H_x]; destruct H_x as [s' H_x].
        exists (C.First _ _ x' y).
        exists s'.
        now apply FirstLeft.
  Qed.
End Step.

Module Steps.
  Inductive t {E : Effect.t} {S : Type} (m : Model.t E S)
    : forall {A : Type}, C.t E A -> S -> C.t E A -> S -> Prop :=
  | Nil : forall (A : Type) (x : C.t E A) (s : S), t m x s x s
  | Cons : forall (A : Type) (x x' x'': C.t E A) (s s' s'': S),
    Step.t m x s x' s' -> t m x' s' x'' s'' -> t m x s x'' s''.
End Steps.

Module Progress.
  Inductive t {E : Effect.t} {S : Type} (m : Model.t E S) {A : Type}
    : C.t E A -> S -> Prop :=
  | Value : forall (x : A) (s : S), t m (C.Ret _ x) s
  | Step : forall (x x': C.t E A) (s s': S), Step.t m x s x' s' -> t m x s.
End Progress.

Module Progresses.
  Inductive t {E : Effect.t} {S : Type} (m : Model.t E S) {A : Type}
    : C.t E A -> S -> Prop :=
  | Value : forall (x : A) (s : S), t m (C.Ret _ x) s
  | Steps : forall (x x': C.t E A) (s s': S), Step.t m x s x' s' ->
    (forall x' s', Step.t m x s x' s' -> t m x' s') ->
    t m x s.
End Progresses.

Module M.
  Inductive t (S : Type) (A : Type) :=
  | Value : A -> t S A
  | Step : (S -> t S A * S) -> t S A.
  Arguments Value {S A} _.
  Arguments Step {S A} _.

  Definition ret {S A : Type} (x : A) : t S A :=
    Value x.

  Fixpoint bind {S A B : Type} (x : t S A) (f : A -> t S B) : t S B :=
    match x with
    | Value x => f x
    | Step x =>
      Step (fun s =>
        let (x, s) := x s in
        (bind x f, s))
    end.
End M.

Module Joining.
  Inductive t {S A B : Type} : M.t S A -> M.t S B -> M.t S (A * B) -> Prop :=
  | Pure : forall (x : A) (y : B), t (M.Value x) (M.Value y) (M.Value (x, y))
  | Left : forall x s' y z, (forall s, t (x s) y (z s)) ->
    t (M.Step (fun s => (x s, s' s))) y (M.Step (fun s => (z s, s' s)))
  | Right : forall x y s' z, (forall s, t x (y s) (z s)) ->
    t x (M.Step (fun s => (y s, s' s))) (M.Step (fun s => (z s, s' s))).
End Joining.*)

Module Model.
  Record t (E : Effect.t) (S : Type) := New {
    condition : Effect.command E -> S -> Prop;
    answer : forall c s, condition c s -> Effect.answer E c;
    state : forall c s, condition c s -> S }.
  Arguments New {E S} _ _ _.
  Arguments condition {E S} _ _ _.
  Arguments answer {E S} _ {c s} _.
  Arguments state {E S} _ {c s} _.
End Model.

Module M.
  Inductive t {E : Effect.t} {S : Type} (m : Model.t E S) (A : Type) : Type :=
  | Ret : A -> t m A
  | Call : forall (c : Effect.command E),
    (forall s, Model.condition m c s -> t m A) -> t m A
  | Choose : t m A -> t m A -> t m A.
  Arguments Ret {E S m A} _.
  Arguments Call {E S m A} _ _.
  Arguments Choose {E S m A} _ _.

  Fixpoint bind {E : Effect.t} {S : Type} {m : Model.t E S} {A B : Type}
    (x : t m A) (f : A -> t m B) : t m B :=
    match x with
    | Ret x => f x
    | Call c h => Call c (fun s H => bind (h s H) f)
    | Choose x1 x2 => Choose (bind x1 f) (bind x2 f)
    end.

  Fixpoint join {E : Effect.t} {S : Type} {m : Model.t E S} {A B : Type}
    (x : t m A) (y : t m B) {struct x} : t m (A * B) :=
    let fix join_aux (y : t m B) {struct y} : t m (A * B) :=
      match y with
      | Ret y => bind x (fun x => Ret (x, y))
      | Call c_y h_y =>
        match x with
        | Ret x => bind y (fun y => Ret (x, y))
        | Call c_x h_x =>
          Choose
          (Call c_x (fun s H => join (h_x s H) y))
          (Call c_y (fun s H => join_aux (h_y s H)))
        | Choose x1 x2 => Choose (join x1 y) (join x1 y)
        end
      | Choose y1 y2 => Choose (join_aux y1) (join_aux y2)
      end in
    match x with
    | Ret x => bind y (fun y => Ret (x, y))
    | Call c_x h_x =>
      match y with
      | Ret y => bind x (fun x => Ret (x, y))
      | Call c_y h_y =>
        Choose
        (Call c_x (fun s H => join (h_x s H) y))
        (Call c_y (fun s H => join_aux (h_y s H)))
      | Choose y1 y2 => Choose (join_aux y1) (join_aux y2)
      end
    | Choose x1 x2 => Choose (join x1 y) (join x2 y)
    end.

  Definition first {E : Effect.t} {S : Type} {m : Model.t E S} {A B : Type}
    (x : t m A) (y : t m B) : t m (A + B).
  Admitted.

  Fixpoint compile {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
    (x : C.t E A) : t m A :=
    match x with
    | C.Ret _ x => Ret x
    | C.Call c => Call c (fun _ H => Ret (Model.answer m H))
    | C.Let _ _ x f => bind (compile x) (fun x => compile (f x))
    | C.Join  _ _ x y => join (compile x) (compile y)
    | C.First  _ _ x y => first (compile x) (compile y)
    end.
End M.

Module ClosedM.
  Inductive t {E : Effect.t} {S : Type} (m : Model.t E S) (A : Type) : Type :=
  | Ret : A -> t m A
  | Call : forall (c : Effect.command E) (s : S),
    (Model.condition m c s -> t m A) -> t m A
  | Choose : t m A -> t m A -> t m A.
  Arguments Ret {E S m A} _.
  Arguments Call {E S m A} _ _ _.
  Arguments Choose {E S m A} _ _.

  Fixpoint compile {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
    (x : M.t m A) (s : S) : t m A :=
    match x with
    | M.Ret x => Ret x
    | M.Call c h => Call c s (fun H => compile (h s H) (Model.state m H))
    | M.Choose x1 x2 => Choose (compile x1 s) (compile x2 s)
    end.
End ClosedM.

Module Progress.
  Inductive t {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
    : ClosedM.t m A -> Prop :=
  | Ret : forall x, t (ClosedM.Ret x)
  | Call : forall c s h H, t (h H) -> t (ClosedM.Call c s h)
  | Choose : forall x1 x2, t x1 -> t x2 -> t (ClosedM.Choose x1 x2).

  Definition of_C {E : Effect.t} {S : Type} (m : Model.t E S) {A : Type}
    (x : C.t E A) (s : S) : Prop :=
    t (ClosedM.compile (M.compile (m := m) x) s).
End Progress.

Module Lock.
  Definition S := bool.

  Module Command.
    Inductive t :=
    | Lock
    | Unlock.
  End Command.

  Definition E : Effect.t :=
    Effect.New Command.t (fun _ => unit).

  Definition lock : C.t E unit :=
    call E Command.Lock.

  Definition unlock : C.t E unit :=
    call E Command.Unlock.

  Module Condition.
    Inductive t : Effect.command E -> S -> Prop :=
    | Lock : t Command.Lock false
    | Unlock : t Command.Unlock true.
  End Condition.

  Definition answer (c : Effect.command E) (s : S) (H : Condition.t c s)
    : Effect.answer E c :=
    tt.

  Definition state (c : Effect.command E) (s : S) (H : Condition.t c s) : S :=
    match c with
    | Command.Lock => true
    | Command.Unlock => false
    end.

  Definition m : Model.t E S :=
    Model.New Condition.t answer state.

  Definition ex1 : C.t E unit :=
    do! lock in
    unlock.

  Compute (M.compile (m := m) ex1).
  Compute (ClosedM.compile (M.compile (m := m) ex1) false).

  Lemma ex1_progress : Progress.of_C m ex1 false.
    apply Progress.Call with (H := Condition.Lock); simpl.
    apply Progress.Call with (H := Condition.Unlock); simpl.
    apply Progress.Ret.
  Qed.
End Lock.
