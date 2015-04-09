(** A small-steps semantics for computations with constraints on the model. *)
Require Import FunctionNinjas.All.
Require Import ErrorHandlers.All.
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

Module Tree.
  Inductive t (A : Type) : Type :=
  | Leaf : A -> t A
  | Node : t A -> t A -> t A.
  Arguments Leaf {A} _.
  Arguments Node {A} _ _.

  Fixpoint map {A B : Type} (f : A -> B) (tree : t A) : t B :=
    match tree with
    | Leaf x => Leaf (f x)
    | Node tree1 tree2 => Node (map f tree1) (map f tree2)
    end.
End Tree.

Module Call.
  Record t {E : Effect.t} {S : Type} (m : Model.t E S) (A : Type) := New {
    c : Effect.command E;
    h : forall s, Model.condition m c s -> A }.
  Arguments New {E S m A} _ _.
  Arguments c {E S m A} _.
  Arguments h {E S m A} _ {s} _.
End Call.

Module M.
  Inductive t {E : Effect.t} {S : Type} (m : Model.t E S) (A : Type) : Type :=
  | Ret : A -> t m A
  | Call : Tree.t (Call.t m (t m A)) -> t m A.
  Arguments Ret {E S m A} _.
  Arguments Call {E S m A} _.

  Fixpoint bind {E : Effect.t} {S : Type} {m : Model.t E S} {A B : Type}
    (x : t m A) (f : A -> t m B) : t m B :=
    let fix binds (tree : Tree.t (Call.t m (t m A)))
      : Tree.t (Call.t m (t m B)) :=
      match tree with
      | Tree.Leaf (Call.New c h) =>
        Tree.Leaf (Call.New c (fun s H => bind (h s H) f))
      | Tree.Node tree1 tree2 => Tree.Node (binds tree1) (binds tree2)
      end in
    match x with
    | Ret x => f x
    | Call tree => Call (binds tree)
    end.

  Definition join {E : Effect.t} {S : Type} {m : Model.t E S} {A B : Type}
    : t m A -> t m B -> t m (A * B) :=
    fix join_left (x : t m A) (y : t m B) {struct x} : t m (A * B) :=
      let fix join_right (y : t m B) {struct y} : t m (A * B) :=
        let fix joins_left (tree : Tree.t (Call.t m (t m A)))
          : Tree.t (Call.t m (t m (A * B))) :=
          match tree with
          | Tree.Leaf (Call.New c h) =>
            Tree.Leaf (Call.New c (fun s H => join_left (h s H) y))
          | Tree.Node tree1 tree2 =>
            Tree.Node (joins_left tree1) (joins_left tree2)
          end in
        let fix joins_right (tree : Tree.t (Call.t m (t m B)))
          : Tree.t (Call.t m (t m (A * B))) :=
          match tree with
          | Tree.Leaf (Call.New c h) =>
            Tree.Leaf (Call.New c (fun s H => join_right (h s H)))
          | Tree.Node tree1 tree2 =>
            Tree.Node (joins_right tree1) (joins_right tree2)
          end in
        match (x, y) with
        | (Ret x, _) => bind y (fun y => Ret (x, y))
        | (_, Ret y) => bind x (fun x => Ret (x, y))
        | (Call tree_x, Call tree_y) =>
          Call (Tree.Node (joins_left tree_x) (joins_right tree_y))
        end in
      let fix joins_left (tree : Tree.t (Call.t m (t m A)))
        : Tree.t (Call.t m (t m (A * B))) :=
        match tree with
        | Tree.Leaf (Call.New c h) =>
          Tree.Leaf (Call.New c (fun s H => join_left (h s H) y))
        | Tree.Node tree1 tree2 =>
          Tree.Node (joins_left tree1) (joins_left tree2)
        end in
      let fix joins_right (tree : Tree.t (Call.t m (t m B)))
        : Tree.t (Call.t m (t m (A * B))) :=
        match tree with
        | Tree.Leaf (Call.New c h) =>
          Tree.Leaf (Call.New c (fun s H => join_right (h s H)))
        | Tree.Node tree1 tree2 =>
          Tree.Node (joins_right tree1) (joins_right tree2)
        end in
      match (x, y) with
      | (Ret x, _) => bind y (fun y => Ret (x, y))
      | (_, Ret y) => bind x (fun x => Ret (x, y))
      | (Call tree_x, Call tree_y) =>
        Call (Tree.Node (joins_left tree_x) (joins_right tree_y))
      end.

  Definition first {E : Effect.t} {S : Type} {m : Model.t E S} {A B : Type}
    (x : t m A) (y : t m B) : t m (A + B).
  Admitted.

  Fixpoint compile {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
    (x : C.t E A) : t m A :=
    match x with
    | C.Ret _ x => Ret x
    | C.Call c =>
      Call (Tree.Leaf (Call.New c (fun _ H => Ret (Model.answer m H))))
    | C.Let _ _ x f => bind (compile x) (fun x => compile (f x))
    | C.Join  _ _ x y => join (compile x) (compile y)
    | C.First  _ _ x y => first (compile x) (compile y)
    end.
End M.

Module ClosedCall.
  Record t {E : Effect.t} {S : Type} (m : Model.t E S) (A : Type) := New {
    c : Effect.command E;
    s : S;
    h : Model.condition m c s -> A }.
  Arguments New {E S m A} _ _ _.
  Arguments c {E S m A} _.
  Arguments s {E S m A} _.
  Arguments h {E S m A} _ _.
End ClosedCall.

(** We link the states. *)
Module ClosedM.
  Inductive t {E : Effect.t} {S : Type} (m : Model.t E S) (A : Type) : Type :=
  | Ret : A -> t m A
  | Call : Tree.t (ClosedCall.t m (t m A)) -> t m A.
  Arguments Ret {E S m A} _.
  Arguments Call {E S m A} _.

  Fixpoint compile {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
    (x : M.t m A) (s : S) : t m A :=
    let fix compiles (tree : Tree.t (Call.t m (M.t m A)))
      : Tree.t (ClosedCall.t m (t m A)) :=
      match tree with
      | Tree.Leaf (Call.New c h) =>
        Tree.Leaf (ClosedCall.New c s (fun H =>
          compile (h s H) (Model.state m H)))
      | Tree.Node tree1 tree2 => Tree.Node (compiles tree1) (compiles tree2)
      end in
    match x with
    | M.Ret x => Ret x
    | M.Call tree => Call (compiles tree)
    end.

  Definition of_C {E : Effect.t} {S : Type} (m : Model.t E S) {A : Type}
    (x : C.t E A) (s : S) : t m A :=
    compile (M.compile x) s.

  Module Tree.
    Module NotStuck.
      Inductive t {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
        : Tree.t (ClosedCall.t m (ClosedM.t m A)) -> Prop :=
      | Leaf : forall c s h, Model.condition m c s ->
        t (Tree.Leaf (ClosedCall.New c s h))
      | NodeLeft : forall tree1 tree2, t tree1 -> t (Tree.Node tree1 tree2)
      | NodeRight : forall tree1 tree2, t tree2 -> t (Tree.Node tree1 tree2).
    End NotStuck.

    Module ForAll.
      Inductive t {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
        (P : ClosedM.t m A -> Prop)
        : Tree.t (ClosedCall.t m (ClosedM.t m A)) -> Prop :=
      | Leaf : forall c s h, (forall H, P (h H)) ->
        t P (Tree.Leaf (ClosedCall.New c s h))
      | Node : forall tree1 tree2, t P tree1 -> t P tree2 ->
        t P (Tree.Node tree1 tree2).
    End ForAll.
  End Tree.
End ClosedM.

Module Progress.
  Inductive t {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
    : ClosedM.t m A -> Prop :=
  | Ret : forall x, t (ClosedM.Ret x)
  | Call : forall tree,
    ClosedM.Tree.NotStuck.t tree -> ClosedM.Tree.ForAll.t t tree ->
    t (ClosedM.Call tree).

  Definition of_C {E : Effect.t} {S : Type} (m : Model.t E S) {A : Type}
    (x : C.t E A) (s : S) : Prop :=
    t (ClosedM.of_C m x s).
End Progress.

(** Try to solve automatically the [Progress.t] predicate. *)
Module Solve.
  Module Tree.
    Fixpoint not_stuck {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
      (dec : forall c s, option (Model.condition m c s))
      (tree : Tree.t (ClosedCall.t m (ClosedM.t m A)))
      : option (ClosedM.Tree.NotStuck.t tree) :=
      match tree with
      | Tree.Leaf (ClosedCall.New c s h) =>
        Option.bind (dec c s) (fun H =>
        Some (ClosedM.Tree.NotStuck.Leaf c s h H))
      | Tree.Node tree1 tree2 =>
        match not_stuck dec tree1 with
        | Some P => Some (ClosedM.Tree.NotStuck.NodeLeft tree1 tree2 P)
        | None =>
          match not_stuck dec tree2 with
          | Some P => Some (ClosedM.Tree.NotStuck.NodeRight tree1 tree2 P)
          | None => None
          end
        end
      end.

    Fixpoint for_all {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
      {P : ClosedM.t m A -> Prop}
      (dec : forall c s (h : Model.condition m c s -> ClosedM.t m A),
        option (forall H, P (h H)))
      (tree : Tree.t (ClosedCall.t m (ClosedM.t m A)))
      : option (ClosedM.Tree.ForAll.t P tree) :=
      match tree with
      | Tree.Leaf (ClosedCall.New c s h) =>
        Option.bind (dec c s h) (fun p =>
        Some (ClosedM.Tree.ForAll.Leaf P c s h p))
      | Tree.Node tree1 tree2 =>
        Option.bind (for_all dec tree1) (fun p1 =>
        Option.bind (for_all dec tree2) (fun p2 =>
        Some (ClosedM.Tree.ForAll.Node P tree1 tree2 p1 p2)))
      end.
  End Tree.

  Fixpoint solve {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
    (dec : forall c s, option (Model.condition m c s)) (x : ClosedM.t m A)
    : Progress.t x + (Effect.command E * S) :=
    match x with
    | ClosedM.Ret x => inl (Progress.Ret x)
    | ClosedM.Call c s h =>
      match dec c s with
      | None => inr (c, s)
      | Some H =>
        Sum.bind (solve dec (h H)) (fun p_h =>
        inl (Progress.Call c s h H p_h))
      end
    | ClosedM.Choose x1 x2 =>
      Sum.bind (solve dec x1) (fun p_x1 =>
      Sum.bind (solve dec x2) (fun p_x2 =>
      inl (Progress.Choose x1 x2 p_x1 p_x2)))
    end.

  Definition is_progress {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
    (dec : forall c s, option (Model.condition m c s)) (x : ClosedM.t m A)
    : bool :=
    match solve dec x with
    | inl _ => true
    | inr _ => false
    end.

  Lemma is_progress_ok {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
    (dec : forall c s, option (Model.condition m c s)) (x : ClosedM.t m A)
    : is_progress dec x = true -> Progress.t x.
    unfold is_progress.
    destruct (solve dec x) as [H |]; congruence.
  Qed.
End Solve.

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

  Definition dec (c : Effect.command E) (s : S) : option (Model.condition m c s).
    destruct c; destruct s;
      try (exact (Some Condition.Lock)); try (exact (Some Condition.Unlock));
      exact None.
  Defined.

  Definition ex1 : C.t E unit :=
    do! lock in
    unlock.

  Compute (M.compile (m := m) ex1).
  Compute (ClosedM.compile (M.compile (m := m) ex1) false).

  (*Lemma ex1_progress : Progress.of_C m ex1 false.
    apply Progress.Call with (H := Condition.Lock); simpl.
    apply Progress.Call with (H := Condition.Unlock); simpl.
    apply Progress.Ret.
  Qed.

  Lemma ex1_auto : Progress.of_C m ex1 false.
    now apply Solve.is_progress_ok with (dec := dec).
  Qed.*)

  Definition ex2 : C.t E (nat * nat) :=
    join (ret 3) (ret 4).

  Compute (M.compile (m := m) ex2).
  Compute (ClosedM.compile (M.compile (m := m) ex2) false).

  (*Lemma ex2_progress : Progress.of_C m ex2 false.
    apply Progress.Ret.
  Qed.

  Lemma ex2_auto : Progress.of_C m ex2 false.
    now apply Solve.is_progress_ok with (dec := dec).
  Qed.*)

  Definition ex3 : C.t E (nat * unit) :=
    join (ret 3) (
      do! lock in
      unlock).

  Compute (M.compile (m := m) ex3).
  Compute (ClosedM.compile (M.compile (m := m) ex3) false).

  (*Lemma ex3_progress : Progress.of_C m ex3 false.
    apply Progress.Call with (H := Condition.Lock); simpl.
    apply Progress.Call with (H := Condition.Unlock); simpl.
    apply Progress.Ret.
  Qed.

  Lemma ex3_auto : Progress.of_C m ex3 false.
    now apply Solve.is_progress_ok with (dec := dec).
  Qed.*)

  Definition ex4 : C.t E (unit * unit) :=
    join (do! lock in unlock) (do! lock in unlock).

  Compute (M.compile (m := m) ex4).
  Compute (ClosedM.compile (M.compile (m := m) ex4) false).

  (*Lemma ex4_auto : Progress.of_C m ex4 false.
    Compute Solve.solve dec (ClosedM.of_C m ex4 false).
    now apply Solve.is_progress_ok with (dec := dec).
  Qed.*)
End Lock.
