(** A small-steps semantics for computations with constraints on the model. *)
Require Import Coq.Bool.Bool.
Require Import FunctionNinjas.All.
Require Import ErrorHandlers.All.

Module Effect.
  Record t := New {
    command : Type;
    answer : command -> Type }.
End Effect.

Module Model.
  Record t (E : Effect.t) (S : Type) := New {
    condition : Effect.command E -> S -> Prop;
    answer : forall c, S -> Effect.answer E c;
    state : Effect.command E -> S -> S }.
  Arguments New {E S} _ _ _.
  Arguments condition {E S} _ _ _.
  Arguments answer {E S} _ _ _.
  Arguments state {E S} _ _ _.
End Model.

Module C.
  (** The description of a computation. *)
  Inductive t (E : Effect.t) (A : Type) : Type :=
  | Ret : A -> t E A
  | Call : forall c, (Effect.answer E c -> t E A) -> t E A
  | Join : forall {B C : Type}, t E B -> t E C -> (B * C -> t E A) -> t E A.
  Arguments Ret {E A} _.
  Arguments Call {E A} _ _.
  Arguments Join {E A B C} _ _ _.

  Module Step.
    Inductive t {E : Effect.t} {S : Type} (m : Model.t E S) {A : Type}
      : S -> C.t E A -> S -> C.t E A -> Prop :=
    | Call : forall s c h,
      Model.condition m c s ->
      t m s (C.Call c h) (Model.state m c s) (h (Model.answer m c s))
    | JoinLeft : forall s B C (x : C.t E B) (y : C.t E C) h s' x',
      t m (A := B) s x s' x' ->
      t m s (C.Join x y h) s' (C.Join x' y h)
    | JoinRight : forall s B C (x : C.t E B) (y : C.t E C) h s' y',
      t m (A := C) s y s' y' ->
      t m s (C.Join x y h) s' (C.Join x y' h)
    | Join : forall s B C (x : B) (y : C) h,
      t m s (C.Join (C.Ret x) (C.Ret y) h) s (h (x, y)).
  End Step.

  Module Step'.
    Inductive t {E : Effect.t} {S : Type} (m : Model.t E S) {A : Type}
      : S -> C.t E A -> S -> C.t E A -> Prop :=
    | Call : forall s c h,
      Model.condition m c s ->
      t m s (C.Call c h) (Model.state m c s) (h (Model.answer m c s))
    | JoinLeft : forall s B C (x : C.t E B) (y : C.t E C) h s' x',
      t m (A := B) s x s' x' ->
      t m s (C.Join x y h) s' (C.Join x' y h)
    | JoinRight : forall s B C (x : C.t E B) (y : C.t E C) h s' y',
      t m (A := C) s y s' y' ->
      t m s (C.Join x y h) s' (C.Join x y' h)
    | Join : forall s B C (x : B) (y : C) h,
      t m s (C.Join (C.Ret x) (C.Ret y) h) s (h (x, y)).
  End Step'.

  Module NotStuck.
    Inductive t {E : Effect.t} {S : Type} (m : Model.t E S) {A : Type}
      : S -> C.t E A -> Prop :=
    | Value : forall s x, t m s (C.Ret x)
    | Step : forall s x s' x', Step.t m s x s' x' -> t m s x.

    Fixpoint is_not_stuck {E : Effect.t} {S : Type} (m : Model.t E S) {A : Type}
      (dec : forall c s, option (Model.condition m c s)) (s : S) (x : C.t E A)
      : option (t m s x) :=
      match x with
      | Ret x => Some (Value m s x)
      | Call c h =>
        Option.bind (dec c s) (fun H =>
        Some (Step m s _ _ _ (Step.Call m s c h H)))
      | Join _ _ x y h =>
        Option.bind (is_not_stuck m dec s x) (fun H =>
          )
      end.

    Fixpoint is_not_stuck {E : Effect.t} {S : Type} (m : Model.t E S) {A : Type}
      (dec : Effect.command E -> S -> bool) (s : S) (x : C.t E A) : bool :=
      match x with
      | Ret _ => true
      | Call c h => dec c s
      | Join _ _ x y h => orb (is_not_stuck m dec s x) (is_not_stuck m dec s y)
      end.

    Fixpoint is_not_stuck_ok {E : Effect.t} {S : Type} (m : Model.t E S)
      {A : Type} (dec : Effect.command E -> S -> bool)
      (dec_ok : forall c s, dec c s = true -> Model.condition m c s) (s : S)
      (x : C.t E A) : is_not_stuck m dec s x = true -> t m s x.
      intro H.
      destruct x as [x | c h | B C x y h].
      - apply Value.
      - eapply Step.
        apply Step.Call.
        now apply dec_ok.
      - destruct (orb_prop _ _ H) as [H_x | H_y].
        + destruct (is_not_stuck_ok _ _ m _ dec dec_ok s x H_x).
    Qed.
  End NotStuck.

  Module DeadLockFree.
    Inductive t {E : Effect.t} {S : Type} (m : Model.t E S) {A : Type}
      (s : S) (x : C.t E A) : Prop :=
    | New : NotStuck.t m s x ->
      (forall s' x', Step.t m s x s' x' -> t m s' x') -> t m s x.
  End DeadLockFree.

  (*Module DeadLockFree.
    Inductive t {E : Effect.t} {S : Type} (m : Model.t E S) {A : Type}
      : S -> C.t E A -> Prop :=
    | Ret : forall s x, t m s (C.Ret x)
    | Call : forall s c h,
      (Model.condition m c s ->
        NotStuck.t m (Model.state m c s) (h (Model.answer m c s)) /\
        t m (Model.state m c s) (h (Model.answer m c s))) ->
      t m s (C.Call c h)
    | Join : .
      (s : S) (x : C.t E A) : Prop :=
      forall (x' : C.t E A) (s' : S), Steps.t m x s x' s' -> NotStuck.t m x' s'.
  End DeadLockFree.*)
End C.

Module M.
  Inductive t {E : Effect.t} {S : Type} (m : Model.t E S) (A : Type) : Type :=
  | Ret : A -> t m A
  | Call : Effect.command E -> (S -> t m A) -> t m A
  | Choose : t m A -> t m A -> t m A.
  Arguments Ret {E S m A} _.
  Arguments Call {E S m A} _ _.
  Arguments Choose {E S m A} _ _.

  (** If a computation is not stuck. *)
  Module NotStuck.
    Inductive t {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
      : M.t m A -> S -> Prop :=
    | Ret : forall x s, t (M.Ret x) s
    | Call : forall c h s, Model.condition m c s -> t (M.Call c h) s
    | ChooseLeft : forall x1 x2 s, t x1 s -> t (M.Choose x1 x2) s
    | ChooseRight : forall x1 x2 s, t x2 s -> t (M.Choose x1 x2) s.
  End NotStuck.

  Module DeadLockFree.
    Inductive t {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
      : M.t m A -> S -> Prop :=
    | Ret : forall x s, t (M.Ret x) s
    | Call : forall c h s,
      (Model.condition m c s ->
        let s := Model.state m c s in
        NotStuck.t (h s) s /\ t (h s) s) ->
      t (M.Call c h) s
    | Choose : forall x1 x2 s, t x1 s -> t x2 s -> t (M.Choose x1 x2) s.
  End DeadLockFree.

  Fixpoint bind {E : Effect.t} {S : Type} {m : Model.t E S} {A B : Type}
    (x : t m A) (f : A -> t m B) : t m B :=
    match x with
    | Ret x => f x
    | Call c h => Call c (fun s => bind (h s) f)
    | Choose x1 x2 => Choose (bind x1 f) (bind x2 f)
    end.

  Fixpoint join_aux {E : Effect.t} {S : Type} {m : Model.t E S} {B C : Type}
    (join : S -> t m B -> t m C) (c_x : Effect.command E)
    (y : t m B) (k : B -> t m C) : t m C :=
    match y with
    | Ret y => k y
    | Call c_y h_y =>
      Choose
        (Call c_x (fun s => join s y))
        (Call c_y (fun s => join_aux join c_x (h_y s) k))
    | Choose y1 y2 => Choose (join_aux join c_x y1 k) (join_aux join c_x y2 k)
    end.

  Fixpoint join {E : Effect.t} {S : Type} {m : Model.t E S} {A B C : Type}
    (x : t m A) (y : t m B) (k : A * B -> t m C) : t m C :=
    match x with
    | Ret x => bind y (fun y => k (x, y))
    | Call c_x h_x => join_aux (fun s y => join (h_x s) y k) c_x y (fun y => bind x (fun x => k (x, y)))
    | Choose x1 x2 => Choose (join x1 y k) (join x2 y k)
    end.

  Fixpoint compile {E : Effect.t} {S : Type} (m : Model.t E S) {A B : Type}
    (x : C.t E A) : (A -> t m B) -> t m B :=
    match x with
    | C.Ret _ x => fun k => k x
    | C.Call c => fun k => Call c (fun s => k (Model.answer m c s))
    | C.Let _ _ x f => fun k => compile m x (fun x => compile m (f x) k)
    | C.Join  _ _ x y => fun k => join (compile m x Ret) (compile m y Ret) k
    end.

  Lemma ok {E : Effect.t} {S : Type} (m : Model.t E S) {A : Type} (x : C.t E A)
    (s : S) : DeadLockFree.t (compile m x Ret) s -> C.DeadLockFree.t m x s.
  Qed.
End M.

Module ClosedCall.
  Record t {E : Effect.t} {S : Type} (m : Model.t E S) (T : Type) := New {
    c : Effect.command E;
    s : S;
    h : T }.
  Arguments New {E S m T} _ _ _.
  Arguments c {E S m T} _.
  Arguments s {E S m T} _.
  Arguments h {E S m T} _.
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
        Tree.Leaf (ClosedCall.New c s (compile (h s) (Model.state m c s)))
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
      | Leaf : forall c s h, (Model.condition m c s -> P h) ->
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
      (dec : Effect.command E -> S -> bool)
      (tree : Tree.t (ClosedCall.t m (ClosedM.t m A))) : bool :=
      match tree with
      | Tree.Leaf (ClosedCall.New c s h) => dec c s
      | Tree.Node tree1 tree2 => orb (not_stuck dec tree1) (not_stuck dec tree2)
      end.

    Fixpoint not_stuck_ok {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
      {dec : Effect.command E -> S -> bool}
      (dec_ok : forall c s, dec c s = true -> Model.condition m c s)
      (tree : Tree.t (ClosedCall.t m (ClosedM.t m A)))
      : not_stuck dec tree = true -> ClosedM.Tree.NotStuck.t tree.
      intro H.
      destruct tree as [call | tree1 tree2].
      - destruct call as [c s h].
        apply ClosedM.Tree.NotStuck.Leaf.
        now apply dec_ok.
      - destruct (orb_prop _ _ H).
        + apply ClosedM.Tree.NotStuck.NodeLeft.
          now apply not_stuck_ok with (dec := dec).
        + apply ClosedM.Tree.NotStuck.NodeRight.
          now apply not_stuck_ok with (dec := dec).
    Qed.
  End Tree.

  Fixpoint solve {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
    (dec : Effect.command E -> S -> bool) (x : ClosedM.t m A)
    : option (Tree.t (ClosedCall.t m (ClosedM.t m A))) :=
    let fix for_all (tree : Tree.t (ClosedCall.t m (ClosedM.t m A)))
      : option (Tree.t (ClosedCall.t m (ClosedM.t m A))) :=
      match tree with
      | Tree.Leaf (ClosedCall.New c s h) =>
        if dec c s then
          solve dec h
        else
          None
      | Tree.Node tree1 tree2 =>
        match for_all tree1 with
        | None => for_all tree2
        | Some err => Some err
        end
      end in
    match x with
    | ClosedM.Ret _ => None
    | ClosedM.Call tree =>
      if Tree.not_stuck dec tree then
        for_all tree
      else
        Some tree
    end.

  (*Fixpoint solve_ok {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
    {dec : Effect.command E -> S -> bool}
    (dec_true_ok : forall c s, dec c s = true -> Model.condition m c s)
    (dec_false_ok : forall c s, dec c s = false -> ~ Model.condition m c s)
    (x : ClosedM.t m A) : solve dec x = None -> Progress.t x.
    intro H.
    destruct x as [x | tree].
    - apply Progress.Ret.
    - assert (H_not_stuck : Tree.not_stuck dec tree = true) by (
        case_eq (Tree.not_stuck dec tree); trivial;
        intro Heq; simpl in H; rewrite Heq in H; congruence).
      apply Progress.Call.
      + now apply (Tree.not_stuck_ok dec_true_ok).
      + refine (
          let fix for_all t : Tree.not_stuck dec t = true ->
            ClosedM.Tree.ForAll.t Progress.t t := _ in
          for_all tree H_not_stuck).
        intro H_t_not_stuck.
        destruct t as [call | t1 t2].
        * destruct call as [c s h].
          apply ClosedM.Tree.ForAll.Leaf.
          case_eq (dec c s); intros H_dec H_condition.
          apply solve_ok with (dec := dec); trivial.
          ++ intro.
            apply solve_ok with (dec := dec); trivial.
            apply dec_true_ok.
          
    refine (
      let fix for_all (tree : Tree.t (ClosedCall.t m (ClosedM.t m A)))
        : ClosedM.Tree.ForAll.t Progress.t tree := _ in _).
    - destruct tree as [call | tree1 tree2].
      + destruct call as [c s h].
        apply ClosedM.Tree.ForAll.Leaf.
        case_eq (dec c s); intro H_dec.
        * intro.
          apply solve_ok with (dec := dec); trivial.
          apply dec_true_ok.
    -
  Qed.*)

  Fixpoint solve_ok {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
    {dec : Effect.command E -> S -> bool}
    (dec_true_ok : forall c s, dec c s = true -> Model.condition m c s)
    (dec_false_ok : forall c s, dec c s = false -> ~ Model.condition m c s)
    (x : ClosedM.t m A) : solve dec x = None -> Progress.t x.
  Admitted.

  (*Fixpoint solve {E : Effect.t} {S : Type} {m : Model.t E S} {A : Type}
    (dec : forall c s, option (Model.condition m c s))
    (dec_not : forall c s, option (~ Model.condition m c s))
    (x : ClosedM.t m A)
    : Progress.t x + Tree.t (ClosedCall.t m (ClosedM.t m A)) :=
    let fix for_all (tree : Tree.t (ClosedCall.t m (ClosedM.t m A)))
      : ClosedM.Tree.ForAll.t Progress.t tree + _ :=
      match tree with
      | Tree.Leaf (ClosedCall.New c s h) =>
        match dec_not c s with
        | Some H_not =>
          inl (ClosedM.Tree.ForAll.Leaf Progress.t c s h (fun H =>
            match H_not H with end))
        | None =>
          Sum.bind (solve dec dec_not h) (fun H =>
          inl (ClosedM.Tree.ForAll.Leaf Progress.t c s h (fun _ => H)))
        end
      | Tree.Node tree1 tree2 =>
        Sum.bind (for_all tree1) (fun H1 =>
        Sum.bind (for_all tree2) (fun H2 =>
        inl (ClosedM.Tree.ForAll.Node Progress.t tree1 tree2 H1 H2)))
      end in
    match x with
    | ClosedM.Ret x => inl (Progress.Ret x)
    | ClosedM.Call tree =>
      match Tree.not_stuck dec tree with
      | Some H_not_stuck =>
        Sum.bind (for_all tree) (fun H_for_all =>
        inl (Progress.Call tree H_not_stuck H_for_all))
      | None => inr tree
      end
    end.*)
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

  Definition answer (c : Effect.command E) (s : S) : Effect.answer E c :=
    tt.

  Definition state (c : Effect.command E) (s : S) : S :=
    match c with
    | Command.Lock => true
    | Command.Unlock => false
    end.

  Definition m : Model.t E S :=
    Model.New Condition.t answer state.

  Definition dec (c : Effect.command E) (s : S) : bool :=
    match (c, s) with
    | (Command.Lock, false) | (Command.Unlock, true) => true
    | (Command.Lock, true) | (Command.Unlock, false) => false
    end.

  Definition dec_true_ok (c : Effect.command E) (s : S)
    : dec c s = true -> Model.condition m c s.
  Admitted.

  Definition dec_false_ok (c : Effect.command E) (s : S)
    : dec c s = false -> ~ Model.condition m c s.
  Admitted.

  Lemma solve_ok {A : Type} (x : C.t E A) (s : S)
    : Solve.solve dec (ClosedM.of_C m x s) = None -> Progress.of_C m x s.
    apply Solve.solve_ok.
    - exact dec_true_ok.
    - exact dec_false_ok.
  Qed.

  Definition ex1 : C.t E unit :=
    do! lock in
    unlock.

  (*Compute (M.compile (m := m) ex1).
  Compute (ClosedM.compile (M.compile (m := m) ex1) false).*)

  Lemma ex1_progress : Progress.of_C m ex1 false.
    now apply solve_ok.
  Qed.

  Definition ex2 : C.t E (nat * nat) :=
    join (ret 3) (ret 4).

  (*Compute (M.compile (m := m) ex2).
  Compute (ClosedM.compile (M.compile (m := m) ex2) false).*)

  Lemma ex2_progress : Progress.of_C m ex2 false.
    now apply solve_ok.
  Qed.

  Definition ex3 : C.t E (nat * unit) :=
    join (ret 3) (
      do! lock in
      unlock).

  (*Compute (M.compile (m := m) ex3).
  Compute (ClosedM.compile (M.compile (m := m) ex3) false).*)

  Lemma ex3_progress : Progress.of_C m ex3 false.
    now apply solve_ok.
  Qed.

  Definition ex4 : C.t E (unit * unit) :=
    join (do! lock in unlock) (do! lock in unlock).

  (*Compute (M.compile (m := m) ex4).
  Compute (ClosedM.compile (M.compile (m := m) ex4) false).*)

  Lemma ex4_progress : Progress.of_C m ex4 false.
    now apply solve_ok.
  Qed.

  Fixpoint ex5 (n : nat) : C.t E unit :=
    match n with
    | O => ret tt
    | Datatypes.S n =>
      let! _ : unit * unit := join (do! lock in unlock) (ex5 n) in
      ret tt
    end.

  Lemma ex5_progress_0 : Progress.of_C m (ex5 0) false.
    Time now apply solve_ok.
  Qed.

  Lemma ex5_progress_1 : Progress.of_C m (ex5 1) false.
    Time now apply solve_ok.
  Qed.

  Lemma ex5_progress_2 : Progress.of_C m (ex5 2) false.
    Time now apply solve_ok.
  Qed.

  Lemma ex5_progress_3 : Progress.of_C m (ex5 3) false.
    Time now apply solve_ok.
  Qed.

  Lemma ex5_progress_4 : Progress.of_C m (ex5 4) false.
    Time now apply solve_ok.
  Qed.

  Lemma ex5_progress_5 : Progress.of_C m (ex5 5) false.
    Time now apply solve_ok.
  Qed.

  Lemma ex5_progress_6 : Progress.of_C m (ex5 6) false.
    Time now apply solve_ok.
  Qed.

  Lemma ex5_progress_7 : Progress.of_C m (ex5 7) false.
    Time now apply solve_ok.
  Qed.

  Fixpoint ex6 (n : nat) : C.t E nat :=
    match n with
    | O => ret 0
    | Datatypes.S n' =>
      let! sv : nat * nat :=
        join (ex6 n') (
          do! lock in
          let v := n in
          do! unlock in
          ret v) in
      let (s, v) := sv in
      ret (s + v)
    end.

  Lemma ex6_progress_0 : Progress.of_C m (ex6 0) false.
    Time now apply solve_ok.
  Qed.

  Lemma ex6_progress_1 : Progress.of_C m (ex6 1) false.
    Time now apply solve_ok.
  Qed.

  Lemma ex6_progress_2 : Progress.of_C m (ex6 2) false.
    Time now apply solve_ok.
  Qed.

  Lemma ex6_progress_3 : Progress.of_C m (ex6 3) false.
    Time now apply solve_ok.
  Qed.

  Lemma ex6_progress_4 : Progress.of_C m (ex6 4) false.
    Time now apply solve_ok.
  Qed.

  Lemma ex6_progress_5 : Progress.of_C m (ex6 5) false.
    Time now apply solve_ok.
  Qed.

  Lemma ex6_progress_6 : Progress.of_C m (ex6 6) false.
    Time now apply solve_ok.
  Qed.

  Lemma ex6_progress_7 : Progress.of_C m (ex6 7) false.
    Time now apply solve_ok.
  Qed.
End Lock.
