(** A small-steps semantics for computations with constraints on the model. *)
Require Import Coq.Bool.Bool.
Require Import FunctionNinjas.All.
Require Import ErrorHandlers.All.
Require Import Io.All.

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

Module Step.
  Inductive t {E : Effect.t} {S : Type} (m : Model.t E S)
    : forall {A : Type}, C.t E A -> S -> C.t E A -> S -> Prop :=
  | Call : forall (c : Effect.command E) (s : S),
    Model.condition m c s ->
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

  (** If the condition is always true then the evaluation is non-blocking. *)
  Fixpoint non_blocking {E : Effect.t} {S : Type} (m : Model.t E S)
    (progress : forall c s, Model.condition m c s)
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

(*Module Progress.
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
End Progresses.*)

Module Call.
  Record t {E : Effect.t} {S : Type} (m : Model.t E S) (T : Type) := New {
    c : Effect.command E;
    h : S -> T }.
  Arguments New {E S m T} _ _.
  Arguments c {E S m T} _.
  Arguments h {E S m T} _ _.
End Call.

Module M.
  Inductive t {E : Effect.t} {S : Type} (m : Model.t E S) (A : Type) : Type :=
  | Ret : A -> t m A
  | Call : Effect.command E -> (S -> t m A) -> t m A
  | Choose : t m A -> t m A -> t m A.
  Arguments Ret {E S m A} _.
  Arguments Call {E S m A} _ _.
  Arguments Choose {E S m A} _ _.

  Fixpoint bind {E : Effect.t} {S : Type} {m : Model.t E S} {A B : Type}
    (x : t m A) (f : A -> t m B) : t m B :=
    match x with
    | Ret x => f x
    | Call c h => Call c (fun s => bind (h s) f)
    | Choose x1 x2 => Choose (bind x1 f) (bind x2 f)
    end.

  Fixpoint join_aux {E : Effect.t} {S : Type} {m : Model.t E S} {A B : Type}
    (join : S -> t m B -> t m (A * B)) (c_x : Effect.command E)
    (x : t m A) (y : t m B) : t m (A * B) :=
    match y with
    | Ret y => bind x (fun x => Ret (x, y))
    | Call c_y h_y =>
      Choose
        (Call c_x (fun s => join s y))
        (Call c_y (fun s => join_aux join c_x x (h_y s)))
    | Choose y1 y2 => Choose (join_aux join c_x x y1) (join_aux join c_x x y2)
    end.

  Fixpoint join {E : Effect.t} {S : Type} {m : Model.t E S} {A B : Type}
    (x : t m A) (y : t m B) {struct x} : t m (A * B) :=
    match x with
    | Ret x => bind y (fun y => Ret (x, y))
    | Call c_x h_x =>
      let join s := join (h_x s) in
      match y with
      | Ret y => bind x (fun x => Ret (x, y))
      | Call c_y h_y =>
        Choose
          (Call c_x (fun s => join s y))
          (Call c_y (fun s => join_aux join c_x x (h_y s)))
      | Choose y1 y2 => Choose (join_aux join c_x x y1) (join_aux join c_x x y2)
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
    | C.Call c =>
      Call (Tree.Leaf (Call.New c (fun s => Ret (Model.answer m c s))))
    | C.Let _ _ x f => bind (compile x) (fun x => compile (f x))
    | C.Join  _ _ x y => join (compile x) (compile y)
    | C.First  _ _ x y => first (compile x) (compile y)
    end.
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
