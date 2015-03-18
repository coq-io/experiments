Require Import Io.All.

Import C.Notations.

Module Counter.
  Inductive t : Set :=
  | Read
  | Incr.

  Definition answer (command : t) : Type :=
    match command with
    | Read => nat
    | Incr => unit
    end.

  Definition effect : Effects.t := {|
    Effects.command := t;
    Effects.answer := answer |}.

  Definition read : C.t effect nat :=
    call effect Read.

  Definition incr : C.t effect unit :=
    call effect Incr.

  Fixpoint run {A : Type} (n : nat) (x : C.t effect A) : nat * A :=
    match x with
    | C.Ret _ x => (n, x)
    | C.Call Read => (n, n)
    | C.Call Incr => (S n, tt)
    | C.Let _ _ x f =>
      let (n, x) := run n x in
      run n (f x)
    | C.Join _ _ x y =>
      let (n_x, x) := run n x in
      let (n_y, y) := run n y in
      (max n_x n_y, (x, y))
    | C.First _ _ x y =>
      let (n, x) := run n x in
      (n, inl x)
    end.
End Counter.

Module BinaryTree.
  Inductive t (A : Type) : Type :=
  | Leaf : t A
  | Node : A -> t A -> t A -> t A.
  Arguments Leaf [A].
  Arguments Node [A] _ _ _.

  Module Functional.
    Fixpoint tag_aux {A : Type} (i : nat) (tree : t A) : nat * t (nat * A) :=
      match tree with
      | Leaf => (i, Leaf)
      | Node x tree_left tree_right =>
        let (i_left, tree_left) := tag_aux i tree_left in
        let (i_right, tree_right) := tag_aux (i_left + 1) tree_right in
        (i_right, Node (i_left, x) tree_left tree_right)
      end.

    Definition tag {A : Type} (i : nat) (tree : t A) : t (nat * A) :=
      snd (tag_aux i tree).
  End Functional.

  Module Imperative.
    Fixpoint tag_aux {A : Type} (tree : t A) : C.t Counter.effect (t (nat * A)) :=
      match tree with
      | Leaf => ret Leaf
      | Node x tree_left tree_right =>
        let! tree_left := tag_aux tree_left in
        let! i := Counter.read in
        do! Counter.incr in
        let! tree_right := tag_aux tree_right in
        ret (Node (i, x) tree_left tree_right)
      end.

    Definition tag {A : Type} (i : nat) (tree : t A) : t (nat * A) :=
      snd (Counter.run i (tag_aux tree)).
  End Imperative.

  Module Tests.
    Require Import Coq.Strings.String.

    Local Open Scope string.

    Definition input : t string :=
      Node "Fred"
        (Node "Jim" Leaf Leaf)
        (Node "Sheila"
          (Node "Alice" Leaf Leaf)
          (Node "Bob" Leaf Leaf)).

    Definition output : t (nat * string) :=
      Node (2, "Fred")
        (Node (1, "Jim") Leaf Leaf)
        (Node (4, "Sheila")
          (Node (3, "Alice") Leaf Leaf)
          (Node (5, "Bob") Leaf Leaf)).

    Definition functional_ok : Functional.tag 1 input = output :=
      eq_refl.

    Definition imperative_ok : Imperative.tag 1 input = output :=
      eq_refl.
  End Tests.
End BinaryTree.
