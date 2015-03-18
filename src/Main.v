Require Import Io.All.

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
End Counter.

Module BinaryTree.
  Inductive t (A : Type) : Type :=
  | Leaf : t A
  | Node : t A -> A -> t A -> t A.
  Arguments Leaf [A].
  Arguments Node [A] _ _ _.

  Module Functional.
    Fixpoint tag_aux {A : Type} (i : nat) (tree : t A) : nat * t (nat * A) :=
      match tree with
      | Leaf => (i, Leaf)
      | Node tree_left x tree_right =>
        let (i_left, tree_left) := tag_aux i tree_left in
        let (i_right, tree_right) := tag_aux (i_left + 1) tree_right in
        (i_right, Node tree_left (i_left, x) tree_right)
      end.

    Definition tag {A : Type} (i : nat) (tree : t A) : t (nat * A) :=
      snd (tag_aux i tree).
  End Functional.

  Module Imperative.
  End Imperative.
End BinaryTree.
