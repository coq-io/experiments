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
    Fixpoint tag {A : Type} (tree : t A) : C.t Counter.effect (t (nat * A)) :=
      match tree with
      | Leaf => ret Leaf
      | Node tree_left x tree_right =>
        let! tree_left := tag tree_left in
        let! i := Counter.read in
        do! Counter.incr in
        let! tree_right := tag tree_right in
        ret (Node tree_left (i, x) tree_right)
      end.
  End Imperative.
End BinaryTree.
