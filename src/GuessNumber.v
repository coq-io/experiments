(** A program to guess the number of the user using comparisons. *)
Require Import Io.All.

Import C.Notations.

Module Command.
  Inductive t (A : Type) :=
  | Propose : A -> t A.
  Arguments Propose {A} _.

  Definition answer {A : Type} (c : t A) : Type :=
    match c with
    | Propose _ => comparison
    end.
End Command.

Definition E (A : Type) : Effect.t :=
  Effect.New (Command.t A) Command.answer.

Definition propose {A : Type} (x : A) : C.t (E A) comparison :=
  call (E A) (Command.Propose x).

Fixpoint guess {A} (mean : A -> A -> A) (steps : nat) (min max : A)
  : C.t (E A) (option A) :=
  match steps with
  | O => ret None
  | S steps =>
    let m := mean min max in
    let! answer := propose m in
    match answer with
    | Lt => guess mean steps m max
    | Gt => guess mean steps min m
    | Eq => ret (Some m)
    end
  end.
