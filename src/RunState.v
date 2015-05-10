Require Import Io.All.

Import C.Notations.

Module Command.
  Inductive t :=
  | Get
  | Store (n : nat)
  | Read.

  Definition answer (c : t) : Type :=
    match c with
    | Get => nat
    | Store _ => unit
    | Read => list nat
    end.
End Command.

Definition E : Effect.t :=
  Effect.New Command.t Command.answer.

Definition get : C.t E nat :=
  C.Call (E := E) Command.Get.

Definition store (n : nat) : C.t E unit :=
  C.Call (E := E) (Command.Store n).

Definition read : C.t E (list nat) :=
  C.Call (E := E) Command.Read.

Fixpoint program (steps : nat) : C.t E (list nat) :=
  match steps with
  | O => read
  | S steps =>
    let! n := get in
    do! store n in
    program steps
  end.
