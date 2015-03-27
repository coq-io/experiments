Require Import Io.All.

Import C.Notations.

Module Command.
  Inductive t (A : Type) :=
  | Lock (id : A)
  | Unlock (id : A).
End Command.

Definition answer {A : Type} (c : Command.t A) : Type :=
  match c with
  | Command.Lock _ => unit
  | Command.Unlock _ => unit
  end.

Definition effect (A : Type) : Effect.t :=
  Effect.New (Command.t A) answer.
