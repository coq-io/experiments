Require Import Io.All.

Import C.Notations.

Module Command.
  Inductive t (L : Type) :=
  | Lock (l : L)
  | Unlock (l : L).
  Arguments Lock {L} _.
  Arguments Unlock {L} _.
End Command.

Definition answer {L : Type} (c : Command.t L) : Type :=
  match c with
  | Command.Lock _ => unit
  | Command.Unlock _ => unit
  end.

Definition effect (L : Type) : Effect.t :=
  Effect.New (Command.t L) answer.

Definition lock {L A : Type} (l : L) (x : C.t (effect L) A)
  : C.t (effect L) A :=
  do! call (effect L) (Command.Lock l) in
  let! x := x in
  do! call (effect L) (Command.Unlock l) in
  ret x.

Module LockFree.
  Definition C := C.t (effect bool).
End LockFree.
