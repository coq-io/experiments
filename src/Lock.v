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

(*Module State.
  Definition t (L : Type) := L -> Prop.

  Definition unlock {L : Type} (state : t L) (l : L) : t L :=
    fun l' =>
      l = l' \/ state l'.
End State.

Module LockFree.
  Inductive t {L : Type} (state : State.t L)
    : forall {A : Type}, C.t (effect L) A -> State.t L -> Prop :=
  | Ret : forall {A : Type} (x : A), t state (C.Ret _ x) state
  | CallUnlock : forall (l : L), t state (C.Call (E := effect L) (Command.Unlock l)) (State.unlock state l)
  | CallLock : forall (l : L), state l -> t state (C.Call (E := effect L) (Command.Lock l)) (State.lock state l).
End LockFree.*)

Module Trace.
  Inductive t (L : Type) :=
  | Ret : t L
  | Lock : L -> t L
  | Unlock : L -> t L
  | Let : t L -> t L -> t L
  | Join : t L -> t L -> t L
  | First : t L + t L -> t L.
  Arguments Lock {L} _.
  Arguments Unlock {L} _.
  Arguments Let {L} _ _.
  Arguments Join {L} _ _.
  Arguments First {L} _.

  Fixpoint run {L A : Type} (x : C.t (effect L) A) : C.t (effect L) (A * t L) :=
    match x with
    | C.Ret _ x => ret (x, Ret _)
    | C.Call c =>
      let! a := call (effect L) c in
      let trace :=
        match c with
        | Command.Lock l => Lock l
        | Command.Unlock l => Unlock l
        end in
      ret (a, trace)
    | C.Let _ _ x f =>
      let! x := run x in
      let (x, trace_x) := x in
      let! y := run (f x) in
      let (y, trace_y) := y in
      ret (y, Let trace_x trace_y)
    | C.Join _ _ x y =>
      let! xy := join (run x) (run y) in
      match xy with
      | ((x, trace_x), (y, trace_y)) => ret ((x, y), Join trace_x trace_y)
      end
    | C.First _ _ x y =>
      let! xy := first (run x) (run y) in
      match xy with
      | inl (x, trace_x) => ret (inl x, First (inl trace_x))
      | inr (y, trace_y) => ret (inr y, First (inr trace_y))
      end
    end.
End Trace.

Module Examples.
  Module LockFree.
    Definition C := C.t (effect unit).

    Definition program : C unit :=
      do! lock tt (ret tt) in
      lock tt (ret tt).
  End LockFree.

  Module Locked.
    Definition C := C.t (effect unit).

    Definition program : C unit :=
      lock tt (lock tt (ret tt)).
  End Locked.
End Examples.
