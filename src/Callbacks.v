(** A definition of concurrent programming with a callbacks style. *)

Module Effect.
  Record t := New {
    command : Type;
    answer : command -> Type }.
End Effect.

Module C.
  Inductive t (E : Effect.t) : Type :=
  | Ret : t E
  | Call : forall (c : Effect.command E), (Effect.answer E c -> t E) -> t E
  | Fork : t E -> t E -> t E.
  Arguments Ret {E}.
  Arguments Call {E} _ _.
  Arguments Fork {E} _ _.
End C.

Module DPN.
  Record t (State Action : Type) := New {
    seq_step : State -> Action -> State -> Prop;
    par_step : State -> Action -> State -> State -> Prop }.

  Definition empty {State Action : Type} : t State Action := {|
    seq_step := fun _ _ _ => False;
    par_step := fun _ _ _ _ => False |}.

  Module Action.
    Inductive t (E : Effect.t) :=
    | Call : forall (c : Effect.command E), Effect.answer E c -> t E
    | Fork : t E.
    Arguments Call {E} _ _.
    Arguments Fork {E}.
  End Action.

  Definition call {E : Effect.t} (c : Effect.command E)
    (callback : Effect.answer E c -> C.t E) : t (C.t E) (Action.t E) := {|
    seq_step := fun x action y =>
      exists a : Effect.answer E c,
        x = C.Call c callback /\
        action = Action.Call c a /\
        y = callback a;
    par_step := fun _ _ _ _ => False |}.
End DPN.
