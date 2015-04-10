Module Effect.
  Record t := New {
    command : Type;
    answer : command -> Type }.
End Effect.

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

Module Sequential.
  Inductive t (E : Effect.t) : Type :=
  | Ret : t E
  | Call : forall c, (Effect.answer E c -> t E) -> t E.
  Arguments Ret {E}.
  Arguments Call {E} _ _.
End Sequential.

Module Concurrent.
  Inductive t (E : Effect.t) : Type :=
  | Ret : Sequential.t E -> t E
  | Spawn : t E -> Sequential.t E -> t E.
  Arguments Ret {E} _.
  Arguments Spawn {E} _ _.
End Concurrent.
