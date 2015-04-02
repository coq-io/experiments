(** A definition of concurrent programming with a callbacks style. *)

Module Effect.
  Record t := New {
    command : Type;
    answer : command -> Type }.
End Effect.

Module C.
  Inductive t (E : Effect.t) (A : Type) : Type :=
  | Ret : A -> t E A
  | Call : forall (command : Effect.command E),
    (Effect.answer E command -> t E A) -> t E A
  | Spawn : t E A -> t E unit -> t E A.
End C.
