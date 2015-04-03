(** Sequential computations. *)

Module Effect.
  Record t := New {
    command : Type;
    answer : command -> Type }.
End Effect.

Module Callback.
  Inductive t (E : Effect.t) (A : Type) : Type :=
  | Ret : t E A
  | Call : forall (c : Effect.command E), (Effect.answer E c -> t E A) -> t E A.
  Arguments Ret _ _.
  Arguments Call {E A} _ _.
End Callback.

Module Monad.
  Inductive t (E : Effect.t) : Type -> Type :=
  | Ret : forall (A : Type) (x : A), t E A
  | Call : forall (c : Effect.command E), t E (Effect.answer E c)
  | Let : forall (A B : Type), t E A -> (A -> t E B) -> t E B.
  Arguments Ret _ {A} _.
  Arguments Call {E} _.
  Arguments Let {E} _ _ _ _.
End Monad.

Fixpoint compile {E : Effect.t} {A B : Type} (x : Monad.t E A)
  : (A -> Callback.t E B) -> Callback.t E B :=
  match x with
  | Monad.Ret _ x => fun k => k x
  | Monad.Call c => fun k => Callback.Call c k
  | Monad.Let _ _ x f => fun k => compile x (fun x => compile (f x) k)
  end.
