(** Composition of effects. *)
Require Import Io.All.

Definition compose (E1 E2 : Effect.t) : Effect.t :=
  Effect.New (Effect.command E1 + Effect.command E2) (fun c =>
    match c with
    | inl c1 => Effect.answer E1 c1
    | inr c2 => Effect.answer E2 c2
    end).
