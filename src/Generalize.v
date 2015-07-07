(** Formalization of the notion of generalization. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Io.All.
Require Import ListString.All.

Import ListNotations.
Import C.Notations.
Local Open Scope char.

Module Command.
  Inductive t : Set :=
  | Print (message : LString.t)
  | ReadLine.

  Definition answer (c : t) : Type :=
    match c with
    | Print _ => unit
    | Read => option LString.t
    end.
End Command.

Definition E : Effect.t := {|
  Effect.command := Command.t;
  Effect.answer := Command.answer |}.

Definition your_name : C.t E unit :=
  do! C.Call (E := E) (Command.Print (LString.s "What is your name?")) in
  let! name := C.Call (E := E) Command.ReadLine in
  match name return C.t E unit with
  | None => C.Ret unit tt
  | Some name => C.Call (E := E) (Command.Print (LString.s "Hello " ++ name))
  end.

Module Run.
  Definition your_name_name (name : LString.t) : Run.t your_name tt.
    apply (Run.Let (Run.Call (E := E)
      (Command.Print (LString.s "What is your name?")) tt)).
    apply (Run.Let (Run.Call (E := E) Command.ReadLine (Some name))).
    apply (Run.Call (E := E) (Command.Print (_ ++ name)) tt).
  Defined.

  Definition your_name_me : Run.t your_name tt.
    apply (Run.Let (Run.Call (E := E)
      (Command.Print (LString.s "What is your name?")) tt)).
    apply (Run.Let (Run.Call (E := E) Command.ReadLine (Some (LString.s "me")))).
    apply (Run.Call (E := E) (Command.Print (LString.s "Hello me")) tt).
  Defined.
End Run.
