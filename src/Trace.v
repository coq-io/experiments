(** Experiments about the traces. *)
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

Definition your_name_uc (name : LString.t) : Trace.t E :=
  Trace.Let (Trace.Call (E := E) (Command.Print (LString.s "What is your name?")) tt) (
  Trace.Let (Trace.Call (E := E) Command.ReadLine (Some name)) (
  Trace.Call (E := E) (Command.Print (LString.s "Hello " ++ name)) tt)).

Module WithTraceNotations.
  Import Trace.Notations.

  Definition your_name_uc' (name : LString.t) : Trace.t E :=
    tlet! call E (Command.Print (LString.s "What is your name?")) tt in
    tlet! call E Command.ReadLine (Some name) in
    call E (Command.Print (LString.s "Hello " ++ name)) tt.
End WithTraceNotations.

Lemma your_name_uc_is_valid (name : LString.t)
  : Valid.t your_name (your_name_uc name) tt.
  eapply Valid.Let.
  apply Valid.Call.
  eapply Valid.Let.
  apply Valid.Call.
  apply (Valid.Call (E := E) (Command.Print _)).
Qed.

Definition run_your_name (name : LString.t) : Run.t your_name tt.
  apply (Run.Let (Run.Call (E := E)
    (Command.Print (LString.s "What is your name?")) tt)).
  apply (Run.Let (Run.Call (E := E) Command.ReadLine (Some name))).
  apply (Run.Call (E := E) (Command.Print (_ ++ name)) tt).
Defined.

Module WithRunNotations.
  Import Run.Notations.

  Definition run_your_name (name : LString.t) : Run.t your_name tt :=
    rlet! call E (Command.Print (LString.s "What is your name?")) tt in
    rlet! call E Command.ReadLine (Some name) in
    call E (Command.Print (_ ++ name)) tt.
End WithRunNotations.

Definition get_name : C.t E (option LString.t) :=
  do! C.Call (E := E) (Command.Print (LString.s "What is your name?")) in
  C.Call (E := E) Command.ReadLine.

Definition your_name2 : C.t E unit :=
  let! name := get_name in
  match name return C.t E unit with
  | None => C.Ret unit tt
  | Some name => C.Call (E := E) (Command.Print (LString.s "Hello " ++ name))
  end.

Definition get_name_uc (name : LString.t) : Run.t get_name (Some name).
  eapply Run.Let. apply (Run.Call (E := E) (Command.Print _) tt).
  apply (Run.Call (E := E) Command.ReadLine (Some name)).
Defined.

Definition your_name2_uc (name : LString.t) : Run.t your_name2 tt.
  eapply Run.Let. apply (get_name_uc name).
  apply (Run.Call (E := E) (Command.Print (LString.s _ ++ name)) tt).
Defined.
