Require Import Io.All.
Require Import ListString.All.

Import IC.Notations.

Module Command.
  Inductive t :=
  | AskLogin
  | AskPassword
  | IsAuthorized (login password : LString.t)
  | Get (message : LString.t)
  | Run (command : LString.t)
  | Answer (result : LString.t)
  | Quit.

  Definition answer (c : t) : Type :=
    match c with
    | AskLogin => LString.t
    | AskPassword => LString.t
    | IsAuthorized _ _ => bool
    | Get _ => option LString.t
    | Run _ => LString.t
    | Answer _ => unit
    | Quit => unit
    end.
End Command.

Definition E : Effect.t :=
  Effect.New Command.t Command.answer.

Definition ask_login : IC.t E LString.t :=
  icall E Command.AskLogin.

Definition ask_password : IC.t E LString.t :=
  icall E Command.AskPassword.

Definition is_authorized (login password : LString.t) : IC.t E bool :=
  icall E (Command.IsAuthorized login password).

Definition get (message : LString.t) : IC.t E (option LString.t) :=
  icall E (Command.Get message).

Definition run (command : LString.t) : IC.t E LString.t :=
  icall E (Command.Run command).

Definition answer (result : LString.t) : IC.t E unit :=
  icall E (Command.Answer result).

Definition quit : IC.t E unit :=
  icall E Command.Quit.

CoFixpoint handle_commands : IC.t E unit :=
  ilet! command := get (LString.s "$ ") in
  match command with
  | None => quit
  | Some command =>
    ilet! result := run command in
    ido! answer result in
    handle_commands
  end.

CoFixpoint main : IC.t E unit :=
  ilet! login := ask_login in
  ilet! password := ask_password in
  ilet! valid := is_authorized login password in
  if valid then
    handle_commands
  else
    main.

Module Run.
  Definition ask_login (login : LString.t) : IRun.t ask_login login.
    apply (IRun.Call (E := E) Command.AskLogin login).
  Defined.

  Definition ask_password (password : LString.t) : IRun.t ask_password password.
    apply (IRun.Call (E := E) Command.AskPassword password).
  Defined.

  Definition is_authorized (login password : LString.t) (answer : bool)
    : IRun.t (is_authorized login password) answer.
    apply (IRun.Call (E := E) (Command.IsAuthorized login password) answer).
  Defined.

  CoFixpoint main_not_authorized (login password : LString.t) : IRun.t main tt.
    rewrite (step_eq main).
    eapply IRun.Let. apply (ask_login login).
    eapply IRun.Let. apply (ask_password password).
    eapply IRun.Let. apply (is_authorized login password false).
    apply (main_not_authorized login password).
  Defined.
End Run.
