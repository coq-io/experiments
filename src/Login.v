Require Import Coq.Lists.Streams.
Require Import Io.All.
Require Import ListString.All.

Import IC.Notations.

Module Command.
  Inductive t :=
  | AskLogin
  | AskPassword
  | IsAuthorized (login password : LString.t)
  | Get
  | Run (command : LString.t)
  | Answer (result : LString.t)
  | Quit.

  Definition answer (c : t) : Type :=
    match c with
    | AskLogin => LString.t
    | AskPassword => LString.t
    | IsAuthorized _ _ => bool
    | Get => option LString.t
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

Definition get : IC.t E (option LString.t) :=
  icall E Command.Get.

Definition run (command : LString.t) : IC.t E LString.t :=
  icall E (Command.Run command).

Definition answer (result : LString.t) : IC.t E unit :=
  icall E (Command.Answer result).

Definition quit : IC.t E unit :=
  icall E Command.Quit.

CoFixpoint handle_commands : IC.t E unit :=
  ilet! command := get in
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

  Definition get_ok (command : LString.t) : IRun.t get (Some command).
    apply (IRun.Call (E := E) Command.Get (Some command)).
  Defined.

  Definition get_quit : IRun.t get None.
    apply (IRun.Call (E := E) Command.Get None).
  Defined.

  Definition run (command result : LString.t)
    : IRun.t (run command) result.
    apply (IRun.Call (E := E) (Command.Run command) result).
  Defined.

  Definition answer (result : LString.t) : IRun.t (answer result) tt.
    apply (IRun.Call (E := E) (Command.Answer result) tt).
  Defined.

  Definition quit : IRun.t quit tt.
    apply (IRun.Call (E := E) Command.Quit tt).
  Defined.

  CoFixpoint main_not_authorized (ids : Stream (LString.t * LString.t))
    : IRun.t main tt.
    rewrite (IC.unfold_eq main).
    destruct ids as [[login password] ids].
    eapply IRun.Let. apply (ask_login login).
    eapply IRun.Let. apply (ask_password password).
    eapply IRun.Let. apply (is_authorized login password false).
    apply (main_not_authorized ids).
  Defined.

  Definition quick (login password command result : LString.t) : IRun.t main tt.
    rewrite (IC.unfold_eq main).
    eapply IRun.Let. apply (ask_login login).
    eapply IRun.Let. apply (ask_password password).
    eapply IRun.Let. apply (is_authorized login password true).
    rewrite (IC.unfold_eq handle_commands).
    eapply IRun.Let. apply (get_ok command).
    eapply IRun.Let. apply (run command result).
    eapply IRun.Let. apply (answer result).
    fold handle_commands; rewrite (IC.unfold_eq handle_commands).
    eapply IRun.Let. apply get_quit.
    apply quit.
  Defined.

  CoFixpoint handle_infinite_commands
    (commands : Stream (LString.t * LString.t)) : IRun.t handle_commands tt.
    rewrite (IC.unfold_eq handle_commands).
    destruct commands as [[command result] commands].
    eapply IRun.Let. apply (get_ok command).
    eapply IRun.Let. apply (run command result).
    eapply IRun.Let. apply (answer result).
    apply (handle_infinite_commands commands).
  Defined.
End Run.
