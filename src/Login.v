Require Import Coq.Lists.Streams.
Require Import Io.All.
Require Import ListPlus.All.
Require Import ListString.All.

Import C.I.Notations.

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

Definition ask_login : C.I.t E LString.t :=
  I.call E Command.AskLogin.

Definition ask_password : C.I.t E LString.t :=
  I.call E Command.AskPassword.

Definition is_authorized (login password : LString.t) : C.I.t E bool :=
  I.call E (Command.IsAuthorized login password).

Definition get : C.I.t E (option LString.t) :=
  I.call E Command.Get.

Definition run (command : LString.t) : C.I.t E LString.t :=
  I.call E (Command.Run command).

Definition answer (result : LString.t) : C.I.t E unit :=
  I.call E (Command.Answer result).

Definition quit : C.I.t E unit :=
  I.call E Command.Quit.

CoFixpoint handle_commands : C.I.t E unit :=
  ilet! command := get in
  match command with
  | None => quit
  | Some command =>
    ilet! result := run command in
    ido! answer result in
    handle_commands
  end.

CoFixpoint main : C.I.t E unit :=
  ilet! login := ask_login in
  ilet! password := ask_password in
  ilet! valid := is_authorized login password in
  if valid then
    handle_commands
  else
    main.

Module Run.
  Definition ask_login (login : LString.t) : Run.I.t ask_login login.
    apply (Run.I.Call (E := E) Command.AskLogin login).
  Defined.

  Definition ask_password (password : LString.t)
    : Run.I.t ask_password password.
    apply (Run.I.Call (E := E) Command.AskPassword password).
  Defined.

  Definition is_authorized (login password : LString.t) (answer : bool)
    : Run.I.t (is_authorized login password) answer.
    apply (Run.I.Call (E := E) (Command.IsAuthorized login password) answer).
  Defined.

  Definition get_ok (command : LString.t) : Run.I.t get (Some command).
    apply (Run.I.Call (E := E) Command.Get (Some command)).
  Defined.

  Definition get_quit : Run.I.t get None.
    apply (Run.I.Call (E := E) Command.Get None).
  Defined.

  Definition run (command result : LString.t)
    : Run.I.t (run command) result.
    apply (Run.I.Call (E := E) (Command.Run command) result).
  Defined.

  Definition answer (result : LString.t) : Run.I.t (answer result) tt.
    apply (Run.I.Call (E := E) (Command.Answer result) tt).
  Defined.

  Definition quit : Run.I.t quit tt.
    apply (Run.I.Call (E := E) Command.Quit tt).
  Defined.

  CoFixpoint main_not_authorized (ids : Stream (LString.t * LString.t))
    : Run.I.t main tt.
    rewrite (C.I.unfold_eq main).
    destruct ids as [[login password] ids].
    eapply Run.I.Let. apply (ask_login login).
    eapply Run.I.Let. apply (ask_password password).
    eapply Run.I.Let. apply (is_authorized login password false).
    apply (main_not_authorized ids).
  Defined.

  Definition quick (login password command result : LString.t)
    : Run.I.t main tt.
    rewrite (C.I.unfold_eq main).
    eapply Run.I.Let. apply (ask_login login).
    eapply Run.I.Let. apply (ask_password password).
    eapply Run.I.Let. apply (is_authorized login password true).
    rewrite (C.I.unfold_eq handle_commands).
    eapply Run.I.Let. apply (get_ok command).
    eapply Run.I.Let. apply (run command result).
    eapply Run.I.Let. apply (answer result).
    fold handle_commands; rewrite (C.I.unfold_eq handle_commands).
    eapply Run.I.Let. apply get_quit.
    apply quit.
  Defined.

  CoFixpoint handle_infinite_commands
    (commands : Stream (LString.t * LString.t)) : Run.I.t handle_commands tt.
    rewrite (C.I.unfold_eq handle_commands).
    destruct commands as [[command result] commands].
    eapply Run.I.Let. apply (get_ok command).
    eapply Run.I.Let. apply (run command result).
    eapply Run.I.Let. apply (answer result).
    apply (handle_infinite_commands commands).
  Defined.
End Run.

Module Users.
  Definition t := list (LString.t * LString.t).
End Users.

Module Eval.
  Definition eval_command (users : Users.t) (c : Command.t)
    : C.I.t E (Effect.answer E c) :=
    match c with
    | Command.IsAuthorized login password =>
      match Assoc.find LString.eqb users login with
      | None => I.ret false
      | Some password' => I.ret (LString.eqb password password')
      end
    | Command.AskLogin => I.call E Command.AskLogin
    | Command.AskPassword => I.call E Command.AskPassword
    | Command.Get => I.call E Command.Get
    | Command.Run command => I.call E (Command.Run command)
    | Command.Answer result => I.call E (Command.Answer result)
    | Command.Quit => I.call E Command.Quit
    end.
End Eval.
