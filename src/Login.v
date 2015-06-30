Require Import Io.All.
Require Import ListString.All.

Import IC.Notations.

Module Command.
  Inductive t :=
  | AskLogin
  | AskPassword.

  Definition answer (c : t) : Type :=
    match c with
    | AskLogin => LString.t
    | AskPassword => LString.t
    end.
End Command.

Definition E : Effect.t :=
  Effect.New Command.t Command.answer.

Definition ask_login : IC.t E LString.t :=
  icall E Command.AskLogin.

Definition ask_password : IC.t E LString.t :=
  icall E Command.AskPassword.

CoFixpoint main : IC.t E unit :=
  ilet! login := ask_login in
  ilet! password := ask_password in
  if LString.eqb login password then
    iret tt
  else
    main.
