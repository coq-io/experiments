(** An example of ATM program. *)
Require Import Coq.NArith.NArith.
Require Import Io.All.
Require Import ListString.All.

Import C.Notations.

Module Command.
  Inductive t :=
  | GetLogin
  | GetPassword
  | CheckAuthorization (login : LString.t) (password : LString.t)
  | GetWithdrawAmount
  | DoWithdraw (amount : N)
  | GiveMoney (amount : N)
  | DisplayError (message : LString.t).

  Definition answer (c : t) : Type :=
    match c with
    | GetLogin => LString.t
    | GetPassword => LString.t
    | CheckAuthorization _ _ => bool
    | GetWithdrawAmount => N
    | DoWithdraw _ => bool
    | GiveMoney _ => bool
    | DisplayError _ => unit
    end.
End Command.

Definition E : Effect.t :=
  Effect.New Command.t Command.answer.

Definition main : C.t E unit :=
  let! login := call E Command.GetLogin in
  let! password := call E Command.GetPassword in
  let! is_authorized := call E (Command.CheckAuthorization login password) in
  if is_authorized then
    let! amount := call E Command.GetWithdrawAmount in
    let! is_withdraw_ok := call E (Command.DoWithdraw amount) in
    if is_withdraw_ok then
      let! is_money_ok := call E (Command.GiveMoney amount) in
      if is_money_ok then
        ret tt
      else
        call E (Command.DisplayError (LString.s "Cannot give you the money."))
    else
      call E (Command.DisplayError (LString.s "Cannot withdraw the money."))
  else
    call E (Command.DisplayError (LString.s "Wrong password.")).

Module Run.
  Import Io.Run.

  Definition main_ok (login password : LString.t) (amount : N) : Run.t main tt.
    eapply Let; [apply (Call E Command.GetLogin login) |].
    eapply Let; [apply (Call E Command.GetPassword password) |].
    eapply Let;
      [apply (Call E (Command.CheckAuthorization login password) true) |].
    eapply Let; [apply (Call E Command.GetWithdrawAmount amount) |].
    eapply Let; [apply (Call E (Command.DoWithdraw amount) true) |].
    eapply Let; [apply (Call E (Command.GiveMoney amount) true) |].
    apply Ret.
  Defined.
End Run.
