Require Import Coq.Lists.List.
Require Import Io.All.
Require Import ListString.All.

Import C.Notations.
Import ListNotations.

Module Article.
  Record t : Set := New {
    name : LString.t;
    price : nat }.

  Fixpoint total_amount (articles : list t) : nat :=
    match articles with
    | [] => 0
    | New _ price :: articles => price + total_amount articles
    end.
End Article.

Module PaymentMethod.
  Inductive t : Set :=
  | Cash
  | Credit.
End PaymentMethod.

Module Command.
  Inductive t : Set :=
  | Welcome
  | ScanArticles
  | GetPaymentMethod
  | GetCash (amount : nat)
  | GetCredit (amount : nat)
  | Goodbye.

  Definition answer (c : t) : Type :=
    match c with
    | Welcome => unit
    | ScanArticles => list Article.t
    | GetPaymentMethod => PaymentMethod.t
    | GetCash _ => unit
    | GetCredit _ => unit
    | Goodbye => unit
    end.
End Command.

Definition E : Effect.t :=
  Effect.New Command.t Command.answer.

Definition welcome : C.t E unit :=
  C.Call (E := E) Command.Welcome.

Definition scan_articles : C.t E (list Article.t) :=
  C.Call (E := E) Command.ScanArticles.

Definition get_payment_method : C.t E PaymentMethod.t :=
  C.Call (E := E) Command.GetPaymentMethod.

Definition get_cash (amount : nat) : C.t E unit :=
  C.Call (E := E) (Command.GetCash amount).

Definition get_credit (amount : nat) : C.t E unit :=
  C.Call (E := E) (Command.GetCredit amount).

Definition goodbye : C.t E unit :=
  C.Call (E := E) Command.Goodbye.

Definition program : C.t E unit :=
  do! welcome in
  let! articles := scan_articles in
  let amount := Article.total_amount articles in
  let! payment_method := get_payment_method in
  do!
    match payment_method with
    | PaymentMethod.Cash => get_cash amount
    | PaymentMethod.Credit => get_credit amount
    end in
  goodbye.
