Require Import Io.All.
Require Import ListString.All.

Module Article.
  Record t : Set := New {
    name : LString.t;
    price : nat }.
End Article.

Module LoyaltyCard.
  Inductive t : Set :=
  | NoCard
  | MarketCard.
End LoyaltyCard.

Module PaymentMethod.
  Inductive t : Set :=
  | Cash
  | Credit.
End PaymentMethod.

Module Command.
  Inductive t : Set :=
  | Welcome
  | ScanArticle
  | GetLoyaltyCard
  | GetPaymentMethod
  | GetCash (n : nat)
  | GetCredit (n : nat)
  | Goodbye.

  Definition answer (c : t) : Type :=
    match c with
    | Welcome => unit
    | ScanArticle => option Article.t
    | GetLoyaltyCard => LoyaltyCard.t
    | GetPaymentMethod => PaymentMethod.t
    | GetCash _ => unit
    | GetCredit _ => unit
    | Goodbye => unit
    end.
End Command.
