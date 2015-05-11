Require Import Io.All.

Module Command.
  Inductive t : Set :=
  | Welcome
  | ScanArticle
  | GetLoyaltyCard
  | GetPaymentMethod
  | GetCash (n : nat)
  | GetCredit (n : nat)
  | Goodbye.
End Command.
