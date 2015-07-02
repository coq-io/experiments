(** A program to guess the number of the user using comparisons. *)
Require Import Coq.Lists.List.
Require Import Io.All.
Require Import Io.Evaluate.

Import C.Notations.

Module Command.
  Inductive t (A : Type) :=
  | Propose : A -> t A.
  Arguments Propose {A} _.

  Definition answer {A : Type} (c : t A) : Type :=
    match c with
    | Propose _ => comparison
    end.
End Command.

Definition E (A : Type) : Effect.t :=
  Effect.New (Command.t A) Command.answer.

Definition propose {A : Type} (x : A) : C.t (E A) comparison :=
  call (E A) (Command.Propose x).

Fixpoint guess {A} (mean : A -> A -> A) (steps : nat) (min max : A)
  : C.t (E A) (option A) :=
  match steps with
  | O => ret None
  | S steps =>
    let m := mean min max in
    let! answer := propose m in
    match answer with
    | Lt => guess mean steps min m
    | Gt => guess mean steps m max
    | Eq => ret (Some m)
    end
  end.

Module Run.
  Definition propose {A} (x : A) (c : comparison) : Run.t (propose x) c.
    apply (Run.Call (E := E A) (Command.Propose x) c).
  Defined.

  Fixpoint never {A} (mean : A -> A -> A) (min max : A) (l : list bool)
    : Run.t (guess mean (List.length l) min max) None.
    destruct l as [|b l]; simpl.
    - apply Run.Ret.
    - destruct b.
      + eapply Run.Let. apply (propose _ Lt).
        apply never.
      + eapply Run.Let. apply (propose _ Gt).
        apply never.
  Defined.

  Definition simple_ok {A} (mean : A -> A -> A) (min max : A)
    : Run.t (guess mean 1 min max) (Some (mean min max)).
    eapply Run.Let. apply (propose _ Eq).
    apply Run.Ret.
  Defined.

  Fixpoint ok {A} (mean : A -> A -> A) (min max : A) (l : list bool)
    : {x : A & Run.t (guess mean (S (List.length l)) min max) (Some x)}.
    destruct l; simpl.
    - exists (mean min max).
      eapply Run.Let. apply (propose _ Eq).
      apply Run.Ret.
    - destruct b.
      + destruct (ok _ mean min (mean min max) l) as [x r].
        exists x.
        eapply Run.Let. apply (propose _ Lt).
        apply r.
      + destruct (ok _ mean (mean min max) max l) as [x r].
        exists x.
        eapply Run.Let. apply (propose _ Gt).
        apply r.
  Defined.

  Fixpoint mean_n {A} (mean : A -> A -> A) (steps : nat) (min max : A) : A :=
    match steps with
    | O => mean min max
    | S steps => mean_n mean steps min (mean min max)
    end.

  Fixpoint lts {A} (mean : A -> A -> A) (min max : A) (steps : nat)
    : Run.t (guess mean (S steps) min max) (Some (mean_n mean steps min max)).
    destruct steps as [|steps]; simpl.
    - eapply Run.Let. apply (propose _ Eq).
      apply Run.Ret.
    - eapply Run.Let. apply (propose _ Lt).
      apply lts.
  Defined.
End Run.

Module Eval.
  Definition eval_command {A} (compare : A -> A -> comparison) (x : A)
    (c : Command.t A) : Effect.answer (E A) c :=
    match c with
    | Command.Propose x' => compare x x'
    end.

  Definition eval {A B} (compare : A -> A -> comparison) (x : A)
    (e : C.t (E A) B) : B :=
    Evaluate.pure (E := E A) (eval_command compare x) (fun _ x _ => x) e.
End Eval.

Module Nat.
  Require Import Coq.Arith.Compare_dec.
  Require Import Coq.Arith.Div2.

  Definition mean (n m : nat) : nat :=
    div2 (n + m).

  Definition ex1 : Run.t (guess mean 5 0 10) (Some 4).
    apply (Run.Let (Run.propose 5 Lt)).
    apply (Run.Let (Run.propose 2 Gt)).
    apply (Run.Let (Run.propose 3 Gt)).
    apply (Run.Let (Run.propose 4 Eq)).
    apply Run.Ret.
  Defined.

  Definition ex2 : Eval.eval nat_compare 4 (guess mean 5 0 10) = Some 4 :=
    eq_refl.
End Nat.
