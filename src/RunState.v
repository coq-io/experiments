Require Import Coq.Lists.List.
Require Import Io.All.

Import C.Notations.
Import ListNotations.

Module Full.
  Module Command.
    Inductive t :=
    | Get
    | Store (n : nat)
    | Read.

    Definition answer (c : t) : Type :=
      match c with
      | Get => nat
      | Store _ => unit
      | Read => list nat
      end.
  End Command.

  Definition E : Effect.t :=
    Effect.New Command.t Command.answer.

  Definition get : C.t E nat :=
    C.Call (E := E) Command.Get.

  Definition store (n : nat) : C.t E unit :=
    C.Call (E := E) (Command.Store n).

  Definition read : C.t E (list nat) :=
    C.Call (E := E) Command.Read.
End Full.

Module Get.
  Definition S := list nat.

  Module Command.
    Inductive t :=
    | Get.

    Definition answer (c : t) : Type :=
      match c with
      | Get => nat
      end.
  End Command.

  Definition E : Effect.t :=
    Effect.New Command.t Command.answer.

  Definition get : C.t E nat :=
    C.Call (E := E) Command.Get.

  Definition command (c : Full.Command.t) (s : S)
    : C.t E (Effect.answer Full.E c * S) :=
    match c with
    | Full.Command.Get =>
      let! n := get in
      ret (n, s)
    | Full.Command.Store n => ret (tt, n :: s)
    | Full.Command.Read => ret (s, s)
    end.

  Fixpoint eval {A} (x : C.t Full.E A) (s : S) : C.t E (A * S) :=
    match x with
    | C.Ret _ v => ret (v, s)
    | C.Call c => command c s
    | C.Let _ _ x f =>
      let! v_x_s := eval x s in
      let (v_x, s) := v_x_s in
      eval (f v_x) s
    | C.Choose _ x1 x2 => choose (eval x1 s) (eval x2 s)
    | C.Join _ _ x y =>
      let! r := join (eval x []) (eval y []) in
      match r with
      | ((v_x, s_x), (v_y, s_y)) => ret ((v_x, v_y), s_x ++ s_y ++ s)
      end
    end.

  Module Run.
    Import Io.Run.

    Definition get (n : nat) : Run.t get n.
      apply (Call (E := E) Command.Get n).
    Qed.

    Definition eval_get (n : nat) (s : S) : Run.t (eval Full.get s) (n, s).
      eapply Let.
      - apply get.
      - apply Ret.
    Defined.
  End Run.
End Get.

Module Example.
  Fixpoint program (steps : nat) : C.t Full.E unit :=
    match steps with
    | O => ret tt
    | S steps =>
      do! program steps in
      let! n := Full.get in
      Full.store n
    end.

  Module Run.
    Import Io.Run.

    Definition program_one (n : nat) : Run.t (Get.eval (program 1) []) (tt, [n]).
      simpl.
      eapply Let. apply Ret.
      eapply Let.
      - apply Get.Run.eval_get.
      - apply Ret.
    Defined.

    Fixpoint program_n (l : list nat)
      : Run.t (Get.eval (program (List.length l)) []) (tt, l).
      destruct l as [| n l]; simpl.
      - apply Ret.
      - eapply Let.
        + apply program_n.
        + simpl.
          eapply Let.
          * apply (Get.Run.eval_get n).
          * apply Ret.
    Defined.
  End Run.
End Example.
