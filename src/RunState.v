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

  Definition eval_command (c : Full.Command.t) (s : S)
    : C.t E (Effect.answer Full.E c * S) :=
    match c with
    | Full.Command.Get =>
      let! n := get in
      ret (n, s)
    | Full.Command.Store n => ret (tt, n :: s)
    | Full.Command.Read => ret (s, s)
    end.

  Fixpoint eval {A} (x : C.t Full.E A) (s : S) : C.t E (A * S) :=
    match x in C.t _ A return C.t E (A * S) with
    | C.Ret _ v => ret (v, s)
    | C.Call c => eval_command c s
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
End Get.

Fixpoint program (steps : nat) : C.t Full.E (list nat) :=
  match steps with
  | O => Full.read
  | S steps =>
    let! n := Full.get in
    do! Full.store n in
    program steps
  end.
