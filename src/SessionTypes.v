Require Import Io.All.

Module Session.
  Inductive t (E : Effect.t) : Type -> Type :=
  | Ret : forall (A : Type), t E A
  | Call : forall (c : Effect.command E), t E (Effect.answer E c)
  | Let : forall (A B : Type), t E A -> (A -> t E B) -> t E B
  | Choose : forall (A : Type), t E A -> t E A -> t E A
  | Join : forall (A B : Type), t E A -> t E B -> t E (A * B).
  Arguments Ret {E} _.
  Arguments Call {E} _.
  Arguments Let {E A B} _ _.
  Arguments Choose {E A} _ _.
  Arguments Join {E A B} _ _.

  Fixpoint eval {E : Effect.t} {A : Type} (x : C.t E A) : t E A :=
    match x with
    | C.Ret A _ => Ret A
    | C.Call c => Call c
    | C.Let _ _ x f => Let (eval x) (fun v => eval (f v))
    | C.Choose _ x1 x2 => Choose (eval x1) (eval x2)
    | C.Join _ _ x y => Join (eval x) (eval y)
    end.

  Module Valid.
    Inductive t {E} : forall {A}, C.t E A -> Session.t E A -> Prop :=
    | Ret : forall A (x : A), t (C.Ret _ x) (Session.Ret A)
    | Call : forall c, t (C.Call c) (Session.Call c)
    | Let : forall A B (x : C.t E A) (f : A -> C.t E B) (s_x : Session.t E A)
      (s_f : A -> Session.t E B), t x s_x -> (forall v, t (f v) (s_f v)) ->
      t (C.Let _ _ x f) (Session.Let s_x s_f)
    | Choose : forall A (x1 x2 : C.t E A) (s1 s2 : Session.t E A),
      t x1 s1 -> t x2 s2 -> t (C.Choose _ x1 x2) (Session.Choose s1 s2)
    | Join : forall A B (x : C.t E A) (y : C.t E B) (s_x : Session.t E A)
      (s_y : Session.t E B), t x s_x -> t y s_y ->
      t (C.Join _ _ x y) (Session.Join s_x s_y).

    Fixpoint eval_is_valid {E A} (x : C.t E A) : t x (Session.eval x).
      destruct x; simpl.
      - apply Ret.
      - apply Call.
      - apply Let.
        + apply eval_is_valid.
        + intro.
          apply eval_is_valid.
      - apply Choose.
        + apply eval_is_valid.
        + apply eval_is_valid.
      - apply Join.
        + apply eval_is_valid.
        + apply eval_is_valid.
    Qed.

    (*Fixpoint unicity {E A} (x : C.t E A) (s : Session.t E A)
      (H : t x s) : s = Session.eval x.
      destruct x; simpl.
      - now inversion_clear H.
      - refine (
          match H in t x s return
            match x with
            | C.Call c => s = Session.Call c
            | _ => True
            end : Prop with
          | Call _ => _
          | _ => I
          end).
      - inversion_clear H.
    Qed.

    Fixpoint unicity {E A} (x : C.t E A) (s s' : Session.t E A)
      (H : t x s) (H' : t x s') : s = s'.
      destruct x.
    Qed.*)
  End Valid.
End Session.

Module Example.
  Require Import Coq.Lists.List.
  Require Import Coq.Strings.Ascii.
  Require Import Io.All.
  Require Import Io.System.All.
  Require Import ListString.All.

  Import ListNotations.
  Import C.Notations.
  Local Open Scope char.

  Definition your_name : C.t System.effect unit :=
    do! System.log (LString.s "What is your name?") in
    let! name := System.read_line in
    match name with
    | None => ret tt
    | Some name => System.log (LString.s "Hello " ++ name ++ LString.s "!")
    end.

  Definition your_name_session : Session.t System.effect unit :=
    Session.Let (Session.eval (System.log (LString.s "What is your name?"))) (fun _ =>
    Session.Let (Session.eval System.read_line) (fun name =>
    match name with
    | None => Session.Ret unit
    | Some name => Session.eval (System.log (LString.s "Hello " ++ name ++ LString.s "!"))
    end)).

  Lemma your_name_session_is_valid
    : Session.Valid.t your_name your_name_session.
    apply Session.Valid.Let; [apply Session.Valid.eval_is_valid |]; intro.
    apply Session.Valid.Let; [apply Session.Valid.eval_is_valid |]; intro name.
    destruct name as [name |].
    - apply Session.Valid.eval_is_valid.
    - apply Session.Valid.Ret.
  Qed.
End Example.
