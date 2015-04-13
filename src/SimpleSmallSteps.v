Require Import Coq.Lists.List.

Import ListNotations.

Module Effect.
  Record t := New {
    command : Type;
    answer : command -> Type }.
End Effect.

Module Model.
  Record t (E : Effect.t) (S : Type) := New {
    condition : Effect.command E -> S -> Prop;
    answer : forall c, S -> Effect.answer E c;
    state : Effect.command E -> S -> S }.
  Arguments New {E S} _ _ _.
  Arguments condition {E S} _ _ _.
  Arguments answer {E S} _ _ _.
  Arguments state {E S} _ _ _.
End Model.

Module Sequential.
  Inductive t (E : Effect.t) : Type :=
  | Ret : t E
  | Call : forall c, (Effect.answer E c -> t E) -> t E.
  Arguments Ret {E}.
  Arguments Call {E} _ _.
End Sequential.

Module Concurrent.
  Definition t (E : Effect.t) := list (Sequential.t E).
End Concurrent.

Module Choose.
  Inductive t (E : Effect.t) : Type :=
  | Ret : t E
  | Call : forall c, (Effect.answer E c -> t E) -> t E
  | Choose : t E -> t E -> t E.
  Arguments Ret {E}.
  Arguments Call {E} _ _.
  Arguments Choose {E} _ _.

  Fixpoint lift {E} (x : Sequential.t E) : t E :=
    match x with
    | Sequential.Ret => Ret
    | Sequential.Call c h => Choose.Call c (fun a => lift (h a))
    end.

  Module Mix.
    Inductive t {E} : Sequential.t E -> Choose.t E -> Type :=
    | RetRet : t Sequential.Ret Choose.Ret
    | RetCall : forall c h, t Sequential.Ret (Choose.Call c h)
    | RetChoose : forall x1 x2, t Sequential.Ret (Choose.Choose x1 x2)
    | CallRet : forall c h, t (Sequential.Call c h) Choose.Ret
    | CallCall : forall c_x h_x c_y h_y,
      (forall a, t (h_x a) (Choose.Call c_y h_y)) ->
      (forall a, t (Sequential.Call c_x h_x) (h_y a)) ->
      t (Sequential.Call c_x h_x) (Choose.Call c_y h_y)
    | CallChoose : forall c h y1 y2,
      t (Sequential.Call c h) y1 -> t (Sequential.Call c h) y2 ->
      t (Sequential.Call c h) (Choose.Choose y1 y2).
    Arguments RetRet {E}.
    Arguments RetCall {E} _ _.
    Arguments RetChoose {E} _ _.
    Arguments CallRet {E} _ _.
    Arguments CallCall {E c_x h_x c_y h_y} _ _.
    Arguments CallChoose {E c h y1 y2} _ _.

    Fixpoint make_call {E} (x : Sequential.t E)
      (c_y : Effect.command E) (h_y : Effect.answer E c_y -> Choose.t E)
      (z : forall x a, t x (h_y a)) : t x (Choose.Call c_y h_y) :=
      match x with
      | Sequential.Ret => RetCall c_y h_y
      | Sequential.Call c_x h_x =>
        CallCall (fun a => make_call (h_x a) c_y h_y z)
          (fun a => z (Sequential.Call c_x h_x) a)
      end.

    Fixpoint make {E} (x : Sequential.t E) (y : Choose.t E) : t x y :=
      match y with
      | Choose.Ret =>
        match x with
        | Sequential.Ret => RetRet
        | Sequential.Call c_x h_x => CallRet c_x h_x
        end
      | Choose.Call c_y h_y => make_call x c_y h_y (fun x a => make x (h_y a))
      | Choose.Choose y1 y2 =>
        match x with
        | Sequential.Ret => RetChoose y1 y2
        | Sequential.Call c_x h_x =>
          CallChoose (make (Sequential.Call c_x h_x) y1)
            (make (Sequential.Call c_x h_x) y2)
        end
      end.

    Fixpoint compile {E} {x y} (xy : t x y) : Choose.t E :=
      match xy with
      | RetRet => Choose.Ret
      | RetCall c_y h_y => Choose.Call c_y h_y
      | RetChoose y1 y2 => Choose.Choose y1 y2
      | CallRet c_x h_x => Choose.Call c_x (fun a => lift (h_x a))
      | CallCall c_x _ c_y _ m_x m_y =>
        Choose.Choose (Choose.Call c_x (fun a => compile (m_x a)))
          (Choose.Call c_y (fun a => compile (m_y a)))
      | CallChoose _ _ _ _ m_y1 m_y2 =>
        Choose.Choose (compile m_y1) (compile m_y2)
      end.
  End Mix.

  Fixpoint compile {E} (xs : Concurrent.t E) : Choose.t E :=
    match xs with
    | [] => Ret
    | x :: xs => Mix.compile (Mix.make x (compile xs))
    end.
End Choose.
