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
  Inductive t (E : Effect.t) (S : Type) : Type :=
  | Ret : t E S
  | Call : Effect.command E -> (S -> t E S) -> t E S
  | Choose : t E S -> t E S -> t E S.
  Arguments Ret {E S}.
  Arguments Call {E S} _ _.
  Arguments Choose {E S} _ _.

  Module Mix.
    Inductive t {E S} : Sequential.t E -> Choose.t E S -> Type :=
    | RetRet : t Sequential.Ret Choose.Ret
    | RetCall : forall c h, t Sequential.Ret (Choose.Call c h)
    | RetChoose : forall x1 x2, t Sequential.Ret (Choose.Choose x1 x2)
    | CallRet : forall c h, t (Sequential.Call c h) Choose.Ret
    | CallCall : forall c_x h_x c_y h_y,
      (forall a, t (h_x a) (Choose.Call c_y h_y)) ->
      (forall s, t (Sequential.Call c_x h_x) (h_y s)) ->
      t (Sequential.Call c_x h_x) (Choose.Call c_y h_y)
    | CallChoose : forall c h y1 y2,
      t (Sequential.Call c h) y1 -> t (Sequential.Call c h) y2 ->
      t (Sequential.Call c h) (Choose.Choose y1 y2).
    Arguments RetRet {E S}.
    Arguments RetCall {E S} _ _.
    Arguments RetChoose {E S} _ _.
    Arguments CallRet {E S} _ _.
    Arguments CallCall {E S c_x h_x c_y h_y} _ _.
    Arguments CallChoose {E S c h y1 y2} _ _.

    Fixpoint make_call {E S} (x : Sequential.t E)
      (c_y : Effect.command E) (h_y : S -> Choose.t E S)
      (z : forall x s, t x (h_y s)) : t x (Choose.Call c_y h_y) :=
      match x with
      | Sequential.Ret => RetCall c_y h_y
      | Sequential.Call c_x h_x =>
        CallCall (fun a => make_call (h_x a) c_y h_y z)
          (fun s => z (Sequential.Call c_x h_x) s)
      end.

    Fixpoint make {E S} (x : Sequential.t E) (y : Choose.t E S) : t x y :=
      match y with
      | Choose.Ret =>
        match x with
        | Sequential.Ret => RetRet
        | Sequential.Call c_x h_x => CallRet c_x h_x
        end
      | Choose.Call c_y h_y => make_call x c_y h_y (fun x s => make x (h_y s))
      | Choose.Choose y1 y2 =>
        match x with
        | Sequential.Ret => RetChoose y1 y2
        | Sequential.Call c_x h_x =>
          CallChoose (make (Sequential.Call c_x h_x) y1)
            (make (Sequential.Call c_x h_x) y2)
        end
      end.
  End Mix.

  

  (*Fixpoint compile {E S} m (x : Sequential.t E) (y : t E S) {struct y} : t E S :=
    (*let fix aux (x : Sequential.t E) {struct x} : t E S :=
      match (x, y) with
      | (Sequential.Ret, y) => y
      | (Sequential.Call c h, Ret) =>
        Call c (fun s => compile m (h (Model.answer m c s)) y)
      | (Sequential.Call c h, Call c' h') =>
        Choose
          (Call c (fun s => compile m (h (Model.answer m c s)) y))
          (Call c' (fun s' => compile m x (h' s')))
      | (Sequential.Call c h, Choose y1 y2) =>
        Choose (compile m x y1) (compile m x y2)
      end in*)
    match (x, y) with
    | (Sequential.Ret, y) => y
    | (Sequential.Call c h, Ret) =>
      Call c (fun s => compile m (h (Model.answer m c s)) y)
    | (Sequential.Call c h, Call c' h') =>
      Choose
        (Call c (fun s => compile m (h (Model.answer m c s)) y))
        (Call c' (fun s' => compile m x (h' s')))
    | (Sequential.Call c h, Choose y1 y2) =>
      Choose (compile m x y1) (compile m x y2)
    end.*)
End Choose.
