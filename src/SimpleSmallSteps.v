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

  Fixpoint compile {E S} m (x : Sequential.t E) (y : t E S) {struct y} : t E S :=
    let fix aux (x : Sequential.t E) {struct x} : t E S :=
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
      end in
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
    end.
End Choose.
