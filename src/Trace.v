(** A trace defined without the description of a computation, with a property in
    [Prop] to assert correspondance with a computation. *)
Require Import Io.All.

Inductive t (E : Effect.t) : Type :=
| Ret : t E
| Call : forall c, Effect.answer E c -> t E
| Let : t E -> t E -> t E
| ChooseLeft : t E -> t E
| ChooseRight : t E -> t E
| Join : t E -> t E -> t E.
Arguments Ret {E}.
Arguments Call {E} _ _.
Arguments Let {E} _ _.
Arguments ChooseLeft {E} _.
Arguments ChooseRight {E} _.
Arguments Join {E} _ _.

Module Valid.
  Inductive t {E} : forall {A}, C.t E A -> Trace.t E -> A -> Type :=
  | Ret : forall A (v : A), t (C.Ret A v) Trace.Ret v
  | Call : forall c (a : Effect.answer E c), t (C.Call c) (Trace.Call c a) a
  | Let : forall A B (x : C.t E A) (f : A -> C.t E B) (t_x t_y : Trace.t E)
    (v_x : A) (v_y : B),
    t x t_x v_x -> t (f v_x) t_y v_y ->
    t (C.Let _ _ x f) (Trace.Let t_x t_y) v_y
  | ChooseLeft : forall A (x1 x2 : C.t E A) (t_x1 : Trace.t E) (v_x1 : A),
    t x1 t_x1 v_x1 -> t (C.Choose _ x1 x2) (Trace.ChooseLeft t_x1) v_x1
  | ChooseRight : forall A (x1 x2 : C.t E A) (t_x2 : Trace.t E) (v_x2 : A),
    t x2 t_x2 v_x2 -> t (C.Choose _ x1 x2) (Trace.ChooseRight t_x2) v_x2
  | Join : forall A B (x : C.t E A) (y : C.t E B) (t_x t_y : Trace.t E)
    (v_x : A) (v_y : B),
    t x t_x v_x -> t y t_y v_y ->
    t (C.Join _ _ x y) (Trace.Join t_x t_y) (v_x, v_y).
End Valid.

Fixpoint of_run {E A} (x : C.t E A) (v_x : A) (r_x : Run.t x v_x)
  : {t_x : t E & Valid.t x t_x v_x}.
  destruct r_x.
  - exists Trace.Ret.
    apply Valid.Ret.
  - exists (Trace.Call c answer).
    apply Valid.Call.
  - destruct (of_run _ _ _ _ r_x1) as [t_x H_x].
    destruct (of_run _ _ _ _ r_x2) as [t_y H_y].
    exists (Trace.Let t_x t_y).
    now apply Valid.Let with (v_x := x).
  - destruct (of_run _ _ _ _ r_x) as [t_x1 H_x1].
    exists (Trace.ChooseLeft t_x1).
    now apply Valid.ChooseLeft.
  - destruct (of_run _ _ _ _ r_x) as [t_x2 H_x2].
    exists (Trace.ChooseRight t_x2).
    now apply Valid.ChooseRight.
  - destruct (of_run _ _ _ _ r_x1) as [t_x H_x].
    destruct (of_run _ _ _ _ r_x2) as [t_y H_y].
    exists (Trace.Join t_x t_y).
    now apply Valid.Join.
Defined.

Fixpoint to_run {E A} (x : C.t E A) (t_x : Trace.t E) (v_x : A)
  (H : Valid.t x t_x v_x) : Run.t x v_x.
  destruct H.
  - apply Run.Ret.
  - apply Run.Call.
  - eapply Run.Let.
    + eapply to_run.
      apply H.
    + eapply to_run.
      apply H0.
  - apply Run.ChooseLeft.
    eapply to_run.
    apply H.
  - apply Run.ChooseRight.
    eapply to_run.
    apply H.
  - apply Run.Join.
    + eapply to_run.
      apply H.
    + eapply to_run.
      apply H0.
Defined.
