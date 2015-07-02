(** A trace defined without the description of a computation, with a property in
    [Prop] to assert correspondance with a computation. *)
Require Import Io.All.

Module Trace.
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
End Trace.

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

Fixpoint of_run {E A} {x : C.t E A} {v_x : A} (r_x : Run.t x v_x)
  : {t_x : Trace.t E & Valid.t x t_x v_x}.
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

Fixpoint to_run {E A} {x : C.t E A} {t_x : Trace.t E} {v_x : A}
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

Fixpoint of_to_run {E A} {x : C.t E A} {t_x : Trace.t E} {v_x : A}
  (H : Valid.t x t_x v_x) : of_run (to_run H) = existT _ t_x H.
  destruct H; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (of_to_run _ _ _ _ _ H).
    rewrite (of_to_run _ _ _ _ _ H0).
    reflexivity.
  - rewrite (of_to_run _ _ _ _ _ H).
    reflexivity.
  - rewrite (of_to_run _ _ _ _ _ H).
    reflexivity.
  - rewrite (of_to_run _ _ _ _ _ H).
    rewrite (of_to_run _ _ _ _ _ H0).
    reflexivity.
Qed.

Fixpoint to_of_run {E A} {x : C.t E A} {v_x : A} (r_x : Run.t x v_x)
  : (let (_, H) := of_run r_x in to_run H) = r_x.
  destruct r_x; simpl.
  - reflexivity.
  - reflexivity.
  - assert (H1 := to_of_run _ _ _ _ r_x1).
    destruct (of_run r_x1) as [t_x1 H_x1].
    assert (H2 := to_of_run _ _ _ _ r_x2).
    destruct (of_run r_x2) as [t_x2 H_x2].
    simpl.
    now rewrite H1; rewrite H2.
  - assert (H := to_of_run _ _ _ _ r_x).
    destruct (of_run r_x) as [t_x H_x].
    simpl.
    now rewrite H.
  - assert (H := to_of_run _ _ _ _ r_x).
    destruct (of_run r_x) as [t_x H_x].
    simpl.
    now rewrite H.
  - assert (H1 := to_of_run _ _ _ _ r_x1).
    destruct (of_run r_x1) as [t_x1 H_x1].
    assert (H2 := to_of_run _ _ _ _ r_x2).
    destruct (of_run r_x2) as [t_x2 H_x2].
    simpl.
    now rewrite H1; rewrite H2.
Qed.

Module I.
  Module Trace.
    CoInductive t (E : Effect.t) : Type :=
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

    Definition unfold {E} (t : Trace.t E) : Trace.t E :=
      match t with
      | Ret => Ret
      | Call c a => Call c a
      | Let t_x t_f => Let t_x t_f
      | ChooseLeft t => ChooseLeft t
      | ChooseRight t => ChooseRight t
      | Join t_x t_y => Join t_x t_y
      end.

    Lemma unfold_eq {E} (t : Trace.t E) : t = unfold t.
      destruct t; reflexivity.
    Defined.

    Module Eq.
      CoInductive t {E} : Trace.t E -> Trace.t E -> Prop :=
      | Ret : t Ret Ret
      | Call : forall c a, t (Call c a) (Call c a)
      | Let : forall t_x1 t_x2 t_f1 t_f2, t t_x1 t_x2 -> t t_f1 t_f2 ->
        t (Let t_x1 t_f1) (Let t_x2 t_f2)
      | ChooseLeft : forall t1 t2, t t1 t2 ->
        t (ChooseLeft t1) (ChooseLeft t2)
      | ChooseRight : forall t1 t2, t t1 t2 ->
        t (ChooseRight t1) (ChooseRight t2)
      | Join : forall t_x1 t_x2 t_y1 t_y2, t t_x1 t_x2 -> t t_y1 t_y2 ->
        t (Join t_x1 t_y1) (Join t_x2 t_y2).
    End Eq.
  End Trace.

  Module Valid.
    CoInductive t {E} : forall {A}, C.I.t E A -> Trace.t E -> A -> Type :=
    | Ret : forall A (v : A), t (C.I.Ret A v) Trace.Ret v
    | Call : forall c (a : Effect.answer E c), t (C.I.Call c) (Trace.Call c a) a
    | Let : forall A B (x : C.I.t E A) (f : A -> C.I.t E B)
      (t_x t_y : Trace.t E) (v_x : A) (v_y : B),
      t x t_x v_x -> t (f v_x) t_y v_y ->
      t (C.I.Let _ _ x f) (Trace.Let t_x t_y) v_y
    | ChooseLeft : forall A (x1 x2 : C.I.t E A) (t_x1 : Trace.t E) (v_x1 : A),
      t x1 t_x1 v_x1 -> t (C.I.Choose _ x1 x2) (Trace.ChooseLeft t_x1) v_x1
    | ChooseRight : forall A (x1 x2 : C.I.t E A) (t_x2 : Trace.t E) (v_x2 : A),
      t x2 t_x2 v_x2 -> t (C.I.Choose _ x1 x2) (Trace.ChooseRight t_x2) v_x2
    | Join : forall A B (x : C.I.t E A) (y : C.I.t E B) (t_x t_y : Trace.t E)
      (v_x : A) (v_y : B),
      t x t_x v_x -> t y t_y v_y ->
      t (C.I.Join _ _ x y) (Trace.Join t_x t_y) (v_x, v_y).
    Arguments Ret {E A} _.
    Arguments Call {E} _ _.
    Arguments Let {E A B x f t_x t_y v_x v_y} _ _.
    Arguments ChooseLeft {E A x1 x2 t_x1 v_x1} _.
    Arguments ChooseRight {E A x1 x2 t_x2 v_x2} _.
    Arguments Join {E A B x y t_x t_y v_x v_y} _ _.

    Definition unfold {E A} {x : C.I.t E A} {t : Trace.t E} {v : A}
      (H : Valid.t x t v) : Valid.t x t v :=
      match H with
      | Ret _ v => Ret v
      | Call c a => Call c a
      | Let _ _ _ _ _ _ _ _ H_x H_f => Let H_x H_f
      | ChooseLeft _ _ _ _ _ H_x1 => ChooseLeft H_x1
      | ChooseRight _ _ _ _ _ H_x2 => ChooseRight H_x2
      | Join _ _ _ _ _ _ _ _ H_x H_y => Join H_x H_y
      end.

    Lemma unfold_eq {E A} {x : C.I.t E A} {t : Trace.t E} {v : A}
      (H : Valid.t x t v) : H = unfold H.
      destruct H; reflexivity.
    Qed.
  End Valid.

  CoFixpoint trace_of_run {E A} {x : C.I.t E A} {v_x : A} (r_x : Run.I.t x v_x)
    : Trace.t E.
    destruct r_x.
    - exact Trace.Ret.
    - exact (Trace.Call c answer).
    - exact (Trace.Let (trace_of_run _ _ _ _ r_x1) (trace_of_run _ _ _ _ r_x2)).
    - exact (Trace.ChooseLeft (trace_of_run _ _ _ _ r_x)).
    - exact (Trace.ChooseRight (trace_of_run _ _ _ _ r_x)).
    - exact (Trace.Join
        (trace_of_run _ _ _ _ r_x1) (trace_of_run _ _ _ _ r_x2)).
  Defined.

  CoFixpoint valid_of_run {E A} {x : C.I.t E A} {v_x : A} (r_x : Run.I.t x v_x)
    : Valid.t x (trace_of_run r_x) v_x.
    rewrite (Trace.unfold_eq (trace_of_run _)).
    destruct r_x; simpl.
    - apply Valid.Ret.
    - apply Valid.Call.
    - eapply Valid.Let; apply valid_of_run.
    - apply Valid.ChooseLeft; apply valid_of_run.
    - apply Valid.ChooseRight; apply valid_of_run.
    - apply Valid.Join; apply valid_of_run.
  Defined.

  CoFixpoint to_run {E A} {x : C.I.t E A} {t_x : Trace.t E} {v_x : A}
    (H : Valid.t x t_x v_x) : Run.I.t x v_x.
    destruct H.
    - apply Run.I.Ret.
    - apply Run.I.Call.
    - eapply Run.I.Let.
      + eapply to_run.
        apply H.
      + eapply to_run.
        apply H0.
    - apply Run.I.ChooseLeft.
      eapply to_run.
      apply H.
    - apply Run.I.ChooseRight.
      eapply to_run.
      apply H.
    - apply Run.I.Join.
      + eapply to_run.
        apply H.
      + eapply to_run.
        apply H0.
  Defined.

  CoFixpoint trace_of_to_run {E A} {x : C.I.t E A} {t_x : Trace.t E} {v_x : A}
    (H : Valid.t x t_x v_x) : Trace.Eq.t (trace_of_run (to_run H)) t_x.
    rewrite (Trace.unfold_eq (trace_of_run _)).
    destruct H; simpl.
    - apply Trace.Eq.Ret.
    - apply Trace.Eq.Call.
    - apply Trace.Eq.Let; apply trace_of_to_run.
    - apply Trace.Eq.ChooseLeft; apply trace_of_to_run.
    - apply Trace.Eq.ChooseRight; apply trace_of_to_run.
    - apply Trace.Eq.Join; apply trace_of_to_run.
  Qed.

  CoFixpoint to_of_run {E A} {x : C.I.t E A} {v : A} (r : Run.I.t x v)
    : Run.I.Eq.t (to_run (valid_of_run r)) r.
    rewrite (Run.I.unfold_eq (to_run _)).
    destruct r; simpl.
    - apply Run.I.Eq.Ret.
    - apply Run.I.Eq.Call.
    - apply Run.I.Eq.Let; apply to_of_run.
    - apply Run.I.Eq.ChooseLeft; apply to_of_run.
    - apply Run.I.Eq.ChooseRight; apply to_of_run.
    - apply Run.I.Eq.Join; apply to_of_run.
  Qed.
End I.

Module Test.
  Require Import Coq.Lists.List.
  Require Import Coq.Strings.Ascii.
  Require Import ListString.All.

  Import ListNotations.
  Import C.Notations.
  Local Open Scope char.

  Module Command.
    Inductive t : Set :=
    | Print (message : LString.t)
    | ReadLine.

    Definition answer (c : t) : Type :=
      match c with
      | Print _ => unit
      | Read => option LString.t
      end.
  End Command.

  Definition E : Effect.t := {|
    Effect.command := Command.t;
    Effect.answer := Command.answer |}.

  Definition your_name : C.t E unit :=
    do! C.Call (E := E) (Command.Print (LString.s "What is your name?")) in
    let! name := C.Call (E := E) Command.ReadLine in
    match name return C.t E unit with
    | None => C.Ret unit tt
    | Some name => C.Call (E := E) (Command.Print (LString.s "Hello " ++ name))
    end.

  Definition your_name_uc (name : LString.t) : Trace.t E :=
    Trace.Let (Trace.Call (E := E) (Command.Print (LString.s "What is your name?")) tt) (
    Trace.Let (Trace.Call (E := E) Command.ReadLine (Some name)) (
    Trace.Call (E := E) (Command.Print (LString.s "Hello " ++ name)) tt)).

  Lemma your_name_uc_is_valid (name : LString.t)
    : Valid.t your_name (your_name_uc name) tt.
    eapply Valid.Let.
    apply Valid.Call.
    eapply Valid.Let.
    apply Valid.Call.
    apply (Valid.Call (E := E) (Command.Print _)).
  Qed.

  Definition run_your_name (name : LString.t) : Run.t your_name tt.
    apply (Run.Let (Run.Call (E := E)
      (Command.Print (LString.s "What is your name?")) tt)).
    apply (Run.Let (Run.Call (E := E) Command.ReadLine (Some name))).
    apply (Run.Call (E := E) (Command.Print (_ ++ name)) tt).
  Defined.

  Definition get_name : C.t E (option LString.t) :=
    do! C.Call (E := E) (Command.Print (LString.s "What is your name?")) in
    C.Call (E := E) Command.ReadLine.

  Definition your_name2 : C.t E unit :=
    let! name := get_name in
    match name return C.t E unit with
    | None => C.Ret unit tt
    | Some name => C.Call (E := E) (Command.Print (LString.s "Hello " ++ name))
    end.

  Definition get_name_uc (name : LString.t) : Run.t get_name (Some name).
    eapply Run.Let. apply (Run.Call (E := E) (Command.Print _) tt).
    apply (Run.Call (E := E) Command.ReadLine (Some name)).
  Defined.

  Definition your_name2_uc (name : LString.t) : Run.t your_name2 tt.
    eapply Run.Let. apply (get_name_uc name).
    apply (Run.Call (E := E) (Command.Print (LString.s _ ++ name)) tt).
  Defined.
End Test.
