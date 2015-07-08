(** Formalization of the notion of generalization. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Io.All.
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

Module Run.
  Definition your_name_all (name : option LString.t) : Run.t your_name tt.
    apply (Run.Let (Run.Call (E := E)
      (Command.Print (LString.s "What is your name?")) tt)).
    destruct name as [name |].
    - apply (Run.Let (Run.Call (E := E) Command.ReadLine (Some name))).
      apply (Run.Call (E := E) (Command.Print (_ ++ name)) tt).
    - apply (Run.Let (Run.Call (E := E) Command.ReadLine None)).
      apply Run.Ret.
  Defined.

  Definition your_name_me : Run.t your_name tt.
    apply (Run.Let (Run.Call (E := E)
      (Command.Print (LString.s "What is your name?")) tt)).
    apply (Run.Let (Run.Call (E := E) Command.ReadLine (Some (LString.s "me")))).
    apply (Run.Call (E := E) (Command.Print (LString.s "Hello me")) tt).
  Defined.

  Lemma name_generalizes_name : exists (name : option LString.t),
    your_name_me = your_name_all name.
    exists (Some (LString.s "me")).
    reflexivity.
  Qed.
End Run.

Module UseCase.
  Record t {E A} (x : C.t E A) : Type := New {
    P : Type;
    v : P -> A;
    r : forall p, Run.t x (v p) }.
  Arguments New {E A x} _ _ _.
  Arguments P {E A x} _.
  Arguments v {E A x} _ _.
  Arguments r {E A x} _ _.
End UseCase.

Module General.
  Fixpoint general {E A} (x : C.t E A) : UseCase.t x.
    destruct x as [A v | c | A B x f | A x1 x2 | A B x y].
    - refine (UseCase.New unit (fun _ => v) (fun _ => _)).
      apply Run.Ret.
    - refine (UseCase.New (Effect.answer E c) (fun a => a) (fun a => _)).
      apply (Run.Call c a).
    - destruct (general _ _ x) as [P_x v_x r_x].
      refine (let g_f := fun v_x => general _ _ (f v_x) in _).
      refine (
        UseCase.New {p_x : P_x & UseCase.P (g_f (v_x p_x))}
          (fun p =>
            let (p_x, p_f) := p in
            UseCase.v (g_f (v_x p_x)) p_f)
          (fun p => _)).
      destruct p as [p_x p_f].
      apply (Run.Let (r_x p_x) (UseCase.r (g_f (v_x p_x)) p_f)).
    - destruct (general _ _ x1) as [P1 v1 r1].
      destruct (general _ _ x2) as [P2 v2 r2].
      refine (
        UseCase.New (P1 + P2)
          (fun p =>
            match p with
            | inl p1 => v1 p1
            | inr p2 => v2 p2
            end)
          (fun p => _)).
      destruct p as [p1 | p2].
      + apply (Run.ChooseLeft (r1 p1)).
      + apply (Run.ChooseRight (r2 p2)).
    - destruct (general _ _ x) as [P_x v_x r_x].
      destruct (general _ _ y) as [P_y v_y r_y].
      refine (
        UseCase.New (P_x * P_y)
          (fun p =>
            let (p_x, p_y) := p in
            (v_x p_x, v_y p_y))
          (fun p => _)).
      destruct p as [p_x p_y].
      apply (Run.Join (r_x p_x) (r_y p_y)).
  Defined.
End General.
