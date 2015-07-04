(** An example of non-terminating use case. *)
Require Import Coq.Lists.Streams.
Require Import Io.All.
Require Import ListString.All.

Import C.I.Notations.

(*Inductive t : Type :=
| Prnt
| A.

Definition to_bool (x : t) : bool :=
  match x with
  | Prnt => true
  | B => false
  end.*)

Module Command.
  Inductive t : Set :=
  | Print (message : LString.t)
  | Read.

  Definition answer (c : t) : Type :=
    match c with
    | Print _ => unit
    | Read => option LString.t
    end.
End Command.

Definition E : Effect.t := {|
  Effect.command := Command.t;
  Effect.answer := Command.answer |}.

CoFixpoint say_hi : C.I.t E unit :=
  ido! C.I.call E (Command.Print (LString.s "Say hi:")) in
  ilet! hi := C.I.call E Command.Read in
  match hi with
  | None => C.I.ret tt
  | Some hi =>
    if LString.eqb hi (LString.s "hi") then
      C.I.ret tt
    else
      say_hi
  end.

Module Run.
  Lemma string_not_eqb_implies_not_eq (x y : LString.t)
    : LString.eqb x y = false -> x <> y.
    intros H_eqb H_eq.
    rewrite H_eq in H_eqb.
    rewrite LString.eqb_same_is_eq in H_eqb.
    congruence.
  Qed.

  Lemma string_not_eq_implies_not_eqb {x y : LString.t}
    : x <> y -> LString.eqb x y = false.
    intro H_neq.
    case_eq (LString.eqb x y); intro H_eqb.
    - destruct (H_neq (LString.eqb_implies_eq _ _ H_eqb)).
    - reflexivity.
  Qed.

  CoFixpoint say_hi_infinite
    (wrong_answers : Stream {s : LString.t | s <> LString.s "hi"})
    : Run.I.t say_hi tt.
    destruct wrong_answers as [[s H_s] wrong_answers].
    rewrite (C.I.unfold_eq say_hi).
    eapply Run.I.Let. apply (Run.I.Call (E := E) (Command.Print _) tt).
    eapply Run.I.Let. apply (Run.I.Call (E := E) Command.Read (Some s)).
    fold say_hi; simpl in *; rewrite (string_not_eq_implies_not_eqb H_s).
    apply (say_hi_infinite wrong_answers).
  Defined.
End Run.
