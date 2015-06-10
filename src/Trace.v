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
  Inductive t {E} : forall {A}, C.t E A -> Trace.t E -> A -> Prop :=
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

(*Require Import JMeq.

  Fixpoint unicity {E A} (x : C.t E A) (t_x : Trace.t E) (v_x v'_x : A)
    (H : t x t_x v_x) (H' : t x t_x v'_x) : v_x = v'_x.
    apply JMeq_eq.
    destruct H.
    - exact (
        match H' in t x t_x v'_x return
          match x with
          | C.Ret _ v => JMeq v v'_x
          | _ => True
          end : Prop with
        | Ret _ _ => JMeq_refl
        | _ => I
        end).
    - exact (
        match H' in t x t_x v'_x return
          match t_x with
          | Trace.Call _ a => JMeq a v'_x
          | _ => True
          end : Prop with
        | Call _ _ => JMeq_refl
        | _ => I
        end).
    - generalize H; clear H.
      generalize H0; clear H0.
      refine (
        match H' in t x t_x v'_x return
          match x with
          | C.Let _ _ x f => t (f v_x) t_y v_y -> t x t_x v_x -> JMeq v_y v'_x
          | _ => True
          end : Prop with
        | Let _ _ _ _ _ _ _ _ _ _ => _
        | _ => I
        end).
      replace 
      apply (JMeq_trans (unicity) ()).
  Qed.*)
End Valid.
