(** Experiments around temporal logic. *)
Require Import Io.All.

Import C.Notations.

(*
(** Compilation to automata. *)
Module Automata.
  Definition t (S : Type) := S -> S -> Prop.

  Definition empty {S : Type} : t S :=
    fun _ _ =>
      False.

  Definition call {S : Type} (s1 s2 : S) : t S :=
    fun s'1 s'2 =>
      s1 = s'1 /\ s2 = s'2.

  Definition union {S : Type} (a1 a2 : t S) : t S :=
    fun s1 s2 =>
      a1 s1 s2 \/ a2 s1 s2.
End Automata.

Fixpoint run {E : Effect.t} {S A : Type}
  (update : forall (c : Effect.command E), S -> Effect.answer E c * S)
  (x : C.t E A) (s : S) : A * S * Automata.t S :=
  match x with
  | C.Ret _ x => (x, s, Automata.empty)
  | C.Call c =>
    let (x, s') := update c s in
    (x, s', Automata.call s s')
  | C.Let _ _ x f =>
    match run update x s with
    | (x, s, a_x) =>
      match run update (f x) s with
      | (y, s, a_y) => (y, s, Automata.union a_x a_y)
      end
    end
  (* | C.Join _ _ x y => *)
  end.*)

(** CCS and compilation to computations. *)
Module CCS.
  Module Action.
    Record t (A : Type) := New {
      eqb : A -> A -> bool }.
    Arguments eqb {A} _ _ _.

    Definition rename {A : Type} (action : t A) (b a a' : A) : A :=
      if eqb action b a then
        a'
      else
        a.
  End Action.

  Module Trace.
    Inductive t (A : Type) :=
    | Empty : t A
    | Do : A -> t A -> t A
    | Join : t A -> t A -> t A
    | First : t A -> t A -> t A.
    Arguments Empty {A}.
    Arguments Do {A} _ _.
    Arguments Join {A} _ _.
    Arguments First {A} _ _.
  End Trace.

  Inductive t {A : Type} (action : Action.t A) : Type :=
  | Empty : t action
  | Do : A -> t action -> t action
  | Join : t action -> t action -> t action
  | First : t action -> t action -> t action.
  Arguments Empty {A action}.
  Arguments Do {A action} _ _.
  Arguments Join {A action} _ _.
  Arguments First {A action} _ _.

  Fixpoint rename {A : Type} {action : Action.t A} (x : t action) (a a' : A)
    : t action :=
    match x with
    | Empty => x
    | Do b x => Do (Action.rename action b a a') (rename x a a')
    | Join x y => Join (rename x a a') (rename y a a')
    | First x y => First (rename x a a') (rename y a a')
    end.

  Fixpoint restrict {A : Type} {action : Action.t A} (x : t action) (a : A)
    : t action :=
    match x with
    | Empty => x
    | Do b x =>
      let x := restrict x a in
      if Action.eqb action a b then
        x
      else
        Do b x
    | Join x y => Join (restrict x a) (restrict y a)
    | First x y => First (restrict x a) (restrict y a)
    end.

  Fixpoint run {A : Type} {action : Action.t A} (x : t action) : Trace.t A :=
    match x with
    | Empty => Trace.Empty
    | Do a x => Trace.Do a (run x)
    | Join x y => Trace.Join (run x) (run y)
    | First x y => Trace.First (run x) (run y)
    end.

  Definition effect (A : Type) : Effect.t :=
    Effect.New A (fun _ => unit).

  Fixpoint compile {A : Type} {action : Action.t A} (x : t action)
    : C.t (effect A) unit :=
    match x with
    | Empty => ret tt
    | Do a x =>
      do! call (effect A) a in
      compile x
    | Join x y =>
      let! _ := join (compile x) (compile y) in
      ret tt
    | First x y =>
      let! _ := choose (compile x) (compile y) in
      ret tt
    end.
End CCS.

(** Definition of the LTL logic for the computations. *)
Module LTL.
  Definition t {E : Effect.t} {A : Type} :=
    C.t E A -> Prop.

  Module Event.
    Record t (E : Effect.t) := New {
      command : Effect.command E;
      answer : Effect.answer E command }.
    Arguments command {E} _.
    Arguments answer {E} _.
  End Event.
End LTL.
