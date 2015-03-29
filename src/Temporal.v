(** Experiments around temporal logic. *)
Require Import Io.All.

Import C.Notations.

(*Module Automata.
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
