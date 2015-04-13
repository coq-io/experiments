Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import FunctionNinjas.All.
Require Import ListPlus.All.

Import ListNotations.

Module Effect.
  Record t := New {
    command : Type;
    answer : command -> Type }.
End Effect.

Module Model.
  Record t (E : Effect.t) (S : Type) := New {
    condition : Effect.command E -> S -> bool;
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

  Fixpoint is_not_stuck {E S} (m : Model.t E S) (x : Choose.t E) (s : S)
    : bool :=
    match x with
    | Ret => true
    | Call c _ => Model.condition m c s
    | Choose x1 x2 => orb (is_not_stuck m x1 s) (is_not_stuck m x2 s)
    end.

  Fixpoint aux {E S} (m : Model.t E S) (post : S -> bool) (x : Choose.t E)
    (s : S) : bool :=
    match x with
    | Ret => post s
    | Call c h =>
      if Model.condition m c s then
        let a := Model.answer m c s in
        let s := Model.state m c s in
        andb (is_not_stuck m (h a) s) (aux m post (h a) s)
      else
        true
    | Choose x1 x2 => andb (aux m post x1 s) (aux m post x2 s)
    end.

  Definition check {E S} (m : Model.t E S) (post : S -> bool) (x : Choose.t E)
    (s : S) : bool :=
    andb (is_not_stuck m x s) (aux m post x s).
End Choose.

Module Examples.
  Definition S := bool.

  Module Command.
    Inductive t :=
    | Lock
    | Unlock.
  End Command.

  Definition E : Effect.t :=
    Effect.New Command.t (fun _ => unit).

  Definition ret : Sequential.t E :=
    Sequential.Ret.

  Definition lock (h : Sequential.t E) : Sequential.t E :=
    Sequential.Call (E := E) Command.Lock (fun _ => h).

  Definition unlock (h : Sequential.t E) : Sequential.t E :=
    Sequential.Call (E := E) Command.Unlock (fun _ => h).

  Definition condition (c : Effect.command E) (s : S) : bool :=
    match (c, s) with
    | (Command.Lock, false) | (Command.Unlock, true) => true
    | (Command.Lock, true) | (Command.Unlock, false) => false
    end.

  Definition answer (c : Effect.command E) (s : S) : Effect.answer E c :=
    tt.

  Definition state (c : Effect.command E) (s : S) : S :=
    match c with
    | Command.Lock => true
    | Command.Unlock => false
    end.

  Definition m : Model.t E S :=
    Model.New condition answer state.

  Fixpoint ex1 (n : nat) : Concurrent.t E :=
    match n with
    | O => []
    | Datatypes.S n =>
      (lock @@
      unlock @@
      ret) :: ex1 n
    end.

  Definition is_ex1_ok : bool :=
    Choose.check m (fun _ => true) (Choose.compile @@ ex1 9) false.

  (* Time Compute is_ex1_ok. *)
End Examples.

Module Increment.
  Definition S := nat.

  Module Command.
    Inductive t :=
    | Read
    | Write (s : S).
  End Command.

  Definition E : Effect.t :=
    Effect.New Command.t (fun c =>
      match c with
      | Command.Read => S
      | Command.Write _ => unit
      end).

  Definition ret : Sequential.t E :=
    Sequential.Ret.

  Definition read (h : S -> Sequential.t E) : Sequential.t E :=
    Sequential.Call (E := E) Command.Read h.

  Definition write (s : S) (h : Sequential.t E) : Sequential.t E :=
    Sequential.Call (E := E) (Command.Write s) (fun _ => h).

  Definition condition (c : Effect.command E) (s : S) : bool :=
    true.

  Definition answer (c : Effect.command E) (s : S) : Effect.answer E c :=
    match c with
    | Command.Read => s
    | Command.Write _ => tt
    end.

  Definition state (c : Effect.command E) (s : S) : S :=
    match c with
    | Command.Read => s
    | Command.Write s => s
    end.

  Definition m : Model.t E S :=
    Model.New condition answer state.

  Definition process : Sequential.t E :=
    read (fun s =>
    write (s + 1)
    ret).

  Definition post (n : nat) (s : S) : bool :=
    beq_nat n s.

  Definition result (n : nat) : bool :=
    Choose.check m (post n) (Choose.compile @@ List.repeat process n) 0.
End Increment.

Module AtomicIncrement.
  Definition S := nat.

  Module Command.
    Inductive t :=
    | Increment.
  End Command.

  Definition E : Effect.t :=
    Effect.New Command.t (fun c =>
      match c with
      | Command.Increment => unit
      end).

  Definition ret : Sequential.t E :=
    Sequential.Ret.

  Definition increment (h : Sequential.t E) : Sequential.t E :=
    Sequential.Call (E := E) Command.Increment (fun _ => h).

  Definition condition (c : Effect.command E) (s : S) : bool :=
    true.

  Definition answer (c : Effect.command E) (s : S) : Effect.answer E c :=
    match c with
    | Command.Increment => tt
    end.

  Definition state (c : Effect.command E) (s : S) : S :=
    match c with
    | Command.Increment => s + 1
    end.

  Definition m : Model.t E S :=
    Model.New condition answer state.

  Definition process : Sequential.t E :=
    increment
    ret.

  Definition post (n : nat) (s : S) : bool :=
    beq_nat n s.

  Definition result (n : nat) : bool :=
    Choose.check m (post n) (Choose.compile @@ List.repeat process n) 0.
End AtomicIncrement.

Module SimpleChannel.
  Definition S := option nat.

  Module Command.
    Inductive t :=
    | Send (x : nat)
    | Receive.
  End Command.

  Definition E : Effect.t :=
    Effect.New Command.t (fun c =>
      match c with
      | Command.Send _ => unit
      | Command.Receive => nat
      end).

  Definition ret : Sequential.t E :=
    Sequential.Ret.

  Definition send (n : nat) (h : Sequential.t E) : Sequential.t E :=
    Sequential.Call (E := E) (Command.Send n) (fun _ => h).

  Definition receive (h : nat -> Sequential.t E) : Sequential.t E :=
    Sequential.Call (E := E) Command.Receive h.

  Definition condition (c : Effect.command E) (s : S) : bool :=
    match (c, s) with
    | (Command.Send _, None) | (Command.Receive, Some _) => true
    | (Command.Send _, Some _) | (Command.Receive, None) => false
    end.

  Definition answer (c : Effect.command E) (s : S) : Effect.answer E c :=
    match c with
    | Command.Send _ => tt
    | Command.Receive =>
      match s with
      | None => 0
      | Some n => n
      end
    end.

  Definition state (c : Effect.command E) (s : S) : S :=
    match c with
    | Command.Send n => Some n
    | Command.Receive => None
    end.

  Definition m : Model.t E S :=
    Model.New condition answer state.

  Definition ex : Concurrent.t E :=
    [receive (fun _ => ret); send 12 ret].

  Definition result : bool :=
    Choose.check m (fun _ => true) (Choose.compile ex) (None).
End SimpleChannel.

(** See `spin/database.spin`. *)
Module Database.
  Record S := New {
    holder : nat;
    up : list bool;
    ack : list nat }.

  Definition init (n : nat) : S :=
    New n (List.repeat false n) (List.repeat 0 n).

  Module Command.
    Inductive t :=
    | UpdateSend (id : nat)
    | ReceiveAck (id : nat)
    | Receive (id : nat)
    | Ack.
  End Command.

  Definition E : Effect.t :=
    Effect.New Command.t (fun c => unit).

  Definition condition (n : nat) (c : Effect.command E) (s : S) : bool :=
    match c with
    | Command.UpdateSend id => beq_nat id (holder s)
    | Command.ReceiveAck id => beq_nat (List.nth id (ack s) n) (n - 1)
    | Command.Receive id =>
      andb (List.nth id (up s) false) (
        match nat_compare (holder s) n with
        | Lt => true
        | _ => false
        end)
    | Command.Ack => true
    end.

  Definition answer (c : Effect.command E) (s : S) : Effect.answer E c :=
    tt.

  Fixpoint list_udpate {A} (l : list A) (n : nat) (x : A) : list A :=
    match (l, n) with
    | ([], _) => []
    | (_ :: l, O) => x :: l
    | (x' :: l, Datatypes.S n) => x' :: list_udpate l n x
    end.

  Definition state (n : nat) (c : Effect.command E) (s : S) : S :=
    match c with
    | Command.UpdateSend id => New id (List.repeat true n) (ack s)
    | Command.ReceiveAck id => New n (up s) (list_udpate (ack s) id 0)
    | Command.Receive id => New (holder s) (list_udpate (up s) id false) (ack s)
    | Command.Ack =>
      let a := List.nth (holder s) (ack s) 0 in
      New (holder s) (up s) (list_udpate (ack s) (holder s) (a + 1))
    end.

  Definition m (n : nat) : Model.t E S :=
    Model.New (condition n) answer (state n).

  Definition process_write (id : nat) : Sequential.t E :=
    Sequential.Call (E := E) (Command.UpdateSend id) (fun _ =>
    Sequential.Call (E := E) (Command.ReceiveAck id) (fun _ =>
    Sequential.Ret)).

  Definition process_read (id : nat) : Sequential.t E :=
    Sequential.Call (E := E) (Command.Receive id) (fun _ =>
    Sequential.Call (E := E) Command.Ack (fun _ =>
    Sequential.Ret)).

  Fixpoint processes_read (n : nat) : Concurrent.t E :=
    match n with
    | O => []
    | Datatypes.S n => process_read n :: processes_read n
    end.

  Definition ex (n : nat) : Concurrent.t E :=
    process_write n :: processes_read n.

  Definition result (n : nat) : bool :=
    Choose.check (m (n + 1)) (fun _ => true) (Choose.compile @@ ex n) (init (n + 1)).
End Database.

(** * Extraction *)
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.

Import C.Notations.

Definition result (argv : list LString.t) : C.t System.effect unit :=
  (* if Examples.is_ex1_ok then *)
  (* if Increment.result 2 then *)
  (* if AtomicIncrement.result 11 then *)
  (* if SimpleChannel.result then *)
  if Database.result 0 then
    System.log (LString.s "OK")
  else
    System.log (LString.s "error").

Definition main := Extraction.run result.
Extraction "extraction/main" main.
