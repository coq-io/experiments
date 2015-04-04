(** Attempts to solve the strictly positive issue. *)

Module One.
  Inductive t : Type -> Type :=
  | Ret : forall (A : Type), A -> t A
  | Double : forall (A : Type) (T : Type -> Type), t A -> t (T A).

  (*Definition test :=
    Double unit t (Ret unit tt).*)
End One.

Module Two.
  Inductive t (T : Type -> Type) : Type -> Type :=
  | Double : forall (A : Type), t T A -> t T (T A).
End Two.

Module Three.
  (*Inductive t : Type -> Type :=
  | Double : forall (A : Type), t A -> t (s A)
  with s : Type -> Type :=
  | Lift : forall (A : Type), t A -> s A.*)
End Three.
