(** Small examples for the Getting started page of Coq.io. *)
Require Import Coq.Lists.List.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.

Import ListNotations.
Import C.Notations.

(** Display the content of a file. *)
Definition cat (argv : list LString.t) : C.t System.effect unit :=
  match argv with
  | [_; file_name] =>
    let! content := System.read_file file_name in
    match content with
    | None => System.log (LString.s "Cannot read the file.")
    | Some content => System.log content
    end
  | _ => System.log (LString.s "One parameter expected.")
  end.

Definition main := Extraction.launch cat.
Extraction "extraction/main" main.
