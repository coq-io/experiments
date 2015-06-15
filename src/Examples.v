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
  | _ => System.log (LString.s "Expected one parameter.")
  end.

Require Import Coq.ZArith.ZArith.

(** A wrapper for the `uname` command. *)
Definition uname (argv : list LString.t) : C.t System.effect unit :=
  let! os := System.eval [LString.s "uname"; LString.s "-o"] in
  let! machine := System.eval [LString.s "uname"; LString.s "-m"] in
  match (os , machine) with
  | (Some (0%Z, os, _), Some (0%Z, machine, _)) =>
    do! System.log (LString.s "OS: " ++ LString.trim os) in
    System.log (LString.s "Machine: " ++ LString.trim machine)
  | _ => ret tt
  end.

Definition main := Extraction.launch uname.
Extraction "extraction/main" main.
