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

(** If the package uses the MIT license. *)
Definition is_MIT (package : LString.t) : C.t System.effect bool :=
  let! license :=
    System.eval [LString.s "opam"; LString.s "show";
      LString.s "--field=license"; package] in
  match license with
  | Some (0%Z, license, _) =>
    ret (LString.eqb (LString.trim license) (LString.s "MIT"))
  | _ => ret false
  end.

(** Filter the packages using the MIT license (sequential version). *)
Fixpoint filter_MIT_seq (packages : list LString.t)
  : C.t System.effect (list LString.t) :=
  match packages with
  | [] => ret []
  | package :: packages =>
    do! System.log (LString.s "Checking " ++ package) in
    let! is_ok := is_MIT package in
    let! packages := filter_MIT_seq packages in
    if is_ok then
      ret (package :: packages)
    else
      ret packages
  end.

(** Filter the packages using the MIT license (concurrent version). *)
Fixpoint filter_MIT_concur (packages : list LString.t)
  : C.t System.effect (list LString.t) :=
  match packages with
  | [] => ret []
  | package :: packages =>
    let! is_ok_packages := join (is_MIT package) (filter_MIT_concur packages) in
    let (is_ok, packages) := is_ok_packages in
    if is_ok then
      ret (package :: packages)
    else
      ret packages
  end.

(** Get the list of packages using the MIT license. *)
Definition list_MIT_packages (argv : list LString.t) : C.t System.effect unit :=
  let! packages :=
    System.eval [LString.s "opam"; LString.s "search"; LString.s "--short"] in
  match packages with
  | Some (0%Z, packages, _) =>
    let packages := LString.split packages LString.Char.n in
    let packages := List.map LString.trim packages in
    let! packages := filter_MIT_seq packages in
    (* let! packages := filter_MIT_concur packages in *)
    System.log (LString.join (LString.s " ") packages)
  | _ => System.log (LString.s "Failed to list the OPAM packages.")
  end.

(** Do two sleep operations. *)
Definition double_sleep (argv : list LString.t) : C.t System.effect unit :=
  let! _ : unit * unit :=
    join
      (let! _ := System.eval [LString.s "sleep"; LString.s "4"] in
      System.log (LString.s "Task of 4 seconds ended."))
      (let! _ := System.eval [LString.s "sleep"; LString.s "2"] in
      System.log (LString.s "Task of 2 seconds ended.")) in
  ret tt.

(** Do two sleep operations (sequential). *)
Definition double_sleep_seq (argv : list LString.t) : C.t System.effect unit :=
  let! _ := System.eval [LString.s "sleep"; LString.s "4"] in
  do! System.log (LString.s "Task of 4 seconds ended.") in
  let! _ := System.eval [LString.s "sleep"; LString.s "2"] in
  System.log (LString.s "Task of 2 seconds ended.").

Definition main := Extraction.launch double_sleep_seq.
Extraction "extraction/main" main.
