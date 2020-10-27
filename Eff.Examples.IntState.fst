module Eff.Examples.IntState

module S = Eff.Signature

open Eff

(* Read and write effects *)

let read = S.Op "read" #unit #int
let write = S.Op "write" #int #unit

let r : S.sig = S.singleton read
let w : S.sig = S.singleton write
let rw : S.sig = r `S.union` w


(* Some examples of using algebraic operations *)

let ex1 () : Eff int rw=
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42; let _ = perform read () in
  perform write 42;
  perform read ()

let ex2 (c1:unit -> Eff int S.emp) 
        (c2:unit -> Eff int rw) 
        : Eff int rw =
  let v = (c1 () <: Eff int rw) in
  let w = c2 () in
  v + w

let ex3 (b:bool) 
        (c1:unit -> Eff int rw) 
        (c2:unit -> Eff int S.emp) 
        : Eff int rw =
  perform write 42;
  let v = (if b then c1 () else (c2 () <: Eff int rw)) in
  perform read ()


(* Some examples of handlers *)

(* Currently clunkier than desired, because the     *)
(* operation cases need to be defined on the repr   *)
(* when handling into a layered effect (e.g., Eff). *)

(* Discarding the write operation *)

let eff_discard_write_handler #a
  : eff_handler rw a r
  = fun op x k -> 
      match op with
      | S.Op "read" -> 
          Node read () (fun y -> k y)
      | S.Op "write" ->
          k ()

let discard_write_handler #a
  : handler rw a r
  = to_handler eff_discard_write_handler

(* Duplicating the write operation *)

let eff_dup_write_handler #a
  : eff_handler rw a rw
  = fun op x k -> 
      match op with
      | S.Op "read" -> 
          Node read () (fun y -> k y)
      | S.Op "write" ->
          Node write x (fun _ -> Node write x (fun _ -> k ()))

let dup_write_handler #a
  : handler rw a rw
  = to_handler eff_dup_write_handler

(* Logging reads (via write) *)

let eff_log_read_handler #a
  : eff_handler r a rw
  = fun op x k -> 
      match op with
      | S.Op "read" -> 
          Node read () (fun y -> Node write y (fun _ -> k y))

let log_read_handler #a
  : handler r a rw
  = to_handler eff_log_read_handler

(* The standard state handler *)

let eff_st_handler #a
  : eff_handler rw (int -> a * int) S.emp
  = fun op x k ->
      match op with
      | S.Op "read" -> 
          Leaf (fun s -> let (Leaf f) = k s in f s)
      | S.Op "write" ->
          Leaf (fun _ -> let (Leaf f) = k () in f x)

let st_handler #a
  : handler rw (int -> a * int) S.emp
  = to_handler eff_st_handler
