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

let ex1 () : Eff int rw =
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


(* Some examples of effect handlers for {r,w,rw} signatures *)

(* Discarding the write operation *)

let discard_write_handler #a
  : handler rw a r
  = fun op x k ->
      match op with
      | S.Op "read" -> 
          let x = perform read () in
          k x
      | S.Op "write" -> 
          k ()


(* Duplicating the write operation *)

let dup_write_handler #a
  : handler rw a rw
  = fun op x k -> 
      match op with
      | S.Op "read" -> 
          let x = perform read () in 
          k x
      | S.Op "write" ->
          perform write x;
          perform write x;
          k ()


(* Logging reads (via writes) *)

let log_read_handler #a
  : handler r a rw
  = fun op x k -> 
      match op with
      | S.Op "read" -> 
          let x = perform read () in
          perform write x;
          k x


(* The standard state handler (in two flavours) *)

(* Returning stateful functions in the Eff effect to make effects match up in `let`s *)
let st_handler1 #a
  : handler rw (int -> Eff (a * int) S.emp) S.emp
  = fun op x k ->
      match op with
      | S.Op "read" -> 
          fun s -> let f = k s in f s
      | S.Op "write" ->
          fun s -> let f = k () in f x

(* Using explicit coercions between `Eff a S.emp` and `Tot a` *)
let st_handler2 #a
  : handler rw (int -> a * int) S.emp
  = fun op x k ->
      match op with
      | S.Op "read" -> 
          fun s -> let f = emp_pure (fun _ -> k s) in f s
      | S.Op "write" ->
          fun s -> let f = emp_pure (fun x -> k x) in f x


(* Handling code *)

let st_handle1 #a (f:unit -> Eff a rw) 
  : Eff (int -> Eff (a * int) S.emp) S.emp
  = handle f st_handler1 (fun x s -> x , s)

let st_handle1' #a (f:unit -> Eff a rw) 
  : Eff (int -> a * int) S.emp
  = fun s -> emp_pure (fun _ -> st_handle1 f s)

let st_handle1'' #a (f:unit -> Eff a rw) 
  : int -> a * int
  = emp_pure (fun _ -> st_handle1' f)

let st_handle2 #a (f:unit -> Eff a rw) 
  : Eff (int -> a * int) S.emp
  = handle f st_handler2 (fun x s -> x , s)

let st_handle2' #a (f:unit -> Eff a rw) 
  : int -> a * int
  = emp_pure (fun _ -> st_handle2 f)


(* Experimenting with equations *)

let f (z:unit -> eff_repr int rw) 
  : Pure unit 
         (requires (
           forall x (z:unit -> eff_repr int rw) . {:pattern (Node write x z)} Node write x z == z ()))
         (ensures (fun _ ->
           Node write 42 z == Node write 24 z))
  = admit ()
  
assume val write_ignore (x:int) (z:unit -> eff_repr int rw)
  : Lemma (Node write x z == z ())
          [SMTPat (Node write x z)]

let g (z:unit -> eff_repr int rw) 
  : Lemma (Node write 42 z == Node write 24 z)
  = admit ()

let g' (z:unit -> eff_repr int rw) 
  : Lemma (Node write 42 z == Node write 24 z)
  = write_ignore 42 z;
    write_ignore 24 z

let g'' (z:unit -> eff_repr int rw) 
  : Lemma (Node read () (fun _ -> Node write 42 z) == Node read () (fun _ -> Node write 24 z))
  = write_ignore 42 z;
    write_ignore 24 z
