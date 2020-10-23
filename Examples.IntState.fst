module Examples.IntState

module S = Eff.Signature

open Eff

let read = S.Op "read" #unit #int
let write = S.Op "write" #int #unit

let r : S.sig = S.singleton read
let w : S.sig = S.singleton write
let rw : S.sig = r `S.union` w

let test1 () : Eff int rw =
  perform write 42;
  perform read ()

let test2 (c1:unit -> Eff int S.emp) 
         (c2:unit -> Eff int rw) 
       : Eff int rw =
  let v = c1 () in
  let w = c2 () in
  v + w

let test3 (b:bool) 
         (c1:unit -> Eff int rw) 
         (c2:unit -> Eff int S.emp) 
       : Eff int rw =
  perform write 42;
  let v = (if b then c1 () else c2 ()) in
  perform read ()

let eff_discard_write_handler #a
  : eff_handler rw a rw
  = fun op x k -> 
      match op with
      | S.Op "read" -> 
          Node op x (fun y -> k y)
      | S.Op "write" ->
          k ()

let discard_write_handler #a
  : handler rw a rw
  = fun op x k ->
      Eff?.reflect (
        eff_discard_write_handler #a op x 
          (fun y -> reify (k y)))
