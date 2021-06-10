module Eff.Template.Equation.Test2

open Eff.Signature
open Eff.Template
open Eff.Template.Equation
open Eff.Template.Equiv

(* Read and write effects for integer state *)

let read = Op "read" #unit #int
let write = Op "write" #int #unit

let r : sig = singleton read
let w : sig = singleton write
let rw : sig = r `union` w


(* Some dummy equations *)

unfold
let eq1 a x (z:unit -> template_repr a rw) 
  = Node write x z `equiv` z ()

unfold
let eq2 a x y (z:unit -> template_repr a rw) 
  = Node write x z `equiv` Node write y z


(* Some experiments re proving equations from eq1 and eq2 *)

assume val t : Type

open FStar.Tactics

let f (z:unit -> template_repr t rw) 
  : Pure unit 
         (requires (forall a x z . eq1 a x z))
         (ensures  (fun _ -> Node write 42 z `equiv` Node write 24 z))
  = ()

let g (z:unit -> template_repr t rw) 
  : Pure unit 
         (requires (forall a x z . eq1 a x z))
         (ensures  (fun _ -> (Node read () (fun _ -> Node write 42 z)) 
                          `equiv` 
                          (Node read () (fun _ -> Node write 24 z))))
  = ()

let h (z:unit -> template_repr t rw) 
  : Pure unit 
         (requires (forall a x z . eq1 a x z))
         (ensures  (fun _ -> Node read () (fun _ -> Node read () (fun _ -> Node write 42 z))
                          `equiv`
                          Node read () (fun _ -> Node read () (fun _ -> Node write 24 z))))
  = ()

let k (z:unit -> template_repr t rw) 
  : Pure unit 
         (requires (forall a x z . eq1 a x z))
         (ensures  (fun _ -> Node write 24 (fun _ -> Node read () (fun _ -> Node read () ((fun _ -> Node write 42 z))))
                          `equiv`
                          Node read () (fun _ -> Node read () (fun _ -> Node write 24 z))))
  = ()

[@ expect_failure]
let k' (z:unit -> template_repr t rw) 
  : Pure unit 
         (requires (forall a x y z . eq2 a x y z)) // eq2 doesn't justify discarding writes altogether!
         (ensures  (fun _ -> Node write 24 (fun _ -> Node read () (fun _ -> Node read () ((fun _ -> Node write 42 z))))
                          `equiv`
                          Node read () (fun _ -> Node read () (fun _ -> Node write 24 z))))
  = ()


