module Eff.Template.Equation.Test3

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


(* State equations using templates *)

let st_eq1 a : repr_equation a rw 
  = { 
      repr_vctx = [];
      repr_cctx = [unit];
      repr_lhs  = (fun vvars cvars -> Node read () (fun y ->
                                   Node write y (fun y' ->
                                   repr_cvar cvars 0 y')));
      repr_rhs  = (fun vvars cvars -> repr_cvar cvars 0 ())
    }

let st_eq2 a : repr_equation a rw
  = {
      repr_vctx = [int];
      repr_cctx = [int];
      repr_lhs  = (fun vvars cvars -> Node write (vvar vvars 0) (fun y ->
                                   Node read () (fun y' ->
                                   repr_cvar cvars 0 y')));
      repr_rhs  = (fun vvars cvars -> Node write (vvar vvars 0) (fun y ->
                                   repr_cvar cvars 0 (vvar vvars 0)))
    }

let st_eq3 a : repr_equation a rw
  = {
      repr_vctx = [int;int];
      repr_cctx = [unit];
      repr_lhs  = (fun vvars cvars -> Node write (vvar vvars 0) (fun y ->
                                   Node write (vvar vvars 1) (fun y' ->
                                   repr_cvar cvars 0 y')));
      repr_rhs  = (fun vvars cvars -> Node write (vvar vvars 1) (fun y ->
                                   repr_cvar cvars 0 y))
    }













(* ***************************** *)

let st_eq a : repr_equation a rw
  = {
      repr_vctx = [int;int;int];
      repr_cctx = [unit];
      repr_lhs  = (fun vvars cvars -> Node write (vvar vvars 0) (fun y ->
                                   Node write (vvar vvars 1) (fun y' ->
                                   Node write (vvar vvars 2) (fun y'' ->
                                   repr_cvar cvars 0 y''))));
      repr_rhs  = (fun vvars cvars -> Node write (vvar vvars 0) (fun y ->
                                   Node write (vvar vvars 2) (fun y' ->
                                   repr_cvar cvars 0 y')))
    }

open FStar.Tactics

let foo a 
  : Lemma (requires (repr_eq_to_prop (st_eq3 a)))
          (ensures  (repr_eq_to_prop (st_eq a))) by (norm [delta;zeta;primops;simplify;iota]; dump "foo")
  = ()




