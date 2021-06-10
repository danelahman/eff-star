module Eff.Equations.Test

open Eff.Equations
open Eff.Signature
open Eff.Template

(* Read and write effects for integer state *)

let read = Op "read" #unit #int
let write = Op "write" #int #unit

let r : sig = singleton read
let w : sig = singleton write
let rw : sig = r `union` w


(* State equations using templates *)

let st_eq1 a : equation a rw 
  = { 
      vctx = [];
      cctx = [unit];
      lhs  = (fun vvars cvars -> let y = perform read () in 
                              let y' = perform write y in
                              cvar cvars 0 y');
      rhs  = (fun vvars cvars -> cvar cvars 0 ())
    }

let st_eq2 a : equation a rw
  = {
      vctx = [int];
      cctx = [int];
      lhs  = (fun vvars cvars -> perform write (vvar vvars 0);
                              let y = perform read () in
                              cvar cvars 0 y);
      rhs  = (fun vvars cvars -> perform write (vvar vvars 0);
                              cvar cvars 0 (vvar vvars 0))
    }

let st_eq3 a : equation a rw
  = {
      vctx = [int;int];
      cctx = [unit];
      lhs  = (fun vvars cvars -> perform write (vvar vvars 0);
                              let y = perform write (vvar vvars 1) in
                              cvar cvars 0 y);
      rhs  = (fun vvars cvars -> let y = perform write (vvar vvars 1) in
                              cvar cvars 0 y)
    }










(* ********************** *)
(* ********************** *)
(* ********************** *)

(*
open FStar.Tactics

let foo a ops (z:int -> template_repr a ops)
  : Lemma (to_cvars #[int] [RCVar int z] == [CVar int (reflect_cont #a #int #ops z)])
  = ()

let st_eq a : equation a rw
  = {
      vctx = [int;int;int];
      cctx = [unit];
      lhs  = (fun vvars cvars -> perform write (vvar vvars 0);
                              perform write (vvar vvars 1);
                              let y = perform write (vvar vvars 2) in
                              cvar cvars 0 y);
      rhs  = (fun vvars cvars -> perform write (vvar vvars 0);
                              let y = perform write (vvar vvars 2) in
                              cvar cvars 0 y)
    }

let prop_st_eq3 a 
  : prop
  = eq_to_prop (to_repr_eq (st_eq3 a))

let prop_st_eq a 
  : prop
  = eq_to_prop (to_repr_eq (st_eq a))

(*
let bar a 
  : Lemma (to_repr_eq (st_eq3 a) == to_repr_eq (st_eq a)) by (norm [delta; nbe]; dump "bar")
  = ()

let bar a : Lemma (requires (prop_st_eq3 a))
                  (ensures  (prop_st_eq a)) by (norm [delta; nbe]; dump "foo")
  = ()
*)
*)
