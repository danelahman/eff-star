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
