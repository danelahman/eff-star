module Eff.Equation.Test

open Eff.Signature
open Eff.Template.Equation

module T = Eff.Template

open Eff

(* Read and write effects for integer state *)

let read = Op "read" #unit #int
let write = Op "write" #int #unit

let r : sig = singleton read
let w : sig = singleton write
let rw : sig = r `union` w


(* State equations using templates *)

let st_eq1 : equation rw 
  = { 
      vctx = [];
      cctx = [unit];
      lhs  = (fun vvars -> let y = T.perform read () in 
                        let y' = T.perform write y in
                        cvar 0 y');
      rhs  = (fun vvars -> cvar 0 ())
    }

let st_eq2 : equation rw
  = {
      vctx = [int];
      cctx = [int];
      lhs  = (fun vvars -> T.perform write (vvar vvars 0);
                        let y = T.perform read () in
                        cvar 0 y);
      rhs  = (fun vvars -> T.perform write (vvar vvars 0);
                        cvar 0 (vvar vvars 0))
    }

let st_eq3 : equation rw
  = {
      vctx = [int;int];
      cctx = [unit];
      lhs  = (fun vvars -> T.perform write (vvar vvars 0);
                        let y = T.perform write (vvar vvars 1) in
                        cvar 0 y);
      rhs  = (fun vvars -> let y = T.perform write (vvar vvars 1) in
                        cvar 0 y)
    }



(* ************************** *)


let st_eq : equation rw
  = {
      vctx = [int;int;int];
      cctx = [unit];
      lhs  = (fun vvars -> T.perform write (vvar vvars 0);
                        T.perform write (vvar vvars 1);
                        let y = T.perform write (vvar vvars 2) in
                        cvar 0 y);
      rhs  = (fun vvars -> T.perform write (vvar vvars 0);
                        let y = T.perform write (vvar vvars 2) in
                        cvar 0 y)
    }


(* ************************** *)

assume val t : Type0


let h1_raw : raw_eff_handler rw [] t rw []
  = fun op x k -> T.Node op x k

let h1 : eff_handler rw [] t rw []
  = (| h1_raw , eff_respects h1_raw () |)


let h2_raw : raw_eff_handler rw [] t rw [st_eq3]
  = fun op x k -> T.Node op x k

(*
let h2 : eff_handler rw [] t rw [st_eq3]
  = (| h2_raw , eff_respects h2_raw () |)
*)
