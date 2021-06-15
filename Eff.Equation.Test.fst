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

let st_eq1 : template_equation rw 
  = { 
      tvctx = [];
      tcctx = [unit];
      tlhs  = (fun vvars -> T.Node read () (fun y ->
                         T.Node write y (fun y' ->
                         T.Leaf (cvar 0 y'))));
      trhs  = (fun vvars -> T.Leaf (cvar 0 ()))
    }

let st_eq2 : template_equation rw
  = {
      tvctx = [int];
      tcctx = [int];
      tlhs  = (fun vvars -> T.Node write (vvar vvars 0) (fun y ->
                         T.Node read () (fun y' ->
                         T.Leaf (cvar 0 y'))));
      trhs  = (fun vvars -> T.Node write (vvar vvars 0) (fun y ->
                         T.Leaf (cvar 0 (vvar vvars 0))))
    }

let st_eq3 : template_equation rw
  = {
      tvctx = [int;int];
      tcctx = [unit];
      tlhs  = (fun vvars -> T.Node write (vvar vvars 0) (fun y ->
                         T.Node write (vvar vvars 1) (fun y' ->
                         T.Leaf (cvar 0 y'))));
      trhs  = (fun vvars -> T.Node write (vvar vvars 1) (fun y ->
                         T.Leaf (cvar 0 y)))
    }



(* ************************** *)


let st_eq : template_equation rw
  = {
      tvctx = [int;int;int];
      tcctx = [unit];
      tlhs  = (fun vvars -> T.Node write (vvar vvars 0) (fun y ->
                         T.Node write (vvar vvars 1) (fun y' ->
                         T.Node write (vvar vvars 2) (fun y'' ->
                         T.Leaf (cvar 0 y'')))));
      trhs  = (fun vvars -> T.Node write (vvar vvars 0) (fun y ->
                         T.Node write (vvar vvars 2) (fun y' ->
                         T.Leaf (cvar 0 y'))))
    }


(* ************************** *)

assume val a : Type

let h1_raw : raw_eff_handler rw [] a rw []
  = fun op x k -> T.Node op x k

let h1 : eff_handler rw [] a rw []
  = (| h1_raw , eff_respects |)

let h2_raw : raw_eff_handler rw [] a rw [st_eq3]
  = fun op x k -> T.Node op x k

let h2 : eff_handler rw [] a rw [st_eq3]
  = (| h2_raw , eff_respects |)


let h3_raw : raw_eff_handler rw [st_eq] a rw [st_eq3]
  = fun op x k -> T.Node op x k

let h3 : eff_handler rw [st_eq] a rw [st_eq3]
  = (| h3_raw , eff_respects |)


let h4_raw : raw_eff_handler rw [] a rw [st_eq2]
  = fun op x k -> T.Node op x k

let h4 : eff_handler rw [] a rw [st_eq2]
  = (| h4_raw , eff_respects |)


