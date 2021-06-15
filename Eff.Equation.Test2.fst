module Eff.Equation.Test2

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

let h1_raw : handler_raw rw [] a rw []
  = fun op x k -> let y = perform op x in k y
  
let h1 : handler rw [] a rw []
  = (| h1_raw , () |)

let h2_raw : handler_raw rw [] a rw [st_eq3]
  = fun op x k -> let y = perform op x in k y

let h2 : handler rw [] a rw [st_eq3]
  = (| h2_raw , () |)

let h3_raw : handler_raw rw [] a rw [st_eq2]
  = fun op x k -> let y = perform op x in k y

let h3 : handler rw [] a rw [st_eq2]
  = (| h3_raw , () |)

let h4_raw : handler_raw rw [st_eq] a rw [st_eq3]
  = fun op x k -> let y = perform op x in k y

(*
let h4 : handler rw [st_eq] a rw [st_eq3]
  = (| h4_raw , ((fun _ -> ()) , ()) |)

let h5_raw : handler_raw rw [st_eq;st_eq] a rw [st_eq3]
  = fun op x k -> let y = perform op x in k y

let h5 : handler rw [st_eq;st_eq] a rw [st_eq3]
  = (| h5_raw , ((fun () -> ()) , 
                ((fun () -> ()) , 
                 ())) |)
*)
