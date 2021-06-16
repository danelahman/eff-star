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

let h1 : eff_handler rw [] a rw [] = {
  eff_op_cases = (fun op x k -> T.Node op x k);
  eff_respects = ()
}

let h2 : eff_handler rw [] a rw [st_eq1;st_eq2;st_eq3] = {
  eff_op_cases = (fun op x k -> T.Node op x k);
  eff_respects = ()
}

let h3 : eff_handler rw [st_eq] a rw [st_eq1;st_eq2;st_eq3] = {
  eff_op_cases = (fun op x k -> T.Node op x k);
  eff_respects = ()
}

let h4 : eff_handler rw [st_eq;st_eq] a rw [st_eq1;st_eq2;st_eq3] = {
  eff_op_cases = (fun op x k -> T.Node op x k);
  eff_respects = () , ()
}

let h5 : eff_handler rw [st_eq] a rw [st_eq1;st_eq2;st_eq3] = {
  eff_op_cases = (fun op x k -> 
                    match op with
                    | read -> 
                      T.Node read x k
                    | write -> 
                      T.Node write (x+1) (fun _ -> 
                      T.Node write x k));
  eff_respects = ()
}

let h6 : eff_handler rw [st_eq1;st_eq2;st_eq3] a rw [st_eq1;st_eq2;st_eq3] = {
  eff_op_cases = (fun op x k -> 
                    match op with
                    | read -> 
                      T.Node read x k
                    | write -> 
                      T.Node write (x + 42) (fun _ -> 
                      T.Node write x k));
  eff_respects = () , ((), ())
}



(* ******* *)

let h7 : eff_handler rw [st_eq3] a rw [st_eq1;st_eq2;st_eq3] = {
  eff_op_cases = (fun op x k -> 
                    match op with
                    | read -> 
                      T.Node read x k
                    | write -> 
                      T.Node read () (fun y -> 
                      T.Node write (x + y) k));
  eff_respects = ()
}


module TT = FStar.Tactics

let h7' ()
  : squash (norm eff_norm_steps (to_respects_hypotheses a [st_eq1;st_eq2;st_eq3])
            ==>
            norm eff_norm_steps (eq_to_prop (to_inst_equation #a #rw #rw st_eq3 (
              (fun op x k -> 
                 match op with
                 | read -> 
                    T.Node read x k
                 | write -> 
                    T.Node read () (fun y -> 
                    T.Node write (x + y) k)))))) by (TT.norm []; TT.dump "foo")
   = ()

(*

Why does F*/SMT think that h7 is a corrrect handler???

Because the following equation doesn't seem to hold:

write' x (write' x' z)

=def=

read (y . write (x + y) (read y' . write (x' + y') z))

=

read (y . write (x + y) (write (x' + x + y) z))

=

read (y . write (x' + x + y) z)

=?=

read (y . write (x' + y) z)

=def=

write x' z

*)

let h8 : eff_handler rw [st_eq1;st_eq2;st_eq3] a rw [st_eq1;st_eq2;st_eq3] = {
  eff_op_cases = (fun op x k -> 
                    match op with
                    | read -> 
                      T.Node read x k
                    | write -> 
                      T.Node write 42 k);
  eff_respects = () , ((), ())
}

(*

Again, why does F*/SMT think this is a correct handler?

*)
