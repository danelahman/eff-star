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

let st_eq1 : template_equation rw 
  = { 
      tvctx = [];
      tcctx = [unit];
      tlhs  = (fun vvars -> Node read () (fun y ->
                         Node write y (fun y' ->
                         Leaf (cvar 0 y'))));
      trhs  = (fun vvars -> Leaf (cvar 0 ()))
    }

let st_eq2 : template_equation rw
  = {
      tvctx = [int];
      tcctx = [int];
      tlhs  = (fun vvars -> Node write (vvar vvars 0) (fun y ->
                         Node read () (fun y' ->
                         Leaf (cvar 0 y'))));
      trhs  = (fun vvars -> Node write (vvar vvars 0) (fun y ->
                         Leaf (cvar 0 (vvar vvars 0))))
    }

let st_eq3 : template_equation rw
  = {
      tvctx = [int;int];
      tcctx = [unit];
      tlhs  = (fun vvars -> Node write (vvar vvars 0) (fun y ->
                         Node write (vvar vvars 1) (fun y' ->
                         Leaf (cvar 0 y'))));
      trhs  = (fun vvars -> Node write (vvar vvars 1) (fun y ->
                         Leaf (cvar 0 y)))
    }








(* ***************************** *)

let st_eq : template_equation rw
  = {
      tvctx = [int;int;int];
      tcctx = [unit];
      tlhs  = (fun vvars -> Node write 42 (fun _ -> 
                         Node write (vvar vvars 0) (fun y ->
                         Node write 42 (fun _ -> 
                         Node write (vvar vvars 1) (fun y' ->
                         Node write 42 (fun _ -> 
                         Node write (vvar vvars 2) (fun y'' ->
                         Leaf (cvar 0 y''))))))));
      trhs  = (fun vvars -> Node write 42 (fun _ -> 
                         Node write (vvar vvars 0) (fun y ->
                         Node write 42 (fun _ -> 
                         Node write (vvar vvars 2) (fun y' ->
                         Leaf (cvar 0 y'))))))
    }


assume val t : Type

module TT = FStar.Tactics

let foo ()
  : Lemma (requires (eq_to_prop (to_inst_equation st_eq3 (id_template_handler t rw))))
          (ensures  (eq_to_prop (to_inst_equation st_eq (id_template_handler t rw))))
          by (TT.compute (); TT.dump "foo")
  = admit ();
    assert (forall x1 x2 x3 (z:unit -> template t rw) . 
             equiv (Node write 42 (fun _ -> 
                    Node write x1 (fun y ->
                    Node write 42 (fun _ -> 
                    Node write x2 (fun y' ->
                    Node write 42 (fun _ -> 
                    Node write x3 z)))))) 
                   (Node write x3 z));
    assert (forall x1 x3 (z:unit -> template t rw) . 
             equiv (Node write 42 (fun _ -> 
                    Node write x1 (fun y ->
                    Node write 42 (fun _ -> 
                    Node write x3 z)))) 
                   (Node write x3 z))
                   




