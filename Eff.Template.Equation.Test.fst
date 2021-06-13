module Eff.Template.Equation.Test

open Eff.Signature
open Eff.Template
open Eff.Template.Equation

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
      lhs  = (fun vvars -> let y = perform read () in 
                        let y' = perform write y in
                        cvar 0 y');
      rhs  = (fun vvars -> cvar 0 ())
    }

let st_eq2 : equation rw
  = {
      vctx = [int];
      cctx = [int];
      lhs  = (fun vvars -> perform write (vvar vvars 0);
                        let y = perform read () in
                        cvar 0 y);
      rhs  = (fun vvars -> perform write (vvar vvars 0);
                        cvar 0 (vvar vvars 0))
    }

let st_eq3 : equation rw
  = {
      vctx = [int;int];
      cctx = [unit];
      lhs  = (fun vvars -> perform write (vvar vvars 0);
                        let y = perform write (vvar vvars 1) in
                        cvar 0 y);
      rhs  = (fun vvars -> let y = perform write (vvar vvars 1) in
                        cvar 0 y)
    }





(* ************************** *)


let st_eq : equation rw
  = {
      vctx = [int;int;int];
      cctx = [unit];
      lhs  = (fun vvars -> perform write (vvar vvars 0);
                        perform write (vvar vvars 1);
                        let y = perform write (vvar vvars 2) in
                        cvar 0 y);
      rhs  = (fun vvars -> perform write (vvar vvars 0);
                        let y = perform write (vvar vvars 2) in
                        cvar 0 y)
    }


assume val t : Type

let foo ()
  : Lemma (requires (norm [delta;zeta;primops;simplify;iota] (eq_to_prop (to_inst_equation (to_template_equation st_eq3) (id_template_handler t rw)))))
          (ensures  (norm [delta;zeta;primops;simplify;iota] (eq_to_prop (to_inst_equation (to_template_equation st_eq) (id_template_handler t rw)))))
  = ()
