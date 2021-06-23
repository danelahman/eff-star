module Eff.Equation.Test

open Eff.Signature
open Eff.Template.Equation
open Eff.Template.Equiv

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

module TT = FStar.Tactics

assume val a : Type

#set-options "--z3rlimit_factor 10"

let h5_op_cases : eff_handler_raw rw [st_eq] a rw [st_eq3]
 = fun op x k -> 
     match op with
     | Op "read" -> 
         T.Node read x k
     | Op "write" -> 
         T.Node write 42 (fun _ -> 
         T.Node write x k)

(*
let val_ctx (x:int) (y:int) 
  : vvars [int;int]
  = [VVar x; VVar y]

let comp_ctx #a (z:unit -> T.template a rw)
  : inst_cvars [unit] a rw
  = [ICVar z]

let apply_st_eq3 #a (x:int) (y:int) (z:unit -> T.template a rw)
  : Lemma (requires (eq_to_prop (to_inst_equation st_eq3 (T.id_template_handler a rw))))
          (ensures  ((
                     ((to_inst_equation st_eq3 (T.id_template_handler a rw)).ilhs (val_ctx x y) (comp_ctx z)) 
                     `equiv` 
                     ((to_inst_equation st_eq3 (T.id_template_handler a rw)).irhs (val_ctx x y) (comp_ctx z))
                     )))
      by (TT.compute ())
  = ()
*)

let apply_st_eq3 #a (x1:int) (x2:int) (z:unit -> T.template a rw)
  : Lemma (requires (forall (x1 x2:int) (z:unit -> T.template a rw) . 
                       equiv (T.Node write x1 (fun y ->
                              T.Node write x2 (fun y' ->
                              z y'))) 
                             (T.Node write x2 (fun y ->
                              z y))))
          (ensures  (equiv (T.Node write x1 (fun y ->
                            T.Node write x2 (fun y' ->
                            z y'))) 
                           (T.Node write x2 (fun y ->
                            z y))))
  = ()

let h5_respects ()
  : Tot (eff_handler_respects rw [st_eq] a rw [st_eq3] h5_op_cases)
  = _ by (let hyp_eqs : list Reflection.Types.binder = respects_tac () in
          respects_op_cong ();
          respects_op_cong ();
          respects_op_cong ();
          respects_trans 
            (fun _ -> TT.apply_lemma (`apply_st_eq3); 
                   TT.compute ();
                   (if (Some? (List.Tot.nth hyp_eqs 0)) then (TT.mapply (Some?.v (List.Tot.nth hyp_eqs 0))) else ()))
            (fun _ -> TT.apply_lemma (`apply_st_eq3); 
                   TT.compute ();
                   (if (Some? (List.Tot.nth hyp_eqs 0)) then (TT.mapply (Some?.v (List.Tot.nth hyp_eqs 0))) else ()));
          TT.dump "foo"
          )

let h5 : eff_handler rw [st_eq] a rw [st_eq3] = {
  eff_op_cases = h5_op_cases;
  eff_respects = h5_respects ()
}



let h1_op_cases : eff_handler_raw rw [] a rw []
 = fun op x k -> T.Node op x k

let h1_respects ()
 : Tot (eff_handler_respects rw [] a rw [] h1_op_cases)
 = ()

let h1 : eff_handler rw [] a rw [] = {
  eff_op_cases = h1_op_cases;
  eff_respects = h1_respects ()
}


let h2_op_cases : eff_handler_raw rw [] a rw [st_eq1;st_eq2;st_eq3]
 = fun op x k -> T.Node op x k

let h2_respects ()
 : Tot (eff_handler_respects rw [] a rw [st_eq1;st_eq2;st_eq3] h2_op_cases)
 = ()

let h2 : eff_handler rw [] a rw [st_eq1;st_eq2;st_eq3] = {
  eff_op_cases = h2_op_cases;
  eff_respects = h2_respects ()
}

(*
let h3_op_cases : eff_handler_raw rw [st_eq] a rw [st_eq1;st_eq2;st_eq3]
 = fun op x k -> T.Node op x k

let h3_respects ()
 : Tot (eff_handler_respects rw [st_eq] a rw [st_eq1;st_eq2;st_eq3] h3_op_cases)
 = _ by (respects_tac_smt ())

let h3 : eff_handler rw [st_eq] a rw [st_eq1;st_eq2;st_eq3] = {
  eff_op_cases = h3_op_cases;
  eff_respects = h3_respects ()
}


let h4_op_cases : eff_handler_raw rw [st_eq;st_eq] a rw [st_eq1;st_eq2;st_eq3]
 = fun op x k -> T.Node op x k

let h4_respects ()
 : Tot (eff_handler_respects rw [st_eq;st_eq] a rw [st_eq1;st_eq2;st_eq3] h4_op_cases)
 = (_ by (respects_tac ())) , 
   (_ by (respects_tac ()))

let h4 : eff_handler rw [st_eq;st_eq] a rw [st_eq1;st_eq2;st_eq3] = {
  eff_op_cases = h4_op_cases;
  eff_respects = h4_respects ()
}
*)

(*
let h6_op_cases : eff_handler_raw rw [st_eq1;st_eq2;st_eq3] a rw [st_eq1;st_eq2;st_eq3]
 = fun op x k -> 
     match op with
     | Op "read" -> 
         T.Node read x k
     | Op "write" -> 
         T.Node write 42 (fun _ -> 
         T.Node write x k)

let h6_respects ()
 : Tot (eff_handler_respects rw [st_eq1;st_eq2;st_eq3] a rw [st_eq1;st_eq2;st_eq3] h6_op_cases)
     by (respects_tac (); TT.dump "foo")
 = ()

let h6 : eff_handler rw [st_eq1;st_eq2;st_eq3] a rw [st_eq1;st_eq2;st_eq3] = {
  eff_op_cases = h6_op_cases;
  eff_respects = h6_respects ()
}


*)
