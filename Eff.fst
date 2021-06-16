module Eff

open Eff.Signature

module T = Eff.Template

open Eff.Template.Equation

module L = FStar.List.Tot


(* Equation annotations in computation types *)

let equations ops = list (template_equation ops)


(* Subtyping equation annotations *)

let eq_subcomp #ops1 #ops2 (p:squash(ops1 `sub` ops2)) (eq:template_equation ops1)
  : template_equation ops2
  = {
      tvctx = eq.tvctx;
      tcctx = eq.tcctx;
      tlhs  = (fun vvars -> T.template_subcomp _ (eq.tlhs vvars));
      trhs  = (fun vvars -> T.template_subcomp _ (eq.trhs vvars))
    }


let dirt_sub (dirt1:(ops1:sig & equations ops1)) (dirt2:(ops2:sig & equations ops2)) //#ops1 #ops2 (eqs1:equations ops1) (eqs2:equations ops2)
  = let (| ops1 , eqs1 |) = dirt1 in
    let (| ops2 , eqs2 |) = dirt2 in
    ops1 `sub` ops2 /\
    (forall (eq:template_equation ops1) (p:squash(ops1 `sub` ops2)) . L.memP eq eqs1 ==> L.memP (eq_subcomp p eq) eqs2)

(* Computation tree representation of the Eff effect *)

let eff (a:Type u#a) (ops:sig) (eqs:equations ops)
  = T.template a ops


(* Monadic operators on the Eff effect *)

let eff_return a x #ops #eqs
  : eff a ops eqs
  = T.template_return a x #ops

let eff_bind a b #ops #eqs
  (t1:eff a ops eqs) 
  (t2:a -> eff b ops eqs) 
  : eff b ops eqs
  = T.template_bind a b #ops t1 t2

let eff_subcomp a #ops1 #ops2 #eqs1 #eqs2
  (t:eff a ops1 eqs1)
  : Pure (eff a ops2 eqs2)
         (requires (ops1 == ops2 /\ eqs1 === eqs2)) // temporarily, TODO: find way around the typechecking problems with inclusions
         //(requires ((| ops1 , eqs1 |) `dirt_sub` (| ops2 , eqs2 |)))
         (ensures (fun _ -> True))
  = T.template_subcomp a #ops1 #ops2 t

let eff_if_then_else a #ops #eqs
  (f:eff a ops eqs)
  (g:eff a ops eqs)
  (b:bool)
  : Type
  = eff a ops eqs

let eff_perform #ops #eqs
  (op:op{op `mem` ops})
  (x:param_of op)
  : eff (arity_of op) ops eqs
  = T.Node op x (fun y -> T.Leaf y)


(* The Eff effect *)

[@@allow_informative_binders]
total
reifiable
reflectable
layered_effect {
  Eff : a:Type -> ops:sig -> equations ops -> Effect
  with
  repr         = eff;
  return       = eff_return;
  bind         = eff_bind;
  subcomp      = eff_subcomp;
  if_then_else = eff_if_then_else;
  perform      = eff_perform
}


(* Lifting of pure computations into the Eff effect *)

let lift_pure_eff a wp ops eqs
  (f:eqtype_as_type unit -> PURE a wp)
  : Pure (eff a ops eqs)
         (requires (wp (fun _ -> True)))
         (ensures (fun _ -> True))
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    T.Leaf (f ())

sub_effect PURE ~> Eff = lift_pure_eff


(* Empty signature computations are pure *)

let eff_emp_pure #a (c:unit -> eff a emp []) : a 
  = match c () with
    | T.Leaf x -> x
  
let emp_pure #a (c:unit -> Eff a emp []) : a 
  = eff_emp_pure (fun x -> reify (c ()))


(* Performing an algebraic effect *)

let perform #ops #eqs (op:op{op `mem` ops}) (x:param_of op) 
  : Eff (arity_of op) ops eqs
  = Eff?.perform op x


(* Normalisation steps used to compute handler types *)

let eff_norm_steps = [delta;zeta;primops;simplify;iota]


(* Hypotheses for proving handler correctness *)

let rec to_respects_hypotheses a #ops (eqs':equations ops) 
  : Type0
  = match eqs' with
    | [] -> True
    | eq :: eqs'' ->
      eq_to_prop (to_inst_equation eq (T.id_template_handler a ops))
      /\
      to_respects_hypotheses a eqs''


(* Effect handlers (on Eff effect representations) *)

let eff_handler_raw (ops:sig) (eqs:equations ops) (a:Type) (ops':sig) (eqs':equations ops') 
  = op:op{op `mem` ops} -> param_of op -> (arity_of op -> eff a ops' eqs') -> eff a ops' eqs'

let rec eff_handler_respects (ops:sig) (eqs:equations ops) (a:Type) 
  (ops':sig) (eqs':equations ops') (h:eff_handler_raw ops eqs a ops' eqs') 
  : Type 
  = match eqs with
    | [] -> unit
    | eq :: [] -> 
        (unit -> Lemma (requires (to_respects_hypotheses a eqs')) 
                      (ensures  (eq_to_prop (to_inst_equation eq h))))
    | eq :: eq' :: eqs'' -> 
        (unit -> Lemma (requires (to_respects_hypotheses a eqs')) 
                      (ensures  (eq_to_prop (to_inst_equation eq h))))
        *
        eff_handler_respects ops (eq' :: eqs'') a ops' eqs' h

noeq type eff_handler (ops:sig) (eqs:equations ops) (a:Type) (ops':sig) (eqs':equations ops') = {
  eff_op_cases : eff_handler_raw ops eqs a ops' eqs';
  eff_respects : eff_handler_respects ops eqs a ops' eqs' eff_op_cases
}


(* Effect handlers *)

let handler_raw (ops:sig) (eqs:equations ops) (a:Type) (ops':sig) (eqs':equations ops') 
  = op:op{op `mem` ops} -> param_of op -> (arity_of op -> Eff a ops' eqs') -> Eff a ops' eqs'

let reflect_cont #a #b #ops #eqs (k:b -> eff a ops eqs) (y:b) : Eff a ops eqs
  = Eff?.reflect (k y)

let to_eff_handler_raw #ops #eqs #a #ops' #eqs'
  (h:handler_raw ops eqs a ops' eqs')
  : eff_handler_raw ops eqs a ops' eqs'
  = fun op x k ->  
      (reify (h op x (reflect_cont k)))

let rec handler_respects (ops:sig) (eqs:equations ops) (a:Type) 
  (ops':sig) (eqs':equations ops') (h:handler_raw ops eqs a ops' eqs') 
  : Type 
  = match eqs with
    | [] -> unit
    | eq :: [] ->
        (unit -> Lemma (requires (to_respects_hypotheses a eqs'))
                      (ensures  (eq_to_prop (to_inst_equation eq (to_eff_handler_raw h)))))
    | eq :: eq' :: eqs'' -> 
        (unit -> Lemma (requires (to_respects_hypotheses a eqs'))
                      (ensures  (eq_to_prop (to_inst_equation eq (to_eff_handler_raw h)))))
        *
        handler_respects ops (eq' :: eqs'') a ops' eqs' h

noeq type handler (ops:sig) (eqs:equations ops) (a:Type) (ops':sig) (eqs':equations ops') = {
  op_cases : handler_raw ops eqs a ops' eqs';
  respects : handler_respects ops eqs a ops' eqs' op_cases
}


(* Effect handling *)

let eff_handle #a #b #ops #ops' #eqs #eqs'
  (t:eff a ops eqs)
  (h:eff_handler ops eqs b ops' eqs')
  (k:a -> eff b ops' eqs')
  : eff b ops' eqs'
  = T.template_handle t h.eff_op_cases k

let handle #a #b #ops #ops' #eqs #eqs'
  (f:unit -> Eff a ops eqs)
  (h:handler ops eqs b ops' eqs')
  (k:a -> Eff b ops' eqs')
  : Eff b ops' eqs'
  = Eff?.reflect (
      T.template_handle
        (reify (f ()))
        (to_eff_handler_raw h.op_cases)
        (fun x -> reify (k x)))
