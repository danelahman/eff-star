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


(* Normalisatin steps used to compute handler types *)

let eff_norm_steps = [delta;zeta;primops;simplify;iota]


(* Effect handlers (on Eff effect representations) *)

let eff_handler_raw (ops:sig) (eqs:equations ops) (a:Type) (ops':sig) (eqs':equations ops') 
  = op:op{op `mem` ops} -> param_of op -> (arity_of op -> eff a ops' eqs') -> eff a ops' eqs'

let rec to_respects_hypotheses a #ops (eqs:equations ops) 
  : Type0
  = match eqs with
    | [] -> True
    | eq :: eqs' ->
      eq_to_prop (to_inst_equation eq (T.id_template_handler a ops))
      /\
      to_respects_hypotheses a eqs'

let rec eff_handler_respects (ops:sig) (eqs:equations ops) (a:Type) 
  (ops':sig) (eqs':equations ops') (h:eff_handler_raw ops eqs a ops' eqs') 
  : Type 
  = match eqs with
    | [] -> unit
    | eq :: [] -> 
        (unit -> Pure unit
                (requires (norm eff_norm_steps (to_respects_hypotheses a eqs')))
                (ensures  (fun _ -> norm eff_norm_steps (eq_to_prop (to_inst_equation eq h)))))
    | eq :: eq' :: eqs'' -> 
        (unit -> Pure unit
                (requires (norm eff_norm_steps (to_respects_hypotheses a eqs')))
                (ensures  (fun _ -> norm eff_norm_steps (eq_to_prop (to_inst_equation eq h)))))
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
        (unit -> Pure unit
                (requires (norm eff_norm_steps (to_respects_hypotheses a eqs')))
                (ensures  (fun _ -> norm eff_norm_steps (eq_to_prop (to_inst_equation eq (to_eff_handler_raw h))))))
    | eq :: eq' :: eqs'' -> 
        (unit -> Pure unit
                (requires (norm eff_norm_steps (to_respects_hypotheses a eqs')))
                (ensures  (fun _ -> norm eff_norm_steps (eq_to_prop (to_inst_equation eq (to_eff_handler_raw h))))))
        *
        handler_respects ops (eq' :: eqs'') a ops' eqs' h

noeq type handler (ops:sig) (eqs:equations ops) (a:Type) (ops':sig) (eqs':equations ops') = {
  op_cases : handler_raw ops eqs a ops' eqs';
  respects : handler_respects ops eqs a ops' eqs' op_cases
}











(*
let handler (ops:S.sig) (a:Type) (ops':S.sig) = 
  op:S.op{op `S.mem` ops} -> S.param_of op -> (S.arity_of op -> Eff a ops') -> Eff a ops'

let reflect_cont #a #b #ops (k:b -> eff_repr a ops) (y:b) : Eff a ops
  = Eff?.reflect (k y)

let to_eff_handler #ops #a #ops'
  (h:handler ops a ops')
  : eff_handler ops a ops'
  = fun op x k ->  
      (reify (h op x (reflect_cont k))) 
*)


(*
module S = Eff.Signature

(* Computation tree representation of the Eff effect *)

noeq type eff_repr' (a:Type u#u) (ops:S.sig) =
  | Leaf : a 
         -> eff_repr' a ops
  | Node : op:S.op
         -> #squash(op `S.mem` ops)
         -> S.param_of op 
         -> (S.arity_of op -> eff_repr' a ops)
         -> eff_repr' a ops

let eff_repr a ops = eff_repr' a ops

(* Monadic operators on the Eff effect *)

let eff_return a x #ops
  : eff_repr a ops
  = Leaf x

let rec eff_bind a b #ops
  (t1:eff_repr a ops) 
  (t2:a -> eff_repr b ops) 
  : eff_repr b ops
  = match t1 with
    | Leaf x -> t2 x
    | Node op x k -> 
        Node op x 
          (fun y -> eff_bind a b (k y) t2)

let rec eff_subcomp a #ops1 #ops2
  (t:eff_repr a ops1)
  : Pure (eff_repr a ops2)
         (requires (ops1 `S.sub` ops2))
         (ensures (fun _ -> True))
  = match t with
    | Leaf x -> Leaf x
    | Node op x k -> 
        Node op x 
          (fun y -> eff_subcomp a (k y))
          
let eff_if_then_else a #ops
  (f:eff_repr a ops)
  (g:eff_repr a ops)
  (b:bool)
  : Type
  = eff_repr a ops


let eff_perform #ops
  (op:S.op{op `S.mem` ops})
  (x:S.param_of op)
  : eff_repr (S.arity_of op) ops 
  = Node op x (fun y -> Leaf y)


(* The Eff effect *)

[@@allow_informative_binders]
total
reifiable
reflectable
layered_effect {
  Eff : a:Type -> S.sig -> Effect
  with
  repr         = eff_repr;
  return       = eff_return;
  bind         = eff_bind;
  subcomp      = eff_subcomp;
  if_then_else = eff_if_then_else;
  perform      = eff_perform
}


(* Lifting of pure computations into the Eff effect *)

let lift_pure_eff a wp ops
  (f:eqtype_as_type unit -> PURE a wp)
  : Pure (eff_repr a ops)
         (requires (wp (fun _ -> True)))
         (ensures (fun _ -> True))
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    Leaf (f ())

sub_effect PURE ~> Eff = lift_pure_eff


(* Empty signature computations are pure *)

let eff_emp_pure #a (c:unit -> eff_repr a S.emp) : a 
  = match c () with
    | Leaf x -> x
  
let emp_pure #a (c:unit -> Eff a S.emp) : a 
  = eff_emp_pure (fun x -> reify (c ()))
  

(* Performing an algebraic effect *)

let perform #ops (op:S.op{op `S.mem` ops}) (x:S.param_of op) 
  : Eff (S.arity_of op) ops 
  = Eff?.perform op x


(* Effect handlers *)

let eff_handler (ops:S.sig) (a:Type) (ops':S.sig) = 
  op:S.op{op `S.mem` ops} -> S.param_of op -> (S.arity_of op -> eff_repr a ops') -> eff_repr a ops'

let handler (ops:S.sig) (a:Type) (ops':S.sig) = 
  op:S.op{op `S.mem` ops} -> S.param_of op -> (S.arity_of op -> Eff a ops') -> Eff a ops'

let reflect_cont #a #b #ops (k:b -> eff_repr a ops) (y:b) : Eff a ops
  = Eff?.reflect (k y)

let to_eff_handler #ops #a #ops'
  (h:handler ops a ops')
  : eff_handler ops a ops'
  = fun op x k ->  
      (reify (h op x (reflect_cont k))) 
      

(* Effect handling *)

let rec eff_handle #a #b #ops #ops'
  (t:eff_repr a ops)
  (h:eff_handler ops b ops')
  (k:a -> eff_repr b ops')
  : eff_repr b ops'
  = match t with
    | Leaf x -> k x
    | Node op x l -> 
        h op x (fun y -> 
          eff_handle (l y) h k)

let handle #a #b #ops #ops'
  (f:unit -> Eff a ops)
  (h:handler ops b ops')
  (k:a -> Eff b ops')
  : Eff b ops'
  = Eff?.reflect (
      eff_handle 
        (reify (f ()))
        (to_eff_handler h)
        (fun x -> reify (k x)))

*)
