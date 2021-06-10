module Eff.Template

open Eff.Signature

(* Computation tree representation of the Template effect *)

val template_repr (a:Type u#u) (ops:sig) : Type u#(max 1 u)


(* Monadic operators on the Template effect *)

val template_return (a:Type) (x:a) (#ops:sig)
  : template_repr a ops

val template_bind (a:Type) (b:Type) (#ops:sig)
  (t1:template_repr a ops) 
  (t2:a -> template_repr b ops) 
  : template_repr b ops

val template_subcomp (a:Type) (#ops1:sig) (#ops2:sig)
  (t:template_repr a ops1)
  : Pure (template_repr a ops2)
         (requires (ops1 `sub` ops2))
         (ensures (fun _ -> True))

let template_if_then_else a #ops
  (f:template_repr a ops)
  (g:template_repr a ops)
  (b:bool)
  : Type
  = template_repr a ops

val template_perform (#ops:sig)
  (op:op{op `mem` ops})
  (x:param_of op)
  : template_repr (arity_of op) ops 


(* The Eff effect *)

[@@allow_informative_binders]
total
reifiable
reflectable
layered_effect {
  Template : a:Type -> sig -> Effect
  with
  repr         = template_repr;
  return       = template_return;
  bind         = template_bind;
  subcomp      = template_subcomp;
  if_then_else = template_if_then_else;
  perform      = template_perform
}


(* Lifting of pure computations into the Template effect *)

val lift_pure_template (a:Type) (wp:_) (ops:sig)
  (f:eqtype_as_type unit -> PURE a wp)
  : Pure (template_repr a ops)
         (requires (wp (fun _ -> True)))
         (ensures (fun _ -> True))

sub_effect PURE ~> Template = lift_pure_template


(* Empty signature computations are pure *)
  
val emp_pure (#a:Type) (c:unit -> Template a emp) : a 


(* Performing an algebraic effect *)

val perform (#ops:sig) (op:op{op `mem` ops}) (x:param_of op) 
  : Template (arity_of op) ops 


(* Effect handlers *)

let handler (ops:sig) (a:Type) (ops':sig) = 
  op:op{op `mem` ops} -> param_of op -> (arity_of op -> Template a ops') -> Template a ops'

val reflect_cont (#a:Type) (#b:Type) (#ops:sig) (k:b -> template_repr a ops) (y:b) : Template a ops


(* Effect handling *)

val handle (#a:Type) (#b:Type) (#ops:sig) (#ops':sig)
  (f:unit -> Template a ops)
  (h:handler ops b ops')
  (k:a -> Template b ops')
  : Template b ops'
