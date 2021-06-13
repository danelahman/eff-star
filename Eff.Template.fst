module Eff.Template

open Eff.Signature

(* Computation tree representation of the Eff effect *)

noeq type template (a:Type u#u) (ops:sig) =
  | Leaf : a 
         -> template a ops
  | Node : op:op
         -> #squash(op `mem` ops)
         -> param_of op 
         -> (arity_of op -> template a ops)
         -> template a ops


(* Monadic operators on the Eff effect *)

let template_return a x #ops
  : template a ops
  = Leaf x

let rec template_bind a b #ops
  (t1:template a ops) 
  (t2:a -> template b ops) 
  : template b ops
  = match t1 with
    | Leaf x -> t2 x
    | Node op x k -> 
        Node op x 
          (fun y -> template_bind a b (k y) t2)

let rec template_subcomp a #ops1 #ops2
  (t:template a ops1)
  : Pure (template a ops2)
         (requires (ops1 `sub` ops2))
         (ensures (fun _ -> True))
  = match t with
    | Leaf x -> Leaf x
    | Node op x k -> 
        Node op x 
          (fun y -> template_subcomp a (k y))

let template_if_then_else a #ops
  (f:template a ops)
  (g:template a ops)
  (b:bool)
  : Type
  = template a ops

let template_perform #ops
  (op:op{op `mem` ops})
  (x:param_of op)
  : template (arity_of op) ops 
  = Node op x (fun y -> Leaf y)


(* The Eff effect *)

[@@allow_informative_binders]
total
reifiable
reflectable
layered_effect {
  Template : a:Type -> sig -> Effect
  with
  repr         = template;
  return       = template_return;
  bind         = template_bind;
  subcomp      = template_subcomp;
  if_then_else = template_if_then_else;
  perform      = template_perform
}


(* Lifting of pure computations into the Eff effect *)

let lift_pure_template a wp ops
  (f:eqtype_as_type unit -> PURE a wp)
  : Pure (template a ops)
         (requires (wp (fun _ -> True)))
         (ensures (fun _ -> True))
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    Leaf (f ())

sub_effect PURE ~> Template = lift_pure_template


(* Empty signature computations are pure *)

let template_emp_pure #a (c:unit -> template a emp) : a 
  = match c () with
    | Leaf x -> x
  
let emp_pure #a (c:unit -> Template a emp) : a 
  = template_emp_pure (fun x -> reify (c ()))
  

(* Performing an algebraic effect *)

let perform #ops (op:op{op `mem` ops}) (x:param_of op) 
  : Template (arity_of op) ops 
  = Template?.perform op x


(* Effect handlers *)

let handler (ops:sig) (a:Type) (ops':sig) = 
  op:op{op `mem` ops} -> param_of op -> (arity_of op -> Template a ops') -> Template a ops'

let template_handler (ops:sig) (a:Type) (ops':sig) = 
  op:op{op `mem` ops} -> param_of op -> (arity_of op -> template a ops') -> template a ops'

let id_template_handler (a:Type) (ops:sig) 
  : template_handler ops a ops
  = fun op x k -> Node op x k

let reflect_cont #a #b #ops (k:b -> template a ops) (y:b) : Template a ops
  = Template?.reflect (k y)

let to_eff_handler #ops #a #ops'
  (h:handler ops a ops')
  : template_handler ops a ops'
  = fun op x k ->  
      (reify (h op x (reflect_cont k))) 
      

(* Effect handling *)

let rec template_handle #a #b #ops #ops'
  (t:template a ops)
  (h:template_handler ops b ops')
  (k:a -> template b ops')
  : template b ops'
  = match t with
    | Leaf x -> k x
    | Node op x l -> 
        h op x (fun y -> 
          template_handle (l y) h k)

let handle #a #b #ops #ops'
  (f:unit -> Template a ops)
  (h:handler ops b ops')
  (k:a -> Template b ops')
  : Template b ops'
  = Template?.reflect (
      template_handle 
        (reify (f ()))
        (to_eff_handler h)
        (fun x -> reify (k x)))

