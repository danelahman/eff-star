module Eff

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
