module Eff

module S = Eff.Signature

(* Computation tree representation of the Eff effect *)

val eff_repr (a:Type u#u) (ops:S.sig) : Type u#(max 1 u)


(* Monadic operators on the Eff effect *)

val eff_return (a:Type) (x:a) (#ops:S.sig)
  : eff_repr a ops

val eff_bind (a:Type) (b:Type) (#ops:S.sig)
  (t1:eff_repr a ops) 
  (t2:a -> eff_repr b ops) 
  : eff_repr b ops

val eff_subcomp (a:Type) (#ops1:S.sig) (#ops2:S.sig)
  (t:eff_repr a ops1)
  : Pure (eff_repr a ops2)
         (requires (ops1 `S.sub` ops2))
         (ensures (fun _ -> True))

let eff_if_then_else a #ops
  (f:eff_repr a ops)
  (g:eff_repr a ops)
  (b:bool)
  : Type
  = eff_repr a ops

val eff_perform (#ops:S.sig)
  (op:S.op{op `S.mem` ops})
  (x:S.param_of op)
  : eff_repr (S.arity_of op) ops 


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

val lift_pure_eff (a:Type) (wp:_) (ops:S.sig)
  (f:eqtype_as_type unit -> PURE a wp)
  : Pure (eff_repr a ops)
         (requires (wp (fun _ -> True)))
         (ensures (fun _ -> True))

sub_effect PURE ~> Eff = lift_pure_eff


(* Empty signature computations are pure *)

val eff_emp_pure (#a:Type) (c:unit -> eff_repr a S.emp) : a 
  
val emp_pure (#a:Type) (c:unit -> Eff a S.emp) : a 


(* Performing an algebraic effect *)

val perform (#ops:S.sig) (op:S.op{op `S.mem` ops}) (x:S.param_of op) 
  : Eff (S.arity_of op) ops 


(* Effect handlers *)

let handler (ops:S.sig) (a:Type) (ops':S.sig) = 
  op:S.op{op `S.mem` ops} -> S.param_of op -> (S.arity_of op -> Eff a ops') -> Eff a ops'


(* Effect handling *)

val handle (#a:Type) (#b:Type) (#ops:S.sig) (#ops':S.sig)
  (f:unit -> Eff a ops)
  (h:handler ops b ops')
  (k:a -> Eff b ops')
  : Eff b ops'
