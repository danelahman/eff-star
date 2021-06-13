module Eff.Template.Equiv

open Eff.Signature
open Eff.Template

open FStar.Squash

[@@ erasable]
noeq type equiv_t (#a:Type) (#ops:sig) : (t1:template a ops) -> (t2:template a ops) -> Type =
  | Refl   : (t:template a ops) 
           -> equiv_t t t
  | Sym    : (t1:template a ops) 
           -> (t2:template a ops) 
           -> equiv_t t1 t2
           -> equiv_t t2 t1
  | Trans  : (t1:template a ops) 
           -> (t2:template a ops) 
           -> (t3:template a ops) 
           -> equiv_t t1 t2
           -> equiv_t t2 t3 
           -> equiv_t t1 t3
  | OpCong : (op:op{op `mem` ops})
           -> (x:param_of op)
           -> (t1:(arity_of op -> template a ops))
           -> (t2:(arity_of op -> template a ops))
           -> (y:arity_of op -> equiv_t (t1 y) (t2 y))
           -> equiv_t (Node op x t1) (Node op x t2)

let equiv (#a:Type) (#ops:sig) (t1 t2:template a ops) 
  = squash (equiv_t t1 t2)

let refl (#a:Type) (#ops:sig) (t:template a ops) 
  = return_squash (Refl t)

let sym (#a:Type) (#ops:sig) (t1 t2:template a ops)
  = bind_squash (get_proof (equiv t1 t2)) (fun p ->
    bind_squash p (fun p' -> 
    return_squash (Sym t1 t2 p')))

let trans (#a:Type) (#ops:sig) (t1 t2 t3:template a ops)
  = bind_squash (get_proof (equiv t1 t2)) (fun p ->
    bind_squash (get_proof (equiv t2 t3)) (fun q ->
    bind_squash p (fun p' ->
    bind_squash q (fun q' -> 
    return_squash (Trans t1 t2 t3 p' q')))))

let leaf_cong (#a:Type) (#ops:sig) (x1 x2:a)
  = return_squash (Refl (Leaf #a #ops x1))

let op_cong (#a:Type) (#ops:sig) 
            (op:op{op `mem` ops}) (x:param_of op) 
            (t1 t2:arity_of op -> template a ops)
  = bind_squash (get_proof (forall (y:arity_of op) . equiv (t1 y) (t2 y))) (fun p ->
    bind_squash (squash_double_arrow p) (fun p' ->
    return_squash (OpCong op x t1 t2 p')))
