module Eff.Template.Equiv

open Eff.Signature
open Eff.Template

val equiv (#a:Type) (#ops:sig) (t1 t2:template a ops) : Type0

val refl (#a:Type) (#ops:sig) (t:template a ops)
  : Lemma (t `equiv` t)
          [SMTPat (t `equiv` t)]

val sym (#a:Type) (#ops:sig) (t1 t2:template a ops)
  : Lemma (requires (t1 `equiv` t2))
          (ensures  (t2 `equiv` t1))
          [SMTPat (t2 `equiv` t1)]

val trans (#a:Type) (#ops:sig) (t1 t2 t3:template a ops)
  : Lemma (requires (t1 `equiv` t2 /\ t2 `equiv` t3))
          (ensures  (t1 `equiv` t3))
          [SMTPat (t1 `equiv` t2); 
           SMTPat (t1 `equiv` t3)]

val leaf_cong (#a:Type) (#ops:sig) (x1 x2:a)
  : Lemma (requires (x1 == x2))
          (ensures  (equiv #a #ops (Leaf x1) (Leaf x2)))
          [SMTPat (equiv #a #ops (Leaf x1) (Leaf x2))]

val op_cong (#a:Type) (#ops:sig) 
            (op:op{op `mem` ops}) (x:param_of op) 
            (t1 t2:arity_of op -> template a ops)
  : Lemma (requires (forall (y:arity_of op) . t1 y `equiv` t2 y))
          (ensures  (Node op x t1 `equiv` Node op x t2))
          [SMTPat (Node op x t1 `equiv` Node op x t2)]
