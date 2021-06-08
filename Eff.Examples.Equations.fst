module Eff.Examples.Equations

module S = Eff.Signature

open Eff.Examples.IntState

module F = FStar.FunctionalExtensionality

open FStar.Tactics // temporary

(* Experimenting with equations *)


assume type template_repr (a:Type)

assume val leaf : #(a:Type) -> a -> template_repr a

assume val node : #(a:Type) -> op:S.op -> S.param_of op -> (S.arity_of op -> template_repr a) -> template_repr a

unfold
let eq1 x (z:unit -> template_repr int) 
  = node write x z == z ()

unfold
let eq2 x y (z:unit -> template_repr int) 
  = node write x z == node write y z

let f (z:unit -> template_repr int) 
  : Pure unit 
         (requires (forall x z . eq1 x z))
         (ensures (fun _ -> node write 42 z == node write 24 z)) 
  = ()

let node_ext (a:Type) (op:S.op) (x:S.param_of op) (z1 z2:S.arity_of op -> template_repr a)
  : Lemma (requires (F.feq z1 z2))
          (ensures  (node op x (F.on_domain (S.arity_of op) z1) == node op x (F.on_domain (S.arity_of op) z2)))
          [SMTPat (node op x (F.on_domain (S.arity_of op) z1)); SMTPat (node op x (F.on_domain (S.arity_of op) z2))]
  = ()

let g (z:unit -> template_repr int) 
  : Pure unit 
         (requires (forall x z . eq1 x z))
         (ensures (fun _ -> node read () (F.on_domain int (fun _ -> node write 42 z)) 
                         == 
                         node read () (F.on_domain int (fun _ -> node write 24 z))))
  = ()
    //; assert (F.feq #int (fun _ -> node write 42 z) (fun _ -> node write 24 z))


(*

assume type template_repr (a:Type) (ops:S.sig)

assume val leaf : #(a:Type) -> #(ops:S.sig) -> a -> template_repr a ops

assume val node : #(a:Type) -> #(ops:S.sig) -> op:S.op -> #squash(op `S.mem` ops) -> S.param_of op -> (S.arity_of op -> template_repr a ops) -> template_repr a ops

unfold
let eq1 x (z:unit -> template_repr int rw) = node write x z == z ()

unfold
let eq2 x y (z:unit -> template_repr int rw) = node write x z == node write y z

let f (z:unit -> template_repr int rw) 
  : Pure unit 
         (requires (forall x z . eq1 x z))
         (ensures (fun _ -> node write 42 z == node write 24 z)) 
  = ()

(*
let foo (z1 z2:int -> template_repr int rw)
  : Lemma (requires (F.feq #int z1 z2))
          (ensures  (node read () (F.on_domain int z1) == node read () (F.on_domain int z2)))
          [SMTPat (node read () (F.on_domain int z1)); SMTPat (node read () (F.on_domain int z2))]
  = ()
*)

let node_ext (a:Type) (ops:S.sig) (op:S.op) (#p:squash(op `S.mem` ops)) (x:S.param_of op) (z1 z2:S.arity_of op -> template_repr a ops)
  : Lemma (requires (F.feq #(S.arity_of op) z1 z2))
          (ensures  (node op #p x (F.on_domain (S.arity_of op) z1) == node op #p x (F.on_domain (S.arity_of op) z2)))
          [SMTPat (node op #p x (F.on_domain (S.arity_of op) z1)); SMTPat (node op #p x (F.on_domain (S.arity_of op) z2))]
  = ()

let g (z:unit -> template_repr int rw) 
  : Pure unit 
         (requires (forall x z . eq1 x z))
         (ensures (fun _ -> node read () (F.on_domain int (fun _ -> node write 42 z)) 
                         == 
                         node read () (F.on_domain int (fun _ -> node write 24 z))))
  = ()
    //assert (forall x . F.on_domain int (fun _ -> node write 42 z) x == F.on_domain int (fun _ -> node write 24 z) x)
    //assert (F.feq #int (fun _ -> node write 42 z) (fun _ -> node write 24 z))
    //assert (F.on_domain int (fun _ -> node write 42 z) == F.on_domain int (fun _ -> node write 24 z))



*)










(*
unfold
let eq = forall x (z:unit -> eff_repr int rw) . {:pattern (Node write x z)} Node write x z == z ()

assume val write_ignore (x:int) (z:unit -> eff_repr int rw)
  : Lemma (Node write x z == z ())
          [SMTPat (Node write x z)]

let f (z:unit -> eff_repr int rw) 
  : Pure unit 
         (requires (eq))
         (ensures (fun _ ->
           Node write 42 z == Node write 24 z)) 
  = admit ()
  
let g (z:unit -> eff_repr int rw) 
  : Lemma (Node write 42 z == Node write 24 z)
  = admit ()

let g' (z:unit -> eff_repr int rw) 
  : Lemma (Node write 42 z == Node write 24 z)
  = write_ignore 42 z;
    write_ignore 24 z

let g'' (z:unit -> eff_repr int rw) 
  : Lemma (Node read () (fun _ -> Node write 42 z) == Node read () (fun _ -> Node write 24 z))
  = write_ignore 42 z;
    write_ignore 24 z
*)



