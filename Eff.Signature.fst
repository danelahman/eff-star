module Eff.Signature

module S = FStar.TSet

(* Operations *)

noeq type op =
  | Op : string -> #a:Type0 -> #b:Type0 -> op

let name_of (Op op #_ #_) = op
let param_of (Op _ #a #_) = a
let arity_of (Op _ #_ #b) = b


(* Signatures *)

let sig_aux = 
  ops:S.set op{forall op1 op2 . op1 `S.mem` ops /\ op2 `S.mem` ops /\ name_of op1 = name_of op2 
                        ==> param_of op1 == param_of op2 /\ arity_of op1 == arity_of op2}

let sig = FStar.Ghost.erased sig_aux


(* Basic operations on signatures *)

let singleton (o:op) : sig = S.singleton o

let mem (op:op) (ops:sig) = op `S.mem` ops

let sub (ops1 ops2:sig) = ops1 `S.subset` ops2

let emp : sig = S.empty

let compat_with (ops1 ops2:sig) =
  forall op1 op2 . op1 `S.mem` ops1 /\ op2 `S.mem` ops2 /\ name_of op1 = name_of op2 
           ==> param_of op1 == param_of op2 /\ arity_of op1 == arity_of op2

let union (ops1 ops2:sig) 
  : Pure sig (requires (ops1 `compat_with` ops2)) (ensures (fun _ -> True)) 
  = ops1 `S.union` ops2
