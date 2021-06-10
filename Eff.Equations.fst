module Eff.Equations

open Eff.Signature
open Eff.Template

module L = FStar.List.Tot


(* Value variables *)

noeq type vvar_t =
  | VVar : (a:Type) -> (x:a) -> vvar_t

let vvars (vctx:list Type) 
  = vvars:list vvar_t{L.length vctx = L.length vvars /\
                     (forall x . x < L.length vvars ==> VVar?.a (L.index vvars x) == (L.index vctx x))}

unfold
let vvar #vctx (vvars:vvars vctx) (x:nat{x < L.length vctx}) 
  : (L.index vctx x)
  = VVar?.x (L.index vvars x)


(* Computation variables *)

noeq type cvar_t a ops =
  | CVar : (b:Type) -> (z:(b -> Template a ops)) -> cvar_t a ops

let cvars (cctx:list Type) a ops
  = cvars:list (cvar_t a ops){L.length cctx = L.length cvars /\
                             (forall x . x < L.length cvars ==> CVar?.b (L.index cvars x) == (L.index cctx x))}

unfold
let cvar #cctx #a #ops (cvars:cvars cctx a ops) (x:nat{x < L.length cctx}) 
  : (L.index cctx x) -> Template a ops
  = CVar?.z (L.index cvars x)


(* Equations between templates *)

noeq type equation (a:Type) (ops:sig) = {
  vctx:list Type;
  cctx:list Type;
  lhs:(vvars vctx) -> (cvars cctx a ops) -> Template a ops;
  rhs:(vvars vctx) -> (cvars cctx a ops) -> Template a ops
}
