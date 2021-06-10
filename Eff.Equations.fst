module Eff.Equations

open Eff.Signature
open Eff.Template

module L = FStar.List.Tot

(* *************************** *)
(* Equations between templates *)
(* *************************** *)

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



(* ********************************************************** *)
(* Turning equations between templates into logical equations *)
(* ********************************************************** *)

(* Computation variables for template representations *)

noeq type repr_cvar_t a ops =
  | RCVar : (b:Type) -> (z:(b -> template_repr a ops)) -> repr_cvar_t a ops

let repr_cvars (cctx:list Type) a ops
  = rcvars:list (repr_cvar_t a ops){L.length cctx = L.length rcvars /\
                                   (forall x . x < L.length rcvars ==> RCVar?.b (L.index rcvars x) == (L.index cctx x))}


(* Equations between the representations of templates *)

noeq type repr_equation (a:Type) (ops:sig) = {
  repr_vctx:list Type;
  repr_cctx:list Type;
  repr_lhs:(vvars repr_vctx) -> (repr_cvars repr_cctx a ops) -> template_repr a ops;
  repr_rhs:(vvars repr_vctx) -> (repr_cvars repr_cctx a ops) -> template_repr a ops
}

let rec to_cvars (#cctx:list Type) #a #ops (rcvars:repr_cvars cctx a ops)
  : cvars cctx a ops 
  = match rcvars with
    | [] -> []
    | (RCVar b z) :: rcvars -> 
        match cctx with
        | b' :: cctx -> (CVar b (reflect_cont #a #b #ops z)) :: to_cvars #cctx #a #ops (admit ()) //rcvars

let to_repr_equation a ops (eq:equation a ops) : repr_equation a ops = {
    repr_vctx = eq.vctx;
    repr_cctx = eq.cctx;
    repr_lhs  = (fun vvars rcvars -> reify (eq.lhs vvars (to_cvars rcvars)));
    repr_rhs  = (fun vvars rcvars -> reify (eq.rhs vvars (to_cvars rcvars)))
}


(* Turning an equation on template representations into to a logical formula *)

let rec eq_to_prop a ops (eq:repr_equation a ops) 
  : Tot prop (decreases %[eq.repr_vctx; eq.repr_cctx])
  = match eq.repr_vctx with
    | [] -> (match eq.repr_cctx with
            | [] -> eq.repr_lhs [] [] == eq.repr_rhs [] []
            | b :: cctx -> 
                forall (z:b -> template_repr a ops) . eq_to_prop a ops ({ repr_vctx = eq.repr_vctx; 
                                                                    repr_cctx = cctx;
                                                                    repr_lhs  = (fun vvars rcvars -> eq.repr_lhs vvars (RCVar b z :: rcvars));
                                                                    repr_rhs  = (fun vvars rcvars -> eq.repr_rhs vvars (RCVar b z :: rcvars)) }))
    | b :: vctx -> 
        forall (x:b) . eq_to_prop a ops ({ repr_vctx = vctx; 
                                      repr_cctx = eq.repr_cctx;
                                      repr_lhs  = (fun vvars rcvars -> eq.repr_lhs (VVar b x :: vvars) rcvars);
                                      repr_rhs  = (fun vvars rcvars -> eq.repr_rhs (VVar b x :: vvars) rcvars) })
