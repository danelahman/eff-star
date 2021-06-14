module Eff.Template.Equation

open Eff.Signature
open Eff.Template
open Eff.Template.Equiv

module L = FStar.List.Tot

(* *************************** *)
(* Equations between templates *)
(* *************************** *)

(* Value contexts and value variables *)

let vctx = list Type0

noeq type vvar_t =
  | VVar : (a:Type0) -> (x:a) -> vvar_t

let vvars_pred (vctx:vctx) (vvars:list vvar_t)
  = L.length vctx = L.length vvars /\
    (forall x . x < L.length vvars ==> VVar?.a (L.index vvars x) == (L.index vctx x))

let vvars vctx 
  = vvars:list vvar_t{vvars_pred vctx vvars}

let vvar #vctx (vvars:vvars vctx) (x:nat{x < L.length vctx}) 
  : (L.index vctx x)
  = VVar?.x (L.index vvars x)


(* Compuation contexts and compuation variables *)

let cctx = list Type0

noeq type cvar_t (cctx:cctx) =
  | CVar : (x:nat{x < L.length cctx}) -> L.index cctx x -> cvar_t cctx

let cvar (#cctx:cctx) (x:nat{x < L.length cctx}) (t:L.index cctx x) 
  : cvar_t cctx
  = CVar x t


(* Equations between (direct-style, effectful) templates *)

noeq type equation (ops:sig) = {
  vctx:vctx;
  cctx:cctx;
  lhs:(vvars vctx) -> Template (cvar_t cctx) ops;
  rhs:(vvars vctx) -> Template (cvar_t cctx) ops
}


(* Equations between (representations of) templates *)

noeq type template_equation (ops:sig) = {
  tvctx:vctx;
  tcctx:cctx;
  tlhs:(vvars tvctx) -> template (cvar_t tcctx) ops;
  trhs:(vvars tvctx) -> template (cvar_t tcctx) ops
}


(* Translate a direct-style, effectful equation to a representation equation *)

let to_template_equation #ops (eq:equation ops)
  : template_equation ops
  = {
      tvctx = eq.vctx;
      tcctx = eq.cctx;
      tlhs  = (fun vvars -> reify (eq.lhs vvars));
      trhs  = (fun vvars -> reify (eq.rhs vvars));
    }


(* Intatiated template equations *)

noeq type inst_cvar_t a ops =
  | ICVar : (b:Type0) -> (z:(b -> template a ops)) -> inst_cvar_t a ops

let inst_cvars_pred (cctx:cctx) a ops (cvars:list (inst_cvar_t a ops))
  = L.length cctx = L.length cvars /\
    (forall x . x < L.length cvars ==> ICVar?.b (L.index cvars x) == (L.index cctx x))

let inst_cvars cctx a ops
  = cvars:list (inst_cvar_t a ops){inst_cvars_pred cctx a ops cvars}

noeq type inst_equation (a:Type) (ops:sig) = {
  ivctx:vctx;
  icctx:cctx;
  ilhs:(vvars ivctx) -> (inst_cvars icctx a ops) -> template a ops;
  irhs:(vvars ivctx) -> (inst_cvars icctx a ops) -> template a ops
}


(* Intatiating a template equation (lhs/rhs) with a handler *)

let rec to_inst_template #a #ops #ops' #cctx
  (t:template (cvar_t cctx) ops)
  (h:template_handler ops a ops')
  (cvars:inst_cvars cctx a ops')
  : template a ops'
  = match t with
    | Leaf (CVar x u) ->
        ICVar?.z (L.index cvars x) u
    | Node op x k -> 
        h op x (fun y -> to_inst_template (k y) h cvars)

let to_inst_equation #a #ops #ops'
  (eq:template_equation ops)
  (h:template_handler ops a ops')
  : inst_equation a ops' 
  = {
      ivctx = eq.tvctx;
      icctx = eq.tcctx;
      ilhs  = (fun vvars -> to_inst_template (eq.tlhs vvars) h);
      irhs  = (fun vvars -> to_inst_template (eq.trhs vvars) h)
    }


(* Turning an (instantiated) template equation into to a logical formula *)

let rec eq_to_prop #a #ops (eq:inst_equation a ops) 
  : Tot Type0 (decreases %[eq.ivctx; eq.icctx])
  = match eq.ivctx with
    | [] -> (match eq.icctx with
            | [] -> eq.ilhs [] [] `equiv` eq.irhs [] []
            | b :: cctx -> 
                forall (z:b -> template a ops) . 
                    eq_to_prop ({ ivctx = eq.ivctx; 
                                  icctx = cctx;
                                  ilhs  = (fun vvars rcvars -> eq.ilhs vvars (ICVar b z :: rcvars));
                                  irhs  = (fun vvars rcvars -> eq.irhs vvars (ICVar b z :: rcvars)) }))
    | b :: vctx -> 
        forall (x:b) . 
            eq_to_prop ({ ivctx = vctx; 
                          icctx = eq.icctx;
                          ilhs  = (fun vvars rcvars -> eq.ilhs (VVar b x :: vvars) rcvars);
                          irhs  = (fun vvars rcvars -> eq.irhs (VVar b x :: vvars) rcvars) })

