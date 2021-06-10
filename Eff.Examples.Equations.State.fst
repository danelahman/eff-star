module Eff.Examples.Equations.State

module S = Eff.Signature

open Eff.Examples.IntState

open FStar.FunctionalExtensionality

open FStar.Tactics // temporary






assume val st : Type

let t a = st -> a * st

let return #a (x:a) 
  : t a 
  = fun s -> x , s

let read #a (k:st -> t a) 
  : t a 
  = fun s -> k s s

let write #a (s:st) (k:unit -> t a)
  : t a
  = fun _ -> k () s


let st_eq1 #a s (z:st -> t a)
  : Lemma (normalize (write s (fun _ -> read z) == write s (fun _ -> z s))) 
  = ()

let st_eq2 #a s s' (z:unit -> t a)
  : Lemma (normalize (write s (fun _ -> write s' z) == write s' z))
  = ()

let st_eq3 #a (z:unit -> t a)
  : Lemma (normalize (read (fun s -> write s z) == z ()))
  = admit ()

let st_eq3' #a (z:unit -> t a)
  : Lemma (normalize (read (fun s -> write s z) == (fun s -> z () s)))
  = ()








(*


assume val st : Type

let t a = st ^-> a * st

let return #a (x:a) 
  : t a 
  = on st (fun s -> x , s)

let read #a (k:st -> t a) 
  : t a 
  = on st (fun s -> k s s)

let write #a (s:st) (k:unit -> t a)
  : t a
  = on st (fun _ -> k () s)


let st_eq1 #a s (z:st ^-> t a)
  : Lemma (normalize (write s (fun _ -> read z) == write s (fun _ -> z s)))
  = ()

let st_eq2 #a s s' (z:unit ^-> t a)
  : Lemma (normalize (write s (fun _ -> write s' z) == write s' z))
  = ()

let st_eq3 #a (z:unit ^-> t a)
  : Lemma (normalize (read (fun s -> write s z) == z ()))
  = ();
    assert (feq (fun s -> z () s) (z ())


*)


