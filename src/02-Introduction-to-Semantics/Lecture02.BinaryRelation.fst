module Lecture02.BinaryRelation

(*
Mathematical Preliminaries

Binary Relations

The product of two sets A and B, written A × B, 
contains all ordered pairs (a,b) with a ∈ A and b ∈ B.

Abinary relation on A andBisjustasubsetR ⊆ A × B.
*)

open FStar.FunctionalExtensionality { (^->) }
module F = FStar.FunctionalExtensionality

//--- set operations ---
type set_t (a_t:eqtype) = a_t ^-> prop
let is_universe_set #a_t (x:set_t a_t) : prop = F.feq x (fun _ -> True)

type universe_set_t (a_t:eqtype) = x:(set_t a_t){is_universe_set x}
let to_set (a_t:eqtype) : universe_set_t a_t = F.on a_t (fun _ -> True <: prop)

let is_member_of (#a_t:eqtype) (element:a_t) (set:set_t a_t) = set element
let (∈) = is_member_of

let is_subset_of (#a_t:eqtype) (l:set_t a_t) (r:set_t a_t) : prop = forall x. (x ∈ l) ==> (x ∈ r)
let (⊆) = is_subset_of
   
let product (#a_t:eqtype) (#b_t:eqtype) (set_a:set_t a_t) (set_b:set_t b_t)
  : set_t (a_t & b_t) =
  let indicate (x:(a_t & b_t)) : prop = 
    (fst x ∈ set_a) /\ (snd x ∈ set_b)
  in
  F.on (a_t & b_t) indicate
(* Note: A `×` B *)
let × = product

let to_tset #a_t (set:set_t a_t) : FStar.TSet.set a_t = FStar.TSet.intension set
let to_predicate #a_t (set:set_t a_t) : Tot (a_t -> prop) = set
//---|

let is_binary_relation
  #a_t #b_t 
  (set_a:set_t a_t) (set_b:set_t b_t)
  (x:set_t (a_t & b_t))
  : prop 
  =
  x ⊆ (set_a `×` set_b)

type binary_relation_t #a_t #b_t (set_a:set_t a_t) (set_b:set_t b_t) =
  x:(set_t (a_t & b_t)){is_binary_relation set_a set_b x}

let get_domain 
  #a_t #b_t (#set_a:set_t a_t) (#set_b:set_t b_t)
  (binary_relation:binary_relation_t set_a set_b) =
  set_a

let get_codomain 
  #a_t #b_t (#set_a:set_t a_t) (#set_b:set_t b_t)
  (binary_relation:binary_relation_t set_a set_b) =
  set_b


(* Some Important Relations *)

unfold private type br_t' = (domain_t:eqtype) -> (codomain_t:eqtype) -> binary_relation_t (to_set domain_t) (to_set codomain_t)

val empty : br_t'
let empty d c = F.on (d & c) (fun _ -> False <: prop)

val total_ : br_t'
let total_ d c = (to_set d) `×` (to_set c)

val identity : (domain_t:eqtype) -> binary_relation_t (to_set domain_t) (to_set domain_t)
let identity d = F.on (d & d) (fun _ -> True <: prop)

let composition 
  (#a_t:eqtype) (#b_t:eqtype) (#c_t:eqtype) 
  (r:set_t (a_t & b_t)) (s:set_t (b_t & c_t))
  : binary_relation_t (to_set a_t) (to_set c_t) =
  let indicate (a_c:(a_t & c_t)) : prop = 
    let (a, c) = a_c in
    exists (b:b_t). ((a,b) ∈ r) /\ ((b,c) ∈ s)
  in
  F.on (a_t & c_t) indicate

