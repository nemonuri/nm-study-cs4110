module Lecture02.Meta.TSet

(*
Mathematical Preliminaries

Binary Relations

The product of two sets A and B, written A × B, 
contains all ordered pairs (a,b) with a ∈ A and b ∈ B.

Abinary relation on A andBisjustasubsetR ⊆ A × B.
*)

module Set = FStar.TSet

let (∈) (#a_t:Type) (elt:a_t) (set:Set.set a_t) = Set.mem elt set
   
let product (#a_t:Type) (#b_t:Type) (set_a:Set.set a_t) (set_b:Set.set b_t)
  : Set.set (a_t & b_t) =
  let indicate (x:(a_t & b_t)) : prop = 
    (fst x ∈ set_a) /\ (snd x ∈ set_b)
  in
  Set.intension indicate

(* Note: A `×` B *)
let × = product

let binary_relation_condition 
  #a_t #b_t 
  (set_a:Set.set a_t) (set_b:Set.set b_t)
  (x:(Set.set (a_t & b_t)))
  : prop =
  Set.subset x (set_a `×` set_b)
  
type binary_relation_t #a_t #b_t (set_a:Set.set a_t) (set_b:Set.set b_t) =
  x:(Set.set (a_t & b_t)){binary_relation_condition set_a set_b x}