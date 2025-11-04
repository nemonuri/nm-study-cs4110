module Nemonuri.Unique

(*
   Uniqueness quantification
   - https://en.wikipedia.org/wiki/Uniqueness_quantification
*)


let is_unique_element (#dom_t:eqtype) (predicate:dom_t -> prop) (elt:dom_t) : prop =
  (predicate elt) /\ (forall (y:dom_t). (predicate y) <==> (y = elt))

let is_singleton_predicate (#dom_t:eqtype) (predicate:dom_t -> prop) : prop =
  exists (x:dom_t). is_unique_element predicate x
  //exists (x:dom_t). (forall (y:dom_t). (predicate y) <==> (y = x))

type singleton_predicate_t (dom_t:eqtype) = p:(dom_t -> prop){is_singleton_predicate p}

let get_unique_element #dom_t (singleton_predicate:singleton_predicate_t dom_t)
  : GTot (x:dom_t{is_unique_element singleton_predicate x}) =
  FStar.IndefiniteDescription.indefinite_description_ghost dom_t singleton_predicate

