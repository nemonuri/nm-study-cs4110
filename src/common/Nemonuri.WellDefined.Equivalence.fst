module Nemonuri.WellDefined.Equivalence

module Td = Nemonuri.Transitive.Decidable

let is_well_defined (#a_t:eqtype) (binrel:Td.binrel_t a_t) : prop =
  (Td.is_transitive binrel) /\ 
  (Td.is_symmetric binrel) /\
  (Td.is_reflexive binrel)

type t (a_t:eqtype) = binrel:(Td.binrel_t a_t){ is_well_defined binrel }

noeq type pack_t = {
  domain_t: eqtype;
  binrel: Td.binrel_t domain_t;
  lemma_is_transitive: squash (Td.is_transitive binrel);
  lemma_is_symmetric: squash (Td.is_symmetric binrel);
  lemma_is_reflexive: squash (Td.is_reflexive binrel);
}

let lemma_pack (pack:pack_t) : Lemma (is_well_defined pack.binrel) = ()

let is_equality_at #a_t (wd_eq:t a_t) (x y:a_t) : bool =
  (wd_eq x y) = (x = y)

let is_equality #a_t (wd_eq:t a_t) : prop =
  forall x y. is_equality_at wd_eq x y

let lemma_is_equality #a_t (wd_eq:t a_t)
  : Lemma (requires is_equality wd_eq)
          (ensures Td.is_antisymmetric wd_eq)
  =
  (* Note: 엥? 이것만으로 증명 끝이라고? *)
  norm_spec [delta_only [`%is_equality; `%is_equality_at]] (is_equality wd_eq)