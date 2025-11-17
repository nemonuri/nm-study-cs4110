module Nemonuri.WellDefined.StrictWeakOrder

module Td = Nemonuri.Transitive.Decidable

let to_incomparable #a_t (binrel:Td.binrel_t a_t) : Td.binrel_t a_t =
  fun x y -> (not (binrel x y)) && (not (binrel y x))

let is_well_defined (#a_t:eqtype) (binrel:Td.binrel_t a_t) : prop =
  (Td.is_transitive binrel) /\ (Td.is_irreflexive binrel) /\
  (Td.is_transitive (to_incomparable binrel))

type t (a_t:eqtype) = binrel:(Td.binrel_t a_t){ is_well_defined binrel }

noeq type pack_t = {
  domain_t: eqtype;
  binrel: Td.binrel_t domain_t;
  lemma_is_transitive: squash (Td.is_transitive binrel);
  lemma_is_irreflexive: squash (Td.is_irreflexive binrel);
  lemma_is_incomparable_transitive: squash (Td.is_transitive (to_incomparable binrel));
}

let lemma_pack (pack:pack_t) : Lemma (is_well_defined pack.binrel) = ()
