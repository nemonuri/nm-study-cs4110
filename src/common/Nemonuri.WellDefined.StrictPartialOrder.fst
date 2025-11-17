module Nemonuri.WellDefined.StrictPartialOrder

module Td = Nemonuri.Transitive.Decidable

let is_well_defined (#a_t:eqtype) (binrel:Td.binrel_t a_t) : prop =
  (Td.is_transitive binrel) /\ (Td.is_irreflexive binrel)

type t (a_t:eqtype) = binrel:(Td.binrel_t a_t){ is_well_defined binrel }

noeq type pack_t = {
  domain_t: eqtype;
  binrel: Td.binrel_t domain_t;
  lemma_is_transitive: squash (Td.is_transitive binrel);
  lemma_is_irreflexive: squash (Td.is_irreflexive binrel);
}

let lemma_pack (pack:pack_t) : Lemma (is_well_defined pack.binrel) = ()