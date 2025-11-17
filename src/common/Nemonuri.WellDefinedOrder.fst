module Nemonuri.WellDefinedOrder

open FStar.Order
module Td = Nemonuri.Transitive.Decidable
module Equ = Nemonuri.WellDefined.Equivalence
module Swo = Nemonuri.WellDefined.StrictWeakOrder

type comparer_t (a_t:eqtype) = a_t -> a_t -> order

type binrel_t #a_t (comparer:comparer_t a_t) (o:order) =
  binrel:(Td.binrel_t a_t){ forall x y. (binrel x y) <==> (comparer x y = o) }

let to_binrel #a_t (comparer:comparer_t a_t) (o:order) 
  : binrel_t comparer o =
  fun x y -> comparer x y = o

type binrel2_t #a_t (comparer:comparer_t a_t) (o1 o2:order) =
  binrel:(Td.binrel_t a_t){ 
    forall x y. (binrel x y) <==> ((comparer x y = o1) \/ (comparer x y = o2)) }

let to_binrel_2 #a_t (comparer:comparer_t a_t) (o1 o2:order) 
  : binrel2_t comparer o1 o2 =
  let binrel1 = to_binrel comparer o1 in
  let binrel2 = to_binrel comparer o2 in
  Td.to_union binrel1 binrel2

unfold let is_comparer_eq_well_defined #a_t (comparer:comparer_t a_t) : prop =
  let is_equal = to_binrel comparer Eq in
  (Td.is_transitive is_equal) /\ (Td.is_symmetric is_equal) /\ (Td.is_reflexive is_equal)

unfold let is_comparer_lt_well_defined #a_t (comparer:comparer_t a_t) : prop =
  let is_less: binrel_t comparer Lt = to_binrel comparer Lt in
  (Td.is_transitive is_less) /\ (Td.is_irreflexive is_less) /\
  (Td.is_transitive (Swo.to_incomparable is_less))

unfold let is_comparer_well_defined #a_t (comparer:comparer_t a_t) : prop =
  (is_comparer_eq_well_defined comparer) /\ (is_comparer_lt_well_defined comparer)

noeq type t (a_t:eqtype) = {
  comparer: comparer_t a_t;
  lemma_well_defined: squash (is_comparer_well_defined comparer);
}

let lemma_quasi_antisym_at
  #a_t (wdo:t a_t) (x y:a_t)
  : Lemma (requires (Swo.to_incomparable (to_binrel wdo.comparer Lt) x y))
          (ensures ((to_binrel wdo.comparer Eq) x y))
  = 
  let is_equal = to_binrel wdo.comparer Eq in
  let is_less = to_binrel wdo.comparer Lt in
  assert (~(is_less x y) /\ ~(is_less y x))




