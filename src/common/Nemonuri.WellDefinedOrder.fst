module Nemonuri.WellDefinedOrder

open FStar.Order
module Td = Nemonuri.Transitive.Decidable

type comparer_t (a_t:eqtype) = a_t -> a_t -> order


type binrel_t #a_t (comparer:comparer_t a_t) (o:order) =
  binrel:(Td.binrel_t a_t){ forall x y. (binrel x y) <==> (comparer x y = o) }

let to_binrel #a_t (comparer:comparer_t a_t) (o:order) 
  : binrel_t comparer o =
  fun x y -> comparer x y = o

(* Note: 뭔가....'이름'이 마음에 안 들어! *)
type binrel_not_t #a_t (comparer:comparer_t a_t) (o:order) =
  binrel:(Td.binrel_t a_t){ forall x y. (binrel x y) <==> (comparer x y <> o) }

let to_binrel_not #a_t (comparer:comparer_t a_t) (o:order)
  : binrel_not_t comparer o =
  fun x y -> comparer x y <> o

let to_is_equal #a_t (comparer:comparer_t a_t) : binrel_t comparer Eq = to_binrel comparer Eq

let to_is_less #a_t (comparer:comparer_t a_t) : binrel_t comparer Lt = to_binrel comparer Lt

let to_is_less_or_equal #a_t (comparer:comparer_t a_t) : binrel_not_t comparer Gt = to_binrel_not comparer Gt


(* a strict partial order [<] is a strict weak order if and only if its induced incomparability relation is an equivalence relation. *)
let is_lt_incomparable_at #a_t (comparer:comparer_t a_t) (x y:a_t) : bool =
  let is_less = to_is_less comparer in
  (not (is_less x y)) && (not (is_less y x))

let is_lt_incomparable_eq_at #a_t (comparer:comparer_t a_t) (x y:a_t) : bool =
  let is_equal = to_is_equal comparer in
  (is_lt_incomparable_at comparer x y) = (is_equal x y)

let lemma_is_lt_incomparable_eq_at #a_t (comparer:comparer_t a_t) (x y:a_t)
  : Lemma (requires is_lt_incomparable_eq_at comparer x y)
          (ensures (~(to_binrel comparer Lt x y) /\ ~(to_binrel comparer Lt y x)) <==> (to_binrel comparer Eq x y))
  = ()

let is_lt_incomparable_eq #a_t (comparer:comparer_t a_t) : prop =
  forall x y. is_lt_incomparable_eq_at #a_t comparer x y


unfold let is_comparer_eq_equivalence #a_t (comparer:comparer_t a_t) : prop =
  let is_equal = to_is_equal comparer in
  (Td.is_transitive is_equal) /\ (Td.is_symmetric is_equal) /\ (Td.is_reflexive is_equal)

unfold let is_comparer_lt_strict_partial_order #a_t (comparer:comparer_t a_t) : prop =
  let is_less = to_is_less comparer in
  (Td.is_transitive is_less) /\ (Td.is_irreflexive is_less)

unfold let is_comparer_lt_strict_weak_order #a_t (comparer:comparer_t a_t) : prop =
  (is_comparer_lt_strict_partial_order comparer) /\ (is_lt_incomparable_eq comparer)

unfold let is_comparer_well_defined #a_t (comparer:comparer_t a_t) : prop =
  (is_comparer_eq_equivalence comparer) /\ (is_comparer_lt_strict_weak_order comparer)

noeq type t (a_t:eqtype) = {
  comparer: comparer_t a_t;
  lemma_well_defined: squash (is_comparer_well_defined comparer);
}




