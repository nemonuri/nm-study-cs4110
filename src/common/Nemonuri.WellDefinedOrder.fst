module Nemonuri.WellDefinedOrder

open FStar.Order

type comparer_t (a_t:Type) = a_t -> a_t -> order

//--- transive order ---
let is_transitive_at
  #a_t (comparer:comparer_t a_t) (o:order) (x:a_t) (y:a_t) (z:a_t) 
  : bool =
  (not ((comparer x y = o) && (comparer y z = o))) || (comparer x z = o)

let lemma_is_transitive_at
  #a_t (comparer:comparer_t a_t) (o:order) (x:a_t) (y:a_t) (z:a_t) 
  : Lemma (requires is_transitive_at comparer o x y z)
          (ensures ((comparer x y = o) /\ (comparer y z = o)) ==> (comparer x z = o))
  = ()

let is_transitive_for
  #a_t (comparer:comparer_t a_t) (o:order) : prop =
  forall x y z. is_transitive_at comparer o x y z

let is_transitive #a_t (comparer:comparer_t a_t) : prop =
  forall o. is_transitive_for comparer o

(*
let lemma_is_transitive #a_t (comparer:comparer_t a_t)
  : Lemma (requires is_transitive comparer)
          (ensures (forall o. is_transitive_for comparer o))
  =
  assume (is_transitive_for comparer Gt)
*)
//---|

//--- equivalence relation ---
let is_equal #a_t (comparer:comparer_t a_t) (x:a_t) (y:a_t) : bool =
  comparer x y |> eq

let is_symmetric_at #a_t (comparer:comparer_t a_t) (x:a_t) (y:a_t) : bool =
  (not (is_equal comparer x y)) || (is_equal comparer y x)

let lemma_is_symmetric_at #a_t (comparer:comparer_t a_t) (x:a_t) (y:a_t)
  : Lemma (requires is_symmetric_at comparer x y) 
          (ensures (is_equal comparer x y) ==> (is_equal comparer y x))
  = ()

let is_symmetric #a_t (comparer:comparer_t a_t) : prop =
  forall x y. is_symmetric_at comparer x y

let is_reflexive_at
  #a_t (comparer:comparer_t a_t) (x:a_t) : bool =
  is_equal comparer x x

let is_reflexive
  #a_t (comparer:comparer_t a_t) : prop =
  forall x. is_reflexive_at comparer x
//---|

//--- strict weak order ---
(* Refernce: https://en.wikipedia.org/wiki/Weak_ordering *)
let is_less #a_t (comparer:comparer_t a_t) (x:a_t) (y:a_t) : bool =
  comparer x y |> lt

let is_asymmetric_at #a_t (comparer:comparer_t a_t) (x:a_t) (y:a_t) : bool =
  (not (is_less comparer x y)) || (not (is_less comparer y x))

let lemma_is_asymmetric_at #a_t (comparer:comparer_t a_t) (x:a_t) (y:a_t)
  : Lemma (requires is_asymmetric_at comparer x y) 
          (ensures (is_less comparer x y) ==> (not (is_less comparer y x)))
  = ()

let is_asymmetric #a_t (comparer:comparer_t a_t) : prop =
  forall x y. is_asymmetric_at comparer x y

let is_irreflexive_at
  #a_t (comparer:comparer_t a_t) (x:a_t) : bool =
  not (is_less comparer x x)

let is_irreflexive
  #a_t (comparer:comparer_t a_t) : prop =
  forall x. is_irreflexive_at comparer x

let lemma_asymmetry_imply_irreflexivity #a_t (comparer:comparer_t a_t)
  : Lemma (requires is_asymmetric comparer) (ensures is_irreflexive comparer) =
  let open FStar.Classical in
  let is_less_p x y: prop = is_less comparer x y in
  let lemma_is_less_p (x:a_t) (y:a_t) 
    : Lemma (requires (is_less_p x y)) (ensures ~(is_less_p y x)) =
    assert (is_less comparer x y);
    assert (is_asymmetric_at comparer x y); (* Note: 가장 중요한 trigger! *)
    assert (not (is_less comparer y x))
  in
  lemma_is_less_p |> move_requires_2 |> forall_intro_2;
  Nemonuri.Transitive.lemma_asymmetry_imply_irreflexivity is_less_p

let is_incomparable_at #a_t (comparer:comparer_t a_t) (x:a_t) (y:a_t) : bool =
  (not (is_less comparer x y)) && (not (is_less comparer x y))

//let is_incomparable_transive_at #a_t (comparer:comparer_t a_t) (x:a_t) (y:a_t) (z:a_t) : bool =


//---|

let is_well_defined #a_t (comparer:comparer_t a_t) : prop =
  (is_transitive comparer) /\
  (is_symmetric comparer) /\ (is_reflexive comparer) /\
  (is_irreflexive comparer) /\ (is_asymmetric comparer)







