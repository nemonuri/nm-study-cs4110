module Nemonuri.Transitive.Decidable

module Un = Nemonuri.Transitive

type binrel_t (a_t:eqtype) = a_t -> a_t -> bool


let to_undecidable #a_t (binrel:binrel_t a_t) : Un.binrel_t a_t =
  fun x y -> b2t (binrel x y)

let is_transitive_at #a_t (binrel:binrel_t a_t) (x:a_t) (y:a_t) (z:a_t) : bool =
  (not ((binrel x y) && (binrel y z))) || (binrel x z)

let lemma_is_transitive_at #a_t (binrel:binrel_t a_t) (x:a_t) (y:a_t) (z:a_t)
  : Lemma ((is_transitive_at binrel x y z) <==> (Un.is_transitive_at (to_undecidable binrel) x y z))
  = ()

let is_transitive #a_t (binrel:binrel_t a_t) : prop =
  forall x y z. is_transitive_at binrel x y z

let lemma_is_transitive #a_t (binrel:binrel_t a_t)
  : Lemma ((is_transitive binrel) <==> (Un.is_transitive (to_undecidable binrel)))
  = 
  let open FStar.Classical in
  forall_intro_3 (lemma_is_transitive_at binrel)

let to_union #a_t (binrel1: binrel_t a_t) (binrel2: binrel_t a_t) 
  : binrel_t a_t =
  fun x y -> (binrel1 x y) || (binrel2 x y)

//--- symmetric ---
let is_symmetric_at #a_t (binrel:binrel_t a_t) (x y:a_t) : bool =
  (not (binrel x y)) || (binrel y x)

let lemma_is_symmetric_at #a_t (binrel:binrel_t a_t) (x y:a_t)
  : Lemma ((is_symmetric_at binrel x y) <==> (Un.is_symmetric_at (to_undecidable binrel) x y))
  = ()

let is_symmetric #a_t (binrel:binrel_t a_t) : prop =
  forall x y. is_symmetric_at binrel x y

let lemma_is_symmetric #a_t (binrel:binrel_t a_t) (x y:a_t)
  : Lemma ((is_symmetric binrel) <==> (Un.is_symmetric (to_undecidable binrel)))
  = 
  FStar.Classical.forall_intro_2 (lemma_is_symmetric_at binrel)
//---|

//--- antisymmetric ---
let is_antisymmetric_at #a_t (binrel:binrel_t a_t) (x y:a_t) : bool =
  (not ((binrel x y) && (binrel y x))) || (x = y)

let lemma_is_antisymmetric_at #a_t (binrel:binrel_t a_t) (x y:a_t)
  : Lemma ((is_antisymmetric_at binrel x y) <==> (Un.is_antisymmetric_at (to_undecidable binrel) x y))
  = ()

let is_antisymmetric #a_t (binrel:binrel_t a_t) : prop =
  forall x y. is_antisymmetric_at binrel x y

let lemma_is_antisymmetric #a_t (binrel:binrel_t a_t) (x y:a_t)
  : Lemma ((is_antisymmetric binrel) <==> (Un.is_antisymmetric (to_undecidable binrel)))
  = 
  FStar.Classical.forall_intro_2 (lemma_is_antisymmetric_at binrel)
//---|

//--- reflexive ---
let is_reflexive_at #a_t (binrel:binrel_t a_t) (x: a_t) : bool = binrel x x

let lemma_is_reflexive_at #a_t (binrel:binrel_t a_t) (x: a_t)
  : Lemma ((is_reflexive_at binrel x) <==> (Un.is_reflexive_at (to_undecidable binrel) x))
  = ()

let is_reflexive #a_t (binrel:binrel_t a_t) : prop = 
  forall x. is_reflexive_at binrel x

let lemma_is_reflexive #a_t (binrel:binrel_t a_t)
  : Lemma ((is_reflexive binrel) <==> (Un.is_reflexive (to_undecidable binrel)))
  =
  FStar.Classical.forall_intro (lemma_is_reflexive_at binrel)
//---|

//--- irreflexive ---
let is_irreflexive_at #a_t (binrel:binrel_t a_t) (x: a_t) : bool = not (binrel x x)

let lemma_is_irreflexive_at #a_t (binrel:binrel_t a_t) (x: a_t)
  : Lemma ((is_irreflexive_at binrel x) <==> (Un.is_irreflexive_at (to_undecidable binrel) x))
  = ()

let is_irreflexive #a_t (binrel:binrel_t a_t) : prop = 
  forall x. is_irreflexive_at binrel x

let lemma_is_irreflexive #a_t (binrel:binrel_t a_t)
  : Lemma ((is_irreflexive binrel) <==> (Un.is_irreflexive (to_undecidable binrel)))
  =
  FStar.Classical.forall_intro (lemma_is_irreflexive_at binrel)
//---|

//--- asymmetric ---
let is_asymmetric_at #a_t (binrel:binrel_t a_t) (x y: a_t) : bool =
  (not (binrel x y)) || (not (binrel y x))

let lemma_is_asymmetric_at #a_t (binrel:binrel_t a_t) (x y: a_t)
  : Lemma ((is_asymmetric_at binrel x y) <==> (Un.is_asymmetric_at (to_undecidable binrel) x y))
  = ()

let is_asymmetric #a_t (binrel:binrel_t a_t) : prop = 
  forall x y. is_asymmetric_at binrel x y

let lemma_is_asymmetric #a_t (binrel:binrel_t a_t)
  : Lemma ((is_asymmetric binrel) <==> (Un.is_asymmetric (to_undecidable binrel)))
  =
  FStar.Classical.forall_intro_2 (lemma_is_asymmetric_at binrel)
//---|

//--- total ---
let is_total_at #a_t (binrel:binrel_t a_t) (x y: a_t) : bool =
          (x = y) || ((binrel x y) || (binrel y x))
  (* not (x <> y) *)

let lemma_is_total_at #a_t (binrel:binrel_t a_t) (x y: a_t)
  : Lemma ((is_total_at binrel x y) <==> (Un.is_total_at (to_undecidable binrel) x y))
  = ()

let is_total #a_t (binrel:binrel_t a_t) : prop = 
  forall x y. is_total_at binrel x y

let lemma_is_total #a_t (binrel:binrel_t a_t)
  : Lemma ((is_total binrel) <==> (Un.is_total (to_undecidable binrel)))
  =
  FStar.Classical.forall_intro_2 (lemma_is_total_at binrel)
//---|

//--- right euclidean ---
let is_right_euclidean_at #a_t (binrel:binrel_t a_t) (x:a_t) (y:a_t) (z:a_t) : bool =
  (not ((binrel x y) && (binrel x z))) || (binrel y z)

let lemma_is_right_euclidean_at #a_t (binrel:binrel_t a_t) (x:a_t) (y:a_t) (z:a_t)
  : Lemma ((is_right_euclidean_at binrel x y z) <==> (Un.is_right_euclidean_at (to_undecidable binrel) x y z))
  = ()

let is_right_euclidean #a_t (binrel:binrel_t a_t) : prop =
  forall x y z. is_right_euclidean_at binrel x y z

let lemma_is_right_euclidean #a_t (binrel:binrel_t a_t)
  : Lemma ((is_right_euclidean binrel) <==> (Un.is_right_euclidean (to_undecidable binrel)))
  = 
  let open FStar.Classical in
  forall_intro_3 (lemma_is_right_euclidean_at binrel)
//---|

let lemma_transitivity_irreflexivity_imply_asymmetry #a_t (binrel: binrel_t a_t)
  : Lemma (requires is_transitive binrel /\ is_irreflexive binrel)
          (ensures is_asymmetric binrel)
  =
  lemma_is_transitive binrel;
  lemma_is_irreflexive binrel;
  Un.lemma_transitivity_irreflexivity_imply_asymmetry (to_undecidable binrel);
  lemma_is_asymmetric binrel

let lemma_asymmetry_imply_irreflexivity #a_t (binrel: binrel_t a_t)
  : Lemma (requires is_asymmetric binrel)
          (ensures is_irreflexive binrel)
  =
  lemma_is_asymmetric binrel;
  Un.lemma_asymmetry_imply_irreflexivity (to_undecidable binrel);
  lemma_is_irreflexive binrel

let lemma_symmetric_and_transitive_is_right_euclidean_at
  #a_t (binrel: binrel_t a_t) (x y z:a_t)
  : Lemma (requires (is_symmetric_at binrel x y) /\
                    (is_transitive_at binrel x y z) /\ (is_transitive_at binrel y x z))
          (ensures is_right_euclidean_at binrel x y z)
  = ()