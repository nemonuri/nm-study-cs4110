module Nemonuri.Transitive.Decidable

module Un = Nemonuri.Transitive

type binrel_t (a_t:eqtype) = a_t -> a_t -> bool

[@@coercion]
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