module Nemonuri.Transitive

(* Refernce: https://en.wikipedia.org/wiki/Transitive_relation *)

type binrel_t (a_t:Type) = a_t -> a_t -> Type

//unfold
let is_transitive_at #a_t (binrel:binrel_t a_t) (x y z:a_t) : prop =
  (binrel x y) /\ (binrel y z) ==> (binrel x z)

let is_transitive #a_t (binrel:binrel_t a_t) : prop =
  forall x y z. is_transitive_at binrel x y z

(* The converse (inverse) of a transitive relation is always transitive *)
let to_converse #a_t (binrel:binrel_t a_t) : binrel_t a_t =
  fun x y -> binrel y x

let lemma_to_converse #a_t (binrel:binrel_t a_t)
  : Lemma (requires is_transitive binrel)
          (ensures binrel |> to_converse |> is_transitive)
  = 
  let pr = is_transitive binrel in
  let pq = binrel |> to_converse |> is_transitive in
  let open FStar.Tactics.V2 in
  assert (pr ==> pq) by (
    norm [delta_only [`%is_transitive; `%is_transitive_at]]
  ) (* Note: ...왜 이러니까 증명이 돼? 대체 왜? *)
  
(* The intersection of two transitive relations is always transitive *)
let to_intersection #a_t (binrel1: binrel_t a_t) (binrel2: binrel_t a_t) 
  : binrel_t a_t =
  fun x y -> (binrel1 x y) /\ (binrel2 y x)

let lemma_to_intersection #a_t (binrel1: binrel_t a_t) (binrel2: binrel_t a_t) 
  : Lemma (requires is_transitive binrel1 /\ is_transitive binrel2)
          (ensures to_intersection binrel1 binrel2 |> is_transitive)
  =
  let pr = is_transitive binrel1 /\ is_transitive binrel2 in
  let pq = to_intersection binrel1 binrel2 |> is_transitive in
  let open FStar.Tactics.V2 in
  assert (pr ==> pq) by (
    norm [delta_only [`%is_transitive; `%is_transitive_at]]
  )

(* The union of two transitive relations need not be transitive *)
let to_union #a_t (binrel1: binrel_t a_t) (binrel2: binrel_t a_t) 
  : binrel_t a_t =
  fun x y -> (binrel1 x y) \/ (binrel2 y x)

let lemma_to_union ()
  : Lemma (~(forall (a_t: Type) (binrel1: binrel_t a_t) (binrel2: binrel_t a_t).
            (is_transitive binrel1 /\ is_transitive binrel2) ==>
            (to_union binrel1 binrel2 |> is_transitive)))
  = 
  let open FStar.Classical in
  let equal_to1 (x:(int & int)) (y:(int & int)) : prop = x._1 == y._1 in
  assert (is_transitive equal_to1);
  let equal_to2 (x:(int & int)) (y:(int & int)) : prop = x._2 == y._2 in
  assert (is_transitive equal_to2);
  let equal_to: binrel_t (int & int) = to_union equal_to1 equal_to2 in
  let lemma_equal_to_is_not_transitive' ()
    : Lemma (requires is_transitive equal_to) (ensures False) =
    let p = (equal_to (1, 2) (1, 3)) /\ (equal_to (1, 3) (2, 3)) in
    let c = (equal_to (1, 2) (2, 3)) in
    let open FStar.Tactics.V2 in
    assert ((is_transitive equal_to) ==> p ==> c) by (
      norm [delta_only [`%is_transitive; `%is_transitive_at]]
    )
  in
  move_requires lemma_equal_to_is_not_transitive' ();
  assert (~(is_transitive (to_union equal_to1 equal_to2)))

(* The complement of a transitive relation need not be transitive *)
let to_complement #a_t (binrel: binrel_t a_t)
  : binrel_t a_t =
  fun x y -> ~(binrel x y)

let lemma_to_complement ()
  : Lemma (~(forall (a_t: Type) (binrel: binrel_t a_t).
            (is_transitive binrel) ==>
            (to_complement binrel |> is_transitive)))
  = 
  (* For instance, while "equal to" is transitive, "not equal to" is only transitive on sets with at most one element. *)
  let open FStar.Classical in
  let equal_to (x:int) (y:int) : prop = x == y in
  assert (is_transitive equal_to);
  let not_equal_to : binrel_t int = to_complement equal_to in
  let lemma_not_equal_to_is_not_transitive' ()
    : Lemma (requires is_transitive not_equal_to) (ensures False) =
    let p = (not_equal_to 1 2) /\ (not_equal_to 2 1) in
    let c = (not_equal_to 1 1) in
    let open FStar.Tactics.V2 in
    assert ((is_transitive not_equal_to) ==> p ==> c) by (
      norm [delta_only [`%is_transitive; `%is_transitive_at]]
    )
  in
  move_requires lemma_not_equal_to_is_not_transitive' ();
  assert (~(is_transitive (to_complement equal_to)))

//--- irreflexivity (1) and transitivity (2) together imply asymmetry (3) ---
(* Reference: https://en.wikipedia.org/wiki/Weak_ordering#Total_preorders *)

let is_irreflexive #a_t (binrel: binrel_t a_t) : prop =
  forall x. ~(binrel x x)

let is_asymmetric #a_t (binrel: binrel_t a_t) : prop =
  forall x y. (binrel x y) ==> ~(binrel y x)

let lemma_transitivity_irreflexivity_imply_asymmetry #a_t (binrel: binrel_t a_t)
  : Lemma (requires is_transitive binrel /\ is_irreflexive binrel)
          (ensures is_asymmetric binrel)
  = 
  let open FStar.Classical in
  let is_asymmetric_at (x:a_t) (y:a_t): prop = (binrel x y) ==> ~(binrel y x) in
  let lemma_is_asymmetric_at' (x:a_t) (y:a_t) : Lemma (is_asymmetric_at x y) =
    let lemma_aux' () : Lemma (requires binrel x y) (ensures ~(binrel y x)) =
      let lemma_contradiction' () : Lemma (requires (binrel y x)) (ensures False) =
        let open FStar.Calc in
        calc (==>) {
          is_transitive binrel;
          ==> { admit () }
          (binrel x y) /\ (binrel y x) ==> (binrel x x);
          ==> { give_witness_from_squash #((binrel x y) /\ (binrel y x)) () }
          (binrel x x);
          ==> { give_witness_from_squash #(is_irreflexive binrel) () }
          False;
        }
      in
      move_requires lemma_contradiction' ()
    in
    move_requires lemma_aux' ()
  in
  forall_intro_2 lemma_is_asymmetric_at'

let lemma_asymmetry_imply_irreflexivity #a_t (binrel: binrel_t a_t)
  : Lemma (requires is_asymmetric binrel)
          (ensures is_irreflexive binrel)
  =
  let open FStar.Classical in
  let lemma_aux' (x: a_t): Lemma (requires binrel x x) (ensures False) =
    let open FStar.Calc in
    calc (==>) {
      is_asymmetric binrel;
      ==> {}
      (binrel x x) ==> ~(binrel x x);
      ==> { give_witness_from_squash #(binrel x x) () }
      ~(binrel x x);
      ==> { give_witness_from_squash #(binrel x x) () }
      (binrel x x) /\ ~(binrel x x);
      ==> {}
      False;
    }
  in
  lemma_aux' |> move_requires |> forall_intro
//---|