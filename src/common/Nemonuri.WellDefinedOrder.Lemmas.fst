module Nemonuri.WellDefinedOrder.Lemmas

open FStar.Order
open Nemonuri.WellDefinedOrder
module Td = Nemonuri.Transitive.Decidable


let lemma_is_equal_implies_is_less_or_equal #a_t (comparer:comparer_t a_t) (x y:a_t)
  : Lemma (requires to_is_equal comparer x y)
          (ensures to_is_less_or_equal comparer x y)
  = ()

let lemma_'is_equal'_is_right_euclidean #a_t (wdo: t a_t)
  : Lemma (ensures Td.is_right_euclidean (to_is_equal wdo.comparer))
  =
  let open FStar.Classical in
  let is_equal = to_is_equal wdo.comparer in
  let lemma_aux' x y z : Lemma (Td.is_right_euclidean_at is_equal x y z) =
    Td.lemma_symmetric_and_transitive_is_right_euclidean_at is_equal x y z
  in
  forall_intro_3 lemma_aux'

let lemma_'is_less_or_equal'_is_reflexive #a_t (wdo: t a_t)
  : Lemma (Td.is_reflexive (to_is_less_or_equal wdo.comparer)) =
  assert (Td.is_reflexive (to_is_equal wdo.comparer))

let lemma_'is_less_or_equal'_is_total #a_t (wdo: t a_t)
  : Lemma (Td.is_total (to_is_less_or_equal wdo.comparer)) =
  let is_less_or_equal = to_is_less_or_equal wdo.comparer in
  let open FStar.Classical in
  let lemma_aux' x y : Lemma ((is_less_or_equal x y) \/ (is_less_or_equal y x)) =
    match wdo.comparer x y with
    | Lt | Eq -> assert (is_less_or_equal x y)
    | Gt ->
    begin
      let open FStar.Calc in
      let is_less = to_is_less wdo.comparer in
      let lemma_not_is_less' () : Lemma (not (is_less x y)) =
        calc (==>) {
          ~(is_less_or_equal x y);
          ==> {}
          ~((is_less x y) \/ (wdo.comparer x y = Eq));
          ==> {}
          ~(is_less x y) /\ ~(wdo.comparer x y = Eq);
          ==> {}
          ~(is_less x y);
        };
        assert (not (is_less_or_equal x y))
      in
      let lemma_contradiction' () 
        : Lemma (requires not (is_less_or_equal y x)) (ensures False) =
        calc (==>) {
          ~(is_less_or_equal y x);
          ==> {}
          ~(is_less y x);
          ==> { give_witness_from_squash #(~(is_less x y)) (lemma_not_is_less' ()) }
          ~(is_less y x) /\ ~(is_less x y);
          ==> { give_witness_from_squash #((is_lt_incomparable_eq_at wdo.comparer y x) |> b2t) () }
          (wdo.comparer y x = Eq) |> b2t;
          ==> { give_witness_from_squash #((wdo.comparer x y <> Eq)) (
                  (move_requires_2 (lemma_is_equal_implies_is_less_or_equal wdo.comparer) x y);
                  assert (~(is_less_or_equal x y))
                ) }
          (wdo.comparer x y = Eq) /\ (wdo.comparer x y <> Eq);
          ==> {}
          False;
        }
      in
      move_requires lemma_contradiction' ()
    end
  in
  forall_intro_2 lemma_aux'


let lemma_'is_less_or_equal'_is_transitive #a_t (wdo: t a_t)
  : Lemma (Td.is_transitive (to_is_less_or_equal wdo.comparer))
  =
  let is_less_or_equal = to_is_less_or_equal wdo.comparer in
  let is_less = to_is_less wdo.comparer in
  let is_equal = to_is_equal wdo.comparer in
  let open FStar.Classical in
  let open FStar.Calc in
  let lemma_aux' x y z 
    : Lemma (requires (is_less_or_equal x y) /\ (is_less_or_equal y z)) 
            (ensures (is_less_or_equal x z)) 
    =
    lemma_'is_equal'_is_right_euclidean wdo;
    lemma_'is_less_or_equal'_is_total wdo;
    let c: prop = (is_less_or_equal x z) in
    match (wdo.comparer x y, wdo.comparer y z) with
    | (Lt, Lt) -> 
    begin
      assert (is_less x y); assert (is_less y z);
      assert (Td.is_transitive_at is_less x y z); 
      assert (is_less x z)
    end
    | (Eq, Eq) -> 
    begin
      assert (is_equal x y); assert (is_equal y z);
      assert (Td.is_transitive_at is_equal x y z); 
      assert (is_equal x z)
    end
    | (Lt, Eq) ->
    (* (is_less x y) /\ (is_equal y z) *)
    begin
      let lemma_not_equal' () : Lemma (requires (is_equal z x)) (ensures False) =
        calc (==>) {
          (is_equal y z) |> b2t;
          ==> { assert (Td.is_symmetric_at is_equal y z) }
          (is_equal z x) /\ (is_equal z y);
          ==> { assert (Td.is_right_euclidean_at is_equal z x y) }
          (is_equal x y) /\ (is_less x y);
          ==> { assert (Eq <> Lt) }
          False;
        }
      in
      let lemma_contradiction' () 
        : Lemma (requires ~(is_less_or_equal x z)) (ensures False) =
        calc (==>) {
          ~(is_less_or_equal x z);
          ==> { assert (Td.is_total_at is_less_or_equal x z) }
          ~(is_less_or_equal x z) /\ ((x = z) \/ (is_less_or_equal x z) \/ (is_less_or_equal z x));
          ==> {}
          (x = z) \/ (is_less_or_equal z x);
          ==> {}
          (z = x) \/ (is_less z x) \/ (is_equal z x);
          ==> { give_witness_from_squash #((z = x) ==> (is_equal z x)) (assert Td.is_reflexive_at is_equal z) }
          (is_less z x) \/ (is_equal z x);
          ==> { give_witness_from_squash #(~(is_equal z x)) (move_requires lemma_not_equal' ()) }
          (is_less z x) |> b2t;
          ==> { assert (is_less x y) }
          (is_less z x) /\ (is_less x y);
          ==> { assert (Td.is_transitive_at is_less z x y) }
          (is_less z y) |> b2t;
          ==> { give_witness_from_squash #(is_equal z y) (assert (is_equal y z); assert (Td.is_symmetric_at is_equal y z)) }
          (is_less z y) /\ (is_equal z y);
          ==> { assert (Lt <> Eq) }
          False;
        }
      in
      move_requires lemma_contradiction' ()
    end
    | (Eq, Lt) -> 
    (* Note: 이거, (Lt, Eq) 의 경우와 꽤 많이 겹치지 않나? 코드 재사용, 어떻게 안 되나? *)
    (* (is_equal x y) /\ (is_less y z) *)
    begin
      let lemma_not_equal' () : Lemma (requires (is_equal z x)) (ensures False) =
        calc (==>) {
          (is_equal x y (* diff *)) |> b2t;
          ==> { assert (Td.is_symmetric_at is_equal z x (* diff *)) }
          (is_equal x z (* diff *)) /\ (is_equal x y (* diff *));
          ==> { assert (Td.is_right_euclidean_at is_equal x y z (* diff *)) }
          (is_equal y z (* diff *)) /\ (is_less y z (* diff *));
          ==> { assert (Eq <> Lt) }
          False;
        }
      in
      let lemma_contradiction' () 
        : Lemma (requires ~(is_less_or_equal x z)) (ensures False) =
        calc (==>) {
          ~(is_less_or_equal x z);
          ==> { assert (Td.is_total_at is_less_or_equal x z) }
          ~(is_less_or_equal x z) /\ ((x = z) \/ (is_less_or_equal x z) \/ (is_less_or_equal z x));
          ==> {}
          (x = z) \/ (is_less_or_equal z x);
          ==> {}
          (z = x) \/ (is_less z x) \/ (is_equal z x);
          ==> { give_witness_from_squash #((z = x) ==> (is_equal z x)) (assert Td.is_reflexive_at is_equal z) }
          (is_less z x) \/ (is_equal z x);
          ==> { give_witness_from_squash #(~(is_equal z x)) (move_requires lemma_not_equal' ()) }
          (is_less z x) |> b2t;
          ==> { assert (is_less y z (* diff *)) } 
          (is_less z x) /\ (is_less y z (* diff *));
          ==> { assert (Td.is_transitive_at is_less y z x (* diff *)) }
          (is_less y x (* diff *)) |> b2t;
          ==> { give_witness_from_squash #(is_equal y x (* diff *)) (assert (is_equal x y (* diff *)); assert (Td.is_symmetric_at is_equal x y (* diff *))) }
          (is_less y x (* diff *)) /\ (is_equal y x (* diff *));
          ==> { assert (Lt <> Eq) }
          False;
        }
      in
      move_requires lemma_contradiction' ()
    end
  in
  lemma_aux' |> move_requires_3 |> forall_intro_3

type is_equal_transitive_at_intro_t #a_t (comparer:comparer_t a_t) =
  (x:a_t) -> (y:a_t) -> (z:a_t) -> 
  Lemma (requires (to_is_equal comparer x y) /\ (to_is_equal comparer y z)) 
        (ensures (to_is_equal comparer x z))

type is_equal_symmetric_at_intro_t #a_t (comparer:comparer_t a_t) =
  (x:a_t) -> (y:a_t) -> 
  Lemma (requires (to_is_equal comparer x y)) 
        (ensures (to_is_equal comparer y x))

type is_equal_reflexive_at_intro_t #a_t (comparer:comparer_t a_t) =
  (x:a_t) -> Lemma (Td.is_reflexive_at (to_is_equal comparer) x)

type is_less_transitive_at_intro_t #a_t (comparer:comparer_t a_t) =
  (x:a_t) -> (y:a_t) -> (z:a_t) -> 
  Lemma (requires (to_is_less comparer x y) /\ (to_is_less comparer y z))
        (ensures (to_is_less comparer x z))

type is_less_irreflexive_at_intro_t #a_t (comparer:comparer_t a_t) =
  (x:a_t) -> Lemma (Td.is_irreflexive_at (to_is_less comparer) x)

type is_lt_incomparable_eq_right_intro_t #a_t (comparer:comparer_t a_t) =
  (x:a_t) -> (y:a_t) -> 
  Lemma (requires (is_lt_incomparable_at comparer x y))
        (ensures (to_is_equal comparer x y))

type is_lt_incomparable_eq_left_intro_t #a_t (comparer:comparer_t a_t) =
  (x:a_t) -> (y:a_t) -> 
  Lemma (requires (to_is_equal comparer x y))
        (ensures (is_lt_incomparable_at comparer x y))
        

let is_comparer_well_defined_intro
  (#a_t: eqtype)
  (comparer: comparer_t a_t)
  (is_equal_transitive_at_intro: is_equal_transitive_at_intro_t comparer)
  (is_equal_symmetric_at_intro: is_equal_symmetric_at_intro_t comparer)
  (is_equal_reflexive_at_intro: is_equal_reflexive_at_intro_t comparer)
  (is_less_transitive_at_intro: is_less_transitive_at_intro_t comparer)
  (is_less_irreflexive_at_intro: is_less_irreflexive_at_intro_t comparer)
  (is_lt_incomparable_eq_right_intro: is_lt_incomparable_eq_right_intro_t comparer)
  (is_lt_incomparable_eq_left_intro: is_lt_incomparable_eq_left_intro_t comparer)
  : Lemma (is_comparer_well_defined comparer) =
  let open FStar.Classical in
  let is_equal = to_is_equal comparer in
  let is_less = to_is_less comparer in
  let p_goal1 = (Td.is_transitive is_equal) in
  let p_goal2 = (Td.is_symmetric is_equal) in
  let p_goal3 = (Td.is_reflexive is_equal) in
  let p_goal4 = (Td.is_transitive is_less) in
  let p_goal5 = (Td.is_irreflexive is_less) in
  let p_goal6 = (is_lt_incomparable_eq comparer) in
  is_equal_transitive_at_intro |> move_requires_3 |> forall_intro_3;
  assert (p_goal1);
  is_equal_symmetric_at_intro |> move_requires_2 |> forall_intro_2;
  assert (p_goal2);
  is_equal_reflexive_at_intro |> forall_intro;
  assert (p_goal3);
  is_less_transitive_at_intro |> move_requires_3 |> forall_intro_3;
  assert (p_goal4);
  is_less_irreflexive_at_intro |> forall_intro;
  assert (p_goal5);
  is_lt_incomparable_eq_right_intro |> move_requires_2 |> forall_intro_2;
  is_lt_incomparable_eq_left_intro |> move_requires_2 |> forall_intro_2;
  assert (p_goal6)
