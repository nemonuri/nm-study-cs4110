module Nemonuri.Eqtype.TotalOrder

open FStar.Order

type comparer_t (a_t:eqtype) = a_t -> a_t -> order

let is_less_or_equal #a_t (comparer:comparer_t a_t) (x:a_t) (y:a_t) : bool =
  comparer x y |> le

let is_equal #a_t (comparer:comparer_t a_t) (x:a_t) (y:a_t) : bool =
  comparer x y |> eq

let are_equality_and_identity_same_at 
  #a_t (comparer:comparer_t a_t) (x:a_t) (y:a_t) : bool =
  (is_equal comparer x y) = (x = y)

let lemma_are_equality_and_identity_same_at
  #a_t (comparer:comparer_t a_t) (x:a_t) (y:a_t)
  : Lemma (requires are_equality_and_identity_same_at comparer x y)
          (ensures (is_equal comparer x y) <==> (x = y))
  =
  ()

let are_equality_and_identity_same #a_t (comparer:comparer_t a_t) : prop =
  forall (x y: a_t). (are_equality_and_identity_same_at comparer x y)

let is_anti_symmetry_at 
  #a_t (comparer:comparer_t a_t) (a1:a_t) (a2:a_t) : prop =
  let is_le = is_less_or_equal comparer in
  let is_eq = is_equal comparer in
  (is_le a1 a2 /\ is_le a2 a1) ==> is_eq a1 a2


let is_anti_symmetry #a_t (comparer:comparer_t a_t) : prop =
  forall a1 a2. is_anti_symmetry_at comparer a1 a2


let lemma_anti_symmetry_less_or_equal #a_t (comparer:comparer_t a_t) (x:a_t) (y:a_t)
  : Lemma (requires 
            (is_anti_symmetry comparer) /\ 
            (is_less_or_equal comparer x y) /\ (is_less_or_equal comparer y x))
          (ensures (is_equal comparer x y) /\ (is_equal comparer y x))
  =
  assert (is_anti_symmetry_at comparer x y <==> is_anti_symmetry_at comparer y x)


let is_transive_at 
  #a_t (comparer:comparer_t a_t) (a1:a_t) (a2:a_t) (a3:a_t) : prop =
  let is_le = is_less_or_equal comparer in
  is_le a1 a2 /\ is_le a2 a3 ==> is_le a1 a3

let is_transive #a_t (comparer:comparer_t a_t) : prop =
  forall a1 a2 a3. is_transive_at comparer a1 a2 a3

let is_total_at
  #a_t (comparer:comparer_t a_t) (a1:a_t) (a2:a_t) : prop =
  let is_le = is_less_or_equal comparer in
  is_le a1 a2 \/ is_le a2 a1

let is_total #a_t (comparer:comparer_t a_t) : prop =
  forall a1 a2. is_total_at comparer a1 a2

let is_total_order #a_t (comparer:comparer_t a_t) : prop =
   is_anti_symmetry comparer
 /\ is_transive comparer
 /\ is_total comparer

let is_eqtype_total_order #a_t (comparer:comparer_t a_t) : prop =
  (are_equality_and_identity_same comparer) /\ (is_total_order comparer)


let lemma_is_eqtype_total_order #a_t (comparer:comparer_t a_t)
  : Lemma (requires is_eqtype_total_order comparer)
          (ensures FStar.OrdSet.total_order a_t (is_less_or_equal comparer))
  =
  let open FStar.Classical in
  let is_le = is_less_or_equal comparer in
  let is_eq = is_equal comparer in
  (lemma_are_equality_and_identity_same_at #a_t comparer) |> move_requires_2 |> forall_intro_2;
  assert (forall (a1 a2 :a_t). are_equality_and_identity_same_at comparer a1 a2);
  assert (forall (a1 a2 :a_t). (is_eq a1 a2) <==> (a1 = a2));

  let p1 (a1 a2: a_t): prop = (is_le a1 a2 /\ is_le a2 a1) ==> a1 = a2 in
  let p_goal1 = (forall a1 a2. p1 a1 a2) in
  let lemma_goal1' (a1 a2:a_t) 
    : Lemma (requires is_anti_symmetry_at comparer a1 a2) (ensures p1 a1 a2)
    = ()
  in
  lemma_goal1' |> move_requires_2 |> forall_intro_2;
  assert (p_goal1);

  let p2 (a1 a2 a3: a_t): prop = (is_le a1 a2 /\ is_le a2 a3 ==> is_le a1 a3) in
  let p_goal2 = (forall a1 a2 a3. p2 a1 a2 a3) in
  (* Note: ...이게 'requires' 를 없애는, 가장 좋은 방법인가? *)
  let lemma_goal2' (a1 a2 a3:a_t) : Lemma (ensures p2 a1 a2 a3) =
    let lemma_goal2'' (a1 a2 a3:a_t) : Lemma (requires is_transive_at comparer a1 a2 a3) (ensures p2 a1 a2 a3) = () in
    assert (is_transive_at comparer a1 a2 a3);
    lemma_goal2'' a1 a2 a3
  in
  lemma_goal2' |> forall_intro_3;
  assert (p_goal2);

  let p3 (a1 a2: a_t): prop = (is_le a1 a2 \/ is_le a2 a1) in
  let p_goal3 = (forall a1 a2. p3 a1 a2) in
  let lemma_goal3' (a1 a2:a_t) : Lemma (ensures p3 a1 a2) =
    let lemma_goal3'' (a1 a2:a_t) : Lemma (requires is_total_at comparer a1 a2) (ensures p3 a1 a2) = () in
    assert (is_total_at comparer a1 a2);
    lemma_goal3'' a1 a2
  in
  lemma_goal3' |> forall_intro_2


noeq type t (a_t:eqtype) = {
  comparer: comparer_t a_t;
  properties: squash (is_eqtype_total_order comparer);
}

let to_cmp #a_t (total_order:t a_t) : FStar.OrdSet.cmp a_t = 
  FStar.Classical.move_requires lemma_is_eqtype_total_order total_order.comparer;
  is_less_or_equal total_order.comparer

