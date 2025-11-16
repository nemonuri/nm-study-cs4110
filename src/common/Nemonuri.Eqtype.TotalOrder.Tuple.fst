module Nemonuri.Eqtype.TotalOrder.Tuple

open FStar.Order
open Nemonuri.Eqtype.TotalOrder
module L = FStar.List.Tot


private let to_tuple_comparer_compare' 
  (#left_t: eqtype)
  (#right_t: eqtype)
  (total_order_l: t left_t)
  (total_order_r: t right_t)
  (x: (left_t & right_t)) (y: (left_t & right_t)) : order =
  match total_order_l.comparer x._1 y._1 with
  | Gt -> Gt
  | Lt -> Lt
  | Eq -> total_order_r.comparer x._2 y._2

let to_tuple_comparer 
  (#left_t: eqtype)
  (#right_t: eqtype)
  (total_order_l: t left_t)
  (total_order_r: t right_t)
  : comparer_t (left_t & right_t) =
  to_tuple_comparer_compare' total_order_l total_order_r

let get_order_pair 
  (#left_t: eqtype)
  (#right_t: eqtype)
  (total_order_l: t left_t)
  (total_order_r: t right_t)
  (x: (left_t & right_t)) (y: (left_t & right_t))
  : (order & order) =
  (total_order_l.comparer x._1 y._1, total_order_r.comparer x._2 y._2)

let is_order_pair_lt
  (#left_t: eqtype)
  (#right_t: eqtype)
  (total_order_l: t left_t)
  (total_order_r: t right_t)
  (x: (left_t & right_t)) (y: (left_t & right_t))
  : prop =
  let o = (get_order_pair total_order_l total_order_r x y) in
  (o._1 = Lt) \/ (o = (Eq, Lt))

let lemma_is_order_pair_lt
  (#left_t: eqtype)
  (#right_t: eqtype)
  (total_order_l: t left_t)
  (total_order_r: t right_t)
  (x: (left_t & right_t)) (y: (left_t & right_t))
  : Lemma ((to_tuple_comparer total_order_l total_order_r x y = Lt) <==> (is_order_pair_lt total_order_l total_order_r x y)) =
  ()

let is_order_pair_eq
  (#left_t: eqtype)
  (#right_t: eqtype)
  (total_order_l: t left_t)
  (total_order_r: t right_t)
  (x: (left_t & right_t)) (y: (left_t & right_t))
  : prop =
  let o = (get_order_pair total_order_l total_order_r x y) in
  (o = (Eq, Eq))

let lemma_is_order_pair_eq
  (#left_t: eqtype)
  (#right_t: eqtype)
  (total_order_l: t left_t)
  (total_order_r: t right_t)
  (x: (left_t & right_t)) (y: (left_t & right_t))
  : Lemma ((to_tuple_comparer total_order_l total_order_r x y = Eq) <==> (is_order_pair_eq total_order_l total_order_r x y)) =
  ()

let lemma_is_less_or_equal 
  (#left_t: eqtype)
  (#right_t: eqtype)
  (total_order_l: t left_t)
  (total_order_r: t right_t)
  (x: (left_t & right_t)) (y: (left_t & right_t))
  : Lemma ((is_less_or_equal (to_tuple_comparer total_order_l total_order_r) x y) <==>
           ((is_order_pair_lt total_order_l total_order_r x y) \/ (is_order_pair_eq total_order_l total_order_r x y)))      
  =
  lemma_is_order_pair_lt total_order_l total_order_r x y;
  lemma_is_order_pair_eq total_order_l total_order_r x y


let lemma_to_tuple_comparer
  (#left_t: eqtype)
  (#right_t: eqtype)
  (total_order_l: t left_t)
  (total_order_r: t right_t)
  : Lemma (is_eqtype_total_order (to_tuple_comparer total_order_l total_order_r)) =
  let open FStar.Classical in
  let comparer = to_tuple_comparer total_order_l total_order_r in
  let is_le = is_less_or_equal comparer in
  let is_eq = is_equal comparer in
  let is_le_l = is_less_or_equal total_order_l.comparer in
  let is_eq_l = is_equal total_order_l.comparer in
  let is_le_r = is_less_or_equal total_order_r.comparer in
  let is_eq_r = is_equal total_order_r.comparer in

  let p_goal1: prop = (are_equality_and_identity_same comparer) in
  let lemma_equality' x y
    : Lemma (are_equality_and_identity_same_at comparer x y) =
    assert ((is_eq_l x._1 y._1 /\ is_eq_r x._2 y._2) <==> (is_eq x y));
    assert ((x._1 = y._1) /\ (x._2 = y._2) <==> (x = y));
    assert (
      ((are_equality_and_identity_same_at total_order_l.comparer x._1 y._1) /\ 
      (are_equality_and_identity_same_at total_order_r.comparer x._2 y._2))
      <==>
      (are_equality_and_identity_same_at comparer x y)
    )
  in
  forall_intro_2 lemma_equality';
  assert (p_goal1);

  let p_goal2: prop = (is_anti_symmetry comparer) in
  let lemma_anti_symmetry' x y
    : Lemma (is_anti_symmetry_at comparer x y) =
    let lemma_aux' () : Lemma (requires (is_le x y /\ is_le y x)) (ensures is_eq x y) = 
      lemma_anti_symmetry_less_or_equal total_order_l.comparer x._1 y._1;
      lemma_anti_symmetry_less_or_equal total_order_r.comparer x._2 y._2
    in
    move_requires lemma_aux' ()
  in
  forall_intro_2 lemma_anti_symmetry';
  assert (p_goal2);

  let p_goal3: prop = (is_transive comparer) in
  let lemma_transivity' x y z
    : Lemma (is_transive_at comparer x y z) =
    let lemma_aux' () : Lemma (requires is_le x y /\ is_le y z) (ensures is_le x z) =
      assert (is_transive_at total_order_l.comparer x._1 y._1 z._1) /\ (is_transive_at total_order_r.comparer x._2 y._2 z._2);
      lemma_is_less_or_equal total_order_l total_order_r x y;
      lemma_is_less_or_equal total_order_l total_order_r y z;
      let (xy1, xy2) = get_order_pair total_order_l total_order_r x y in
      let (yz1, yz2) = get_order_pair total_order_l total_order_r y z in
      let (xz1, xz2) = get_order_pair total_order_l total_order_r x z in
      assert ((xy1 |> le) /\ (yz1 |> le));
      assert (xz1 |> le);
      assert ((yz1 = Eq) ==> (yz2 |> le));
      let p_goal3_1: prop = ((xz1, xz2) <> (Eq, Gt)) in
      let lemma_goal3_1' () : Lemma (ensures p_goal3_1) =
        let lemma_aux' () : Lemma (requires (xz1 = Eq)) (ensures (xz2 |> le)) =
          assert (are_equality_and_identity_same total_order_l.comparer);
          lemma_are_equality_and_identity_same_at total_order_l.comparer x._1 z._1;
          assert (x._1 = z._1);
          lemma_are_equality_and_identity_same_at total_order_l.comparer y._1 z._1;
          assume (y._1 = z._1);
          //lemma_are_equality_and_identity_same_at total_order_l.comparer x._1 y._1;
          assert (x._1 = y._1)

          //assert ((xy1 = Eq) /\ (yz1 = Eq))
        in
        move_requires lemma_aux' ()
      in
      lemma_goal3_1' ();
      assert ((is_order_pair_lt total_order_l total_order_r x z) \/ (is_order_pair_eq total_order_l total_order_r x z))
    in
    move_requires lemma_aux' ()
  in
  forall_intro_3 lemma_transivity';
  assert (p_goal3);

  let p_goal4: prop = (is_total comparer) in
  //forall_intro_2 (lemma_to_either_comparer_total total_order_l total_order_g);
  assume (p_goal4)


let to_tuple
  (#left_t: eqtype)
  (#right_t: eqtype)
  (total_order_l: t left_t)
  (total_order_r: t right_t)
  : t (left_t & right_t) =
  {
    comparer = to_tuple_comparer total_order_l total_order_r;
    properties = lemma_to_tuple_comparer total_order_l total_order_r;
  } 
  
