module Nemonuri.Eqtype.TotalOrder.Tuple

open FStar.Order
open Nemonuri.Eqtype.TotalOrder


let to_tuple_comparer 
  (#left_t: eqtype)
  (#right_t: eqtype)
  (total_order_l: t left_t)
  (total_order_r: t right_t)
  : comparer_t (left_t & right_t) =
  let compare' (x: (left_t & right_t)) (y: (left_t & right_t)) : order =
    (* lex order *)
    match total_order_l.comparer x._1 y._1 with
    | Gt -> Gt
    | Lt -> Lt
    | Eq -> total_order_r.comparer x._2 y._2
  in
  compare'

let lemma_to_tuple_comparer
  (#left_t: eqtype)
  (#right_t: eqtype)
  (total_order_l: t left_t)
  (total_order_r: t right_t)
  : Lemma (is_eqtype_total_order (to_tuple_comparer total_order_l total_order_r)) =
  let open FStar.Classical in
  let open FStar.Calc in
  let open FStar.Squash in
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
    let lemma_aux () : Lemma (requires (is_le x y /\ is_le y x)) (ensures is_eq x y) = 
      let lemma_contradict () : Lemma (requires ~(is_eq x y)) (ensures False) =
        let lemma_total_order () 
          : Lemma ((is_anti_symmetry_at total_order_l.comparer x._1 y._1) /\ (is_anti_symmetry_at total_order_r.comparer x._2 y._2)) = ()
        in
        let lemma_contradict2 () 
          : Lemma (ensures ((is_le_l x._1 y._1) \/ (is_le_r x._2 y._2)) /\ ((is_le_l y._1 x._1) \/ (is_le_r y._2 x._2)))
          = 
          let lemma_aux (x': (left_t & right_t)) (y': (left_t & right_t)) 
            : Lemma (requires is_le x' y') (ensures (is_le_l x'._1 y'._1) \/ (is_le_r x'._2 y'._2)) = ()
          in
          move_requires_2 lemma_aux x y;
          move_requires_2 lemma_aux y x
        in
        let pl_xy = (is_le_l x._1 y._1) in
        let pr_xy = (is_le_r x._2 y._2) in
        let pl_yx = (is_le_l y._1 x._1) in
        let pr_yx = (is_le_r y._2 x._2) in
        let p1 = ~pl_xy \/ ~pr_xy \/ ~pl_yx \/ ~pr_yx in
        let p2 = (pl_xy \/ pr_xy) /\ (pl_yx \/ pr_yx) in
        let (==>>) = (==>) in
        calc (==>>) {
          ~(is_eq x y);
          ==> {}
          ~(is_eq_l x._1 y._1) \/ ~(is_eq_r x._2 y._2);
          ==> { lemma_total_order () }
          p1;
          ==> { lemma_contradict2 () }
          p1 /\ p2;
        };
        assert (~(is_eq x y) ==>> (p1 /\ p2))
        //assert ((comparer x y = Lt) ==> (comparer y x = Gt));
        //assert (~(comparer x y = Lt) ==> (comparer x y = Gt))
      in
      move_requires lemma_contradict ()
    in
    move_requires lemma_aux ()
  in
  forall_intro_2 lemma_anti_symmetry';
  assert (p_goal2);

  let p_goal3: prop = (is_transive comparer) in
  //forall_intro_3 (lemma_to_either_comparer_transivity total_order_l total_order_g);
  assert (p_goal3);

  let p_goal4: prop = (is_total comparer) in
  //forall_intro_2 (lemma_to_either_comparer_total total_order_l total_order_g);
  assert (p_goal4)


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
  
