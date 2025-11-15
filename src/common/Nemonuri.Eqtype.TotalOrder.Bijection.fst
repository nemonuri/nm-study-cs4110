module Nemonuri.Eqtype.TotalOrder.Bijection

open FStar.Order
open Nemonuri.Eqtype.TotalOrder
module B = FStar.Bijection

let is_bijective_at
  (#dom_t:eqtype)
  (#codom_t:eqtype)
  (bijection:B.bijection dom_t codom_t)
  (x:dom_t) (y:codom_t)
  : bool =
  ((bijection.right x) = y) = (x = (bijection.left y))

let lemma_is_bijective_at
  (#dom_t:eqtype)
  (#codom_t:eqtype)
  (bijection:B.bijection dom_t codom_t)
  (x:dom_t) (y:codom_t)
  : Lemma (requires is_bijective_at bijection x y)
          (ensures ((bijection.right x) == y) <==> (x == (bijection.left y))) 
          [SMTPat (bijection.right x); SMTPat (bijection.left y)]
  =
  ()

let get_inverse
  (#dom_t:eqtype)
  (#codom_t:eqtype)
  (bijection:B.bijection dom_t codom_t)
  (codom: codom_t)
  : Tot (dom:dom_t{is_bijective_at bijection dom codom}) =
  bijection.left codom

let get_inverse_2
  (#dom_t:eqtype)
  (#codom_t:eqtype)
  (bijection:B.bijection dom_t codom_t)
  (codom1: codom_t) (codom2: codom_t)
  : Tot (dom_pair:(dom_t & dom_t){
      (is_bijective_at bijection dom_pair._1 codom1) /\
      (is_bijective_at bijection dom_pair._2 codom2)
    }) =
  (get_inverse bijection codom1, get_inverse bijection codom2)


let create_comparer_from_bijection
  (#dom_t:eqtype)
  (#codom_t:eqtype)
  (bijection:B.bijection dom_t codom_t)
  (total_order_dom: t dom_t)
  : comparer_t codom_t =
  let compare' (x:codom_t) (y:codom_t) : order =
    let (inv_x, inv_y) = get_inverse_2 bijection x y in
    total_order_dom.comparer inv_x inv_y
  in
  compare'

let lemma_create_comparer_from_bijection_equality
  (#dom_t:eqtype)
  (#codom_t:eqtype)
  (bijection:B.bijection dom_t codom_t)
  (total_order_dom: t dom_t)
  (x: codom_t) (y: codom_t)
  : Lemma (are_equality_and_identity_same_at (create_comparer_from_bijection bijection total_order_dom) x y) =
  let open FStar.Classical in
  let comparer = create_comparer_from_bijection bijection total_order_dom in
  let (inv_x, inv_y) = get_inverse_2 bijection x y in
  let p_goal: prop = ((is_equal comparer x y) <==> (x = y)) in
  let p1: prop = (is_equal comparer x y) in
  let p2: prop = (x = y) in
  let lemma_1_to_2' () : Lemma (requires p1) (ensures p2) = 
    assert (are_equality_and_identity_same_at total_order_dom.comparer inv_x inv_y);
    assert (inv_x = inv_y);
    assert (x = y)
  in
  let lemma_2_to_1' () : Lemma (requires p2) (ensures p1) =
    () (* Note: 이게 그냥 생략이 되네...? *)
  in
  move_requires lemma_1_to_2' (); 
  move_requires lemma_2_to_1' ();
  assert (p_goal)

let lemma_create_comparer_from_bijection_anti_symmetry
  (#dom_t:eqtype)
  (#codom_t:eqtype)
  (bijection:B.bijection dom_t codom_t)
  (total_order_dom: t dom_t)
  (x: codom_t) (y: codom_t)
  : Lemma (is_anti_symmetry_at (create_comparer_from_bijection bijection total_order_dom) x y) =
  let (inv_x, inv_y) = get_inverse_2 bijection x y in
  assert (is_anti_symmetry_at total_order_dom.comparer inv_x inv_y)


let lemma_create_comparer_from_bijection_transivity
  (#dom_t:eqtype)
  (#codom_t:eqtype)
  (bijection:B.bijection dom_t codom_t)
  (total_order_dom: t dom_t)
  (x: codom_t) (y: codom_t) (z: codom_t)
  : Lemma (is_transive_at (create_comparer_from_bijection bijection total_order_dom) x y z) =
  let open FStar.Classical in
  let comparer = create_comparer_from_bijection bijection total_order_dom in
  let is_le = is_less_or_equal comparer in
  let (inv_x, inv_y) = get_inverse_2 bijection x y in
  let inv_z = get_inverse bijection z in
  assert (is_transive_at total_order_dom.comparer inv_x inv_y inv_z)


let lemma_create_comparer_from_bijection_total
  (#dom_t:eqtype)
  (#codom_t:eqtype)
  (bijection:B.bijection dom_t codom_t)
  (total_order_dom: t dom_t)
  (x: codom_t) (y: codom_t)
  : Lemma (is_total_at (create_comparer_from_bijection bijection total_order_dom) x y) =
  let open FStar.Classical in
  let comparer = create_comparer_from_bijection bijection total_order_dom in
  let is_le = is_less_or_equal comparer in
  let (inv_x, inv_y) = get_inverse_2 bijection x y in
  assert (is_total_at total_order_dom.comparer inv_x inv_y)


let lemma_create_comparer_from_bijection
  (#dom_t:eqtype)
  (#codom_t:eqtype)
  (bijection:B.bijection dom_t codom_t)
  (total_order_dom: t dom_t)
  : Lemma (is_eqtype_total_order (create_comparer_from_bijection bijection total_order_dom)) =
  let open FStar.Classical in
  let comparer = create_comparer_from_bijection bijection total_order_dom in
  let p_goal1: prop = (are_equality_and_identity_same comparer) in
  forall_intro_2 (lemma_create_comparer_from_bijection_equality bijection total_order_dom);
  assert (p_goal1);

  let p_goal2: prop = (is_anti_symmetry comparer) in
  forall_intro_2 (lemma_create_comparer_from_bijection_anti_symmetry bijection total_order_dom);
  assert (p_goal2);

  let p_goal3: prop = (is_transive comparer) in
  forall_intro_3 (lemma_create_comparer_from_bijection_transivity bijection total_order_dom);
  assert (p_goal3);

  let p_goal4: prop = (is_total comparer) in
  forall_intro_2 (lemma_create_comparer_from_bijection_total bijection total_order_dom);
  assert (p_goal4)

let from_bijection
  (#dom_t:eqtype)
  (#codom_t:eqtype)
  (bijection:B.bijection dom_t codom_t)
  (total_order_dom: t dom_t)
  : t codom_t =
  {
    comparer = create_comparer_from_bijection bijection total_order_dom;
    properties = lemma_create_comparer_from_bijection bijection total_order_dom;
  }


