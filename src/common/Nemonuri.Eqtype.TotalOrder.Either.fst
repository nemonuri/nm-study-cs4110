module Nemonuri.Eqtype.TotalOrder.Either

open FStar.Order
open Nemonuri.Eqtype.TotalOrder

//---- either ----

private let to_either_comparer_compare'
  (#lesser_t: eqtype)
  (#greater_t: eqtype{lesser_t =!= greater_t})
  (total_order_l: t lesser_t)
  (total_order_g: t greater_t)
  (x: either lesser_t greater_t) (y: either lesser_t greater_t) : order =
  match (x, y) with
  | (Inl _, Inr _) -> Lt
  | (Inr _, Inl _) -> Gt
  | (Inl xl, Inl yl) -> total_order_l.comparer xl yl
  | (Inr xg, Inr yg) -> total_order_g.comparer xg yg

let to_either_comparer 
  (#lesser_t: eqtype)
  (#greater_t: eqtype{lesser_t =!= greater_t})
  (total_order_l: t lesser_t)
  (total_order_g: t greater_t)
  : comparer_t (either lesser_t greater_t) =
  to_either_comparer_compare' total_order_l total_order_g


let lemma_to_either_comparer_equality
  (#lesser_t: eqtype)
  (#greater_t: eqtype{lesser_t =!= greater_t})
  (total_order_l: t lesser_t)
  (total_order_g: t greater_t)
  (x: either lesser_t greater_t) (y: either lesser_t greater_t)
  : Lemma (are_equality_and_identity_same_at (to_either_comparer total_order_l total_order_g) x y) =
  let open FStar.Classical in
  let comparer = to_either_comparer total_order_l total_order_g in
  let p_goal: prop = ((is_equal comparer x y) <==> (x = y)) in
  let p1: prop = (is_equal comparer x y) in
  let p2: prop = (x = y) in
  let lemma_1_to_2' () : Lemma (requires p1) (ensures p2) =
    let lemma_1_to_2_aux' #a_t (total_order: t a_t) (x:a_t) (y:a_t)
      : Lemma (requires total_order.comparer x y = Eq) (ensures x = y) =
      assert (total_order.comparer x y = Eq);
      assert (are_equality_and_identity_same total_order.comparer);
      lemma_are_equality_and_identity_same_at total_order.comparer x y
    in
    assert (comparer x y = Eq);
    match (x, y) with
    | (Inl xl, Inl yl) -> lemma_1_to_2_aux' total_order_l xl yl
    | (Inr xg, Inr yg) -> lemma_1_to_2_aux' total_order_g xg yg
  in
  let lemma_2_to_1' () : Lemma (requires p2) (ensures p1) =
    let lemma_2_to_1_aux' #a_t (total_order: t a_t) (x:a_t) (y:a_t)
      : Lemma (requires x = y) (ensures total_order.comparer x y = Eq) =
      assert (are_equality_and_identity_same total_order.comparer);
      lemma_are_equality_and_identity_same_at total_order.comparer x y
    in
    match (x, y) with
    | (Inl xl, Inl yl) -> lemma_2_to_1_aux' total_order_l xl yl
    | (Inr xg, Inr yg) -> lemma_2_to_1_aux' total_order_g xg yg
  in
  move_requires lemma_1_to_2' (); 
  move_requires lemma_2_to_1' ();
  assert (p_goal)


let lemma_to_either_comparer_anti_symmetry
  (#lesser_t: eqtype)
  (#greater_t: eqtype{lesser_t =!= greater_t})
  (total_order_l: t lesser_t)
  (total_order_g: t greater_t)
  (x: either lesser_t greater_t) (y: either lesser_t greater_t)
  : Lemma (is_anti_symmetry_at (to_either_comparer total_order_l total_order_g) x y) =
  let comparer = to_either_comparer total_order_l total_order_g in
  let is_le = is_less_or_equal comparer in
  match (is_le x y, is_le y x) with
  | (true, true) -> 
  begin
    assert (~((Inl? x /\ Inr? y) \/ (Inr? x /\ Inl? y)));
    match (x, y) with
    | (Inl xl, Inl yl) -> lemma_anti_symmetry_less_or_equal total_order_l.comparer xl yl
    | (Inr xg, Inr yg) -> lemma_anti_symmetry_less_or_equal total_order_g.comparer xg yg
  end
  | _ -> ()

let lemma_to_either_comparer_transivity
  (#lesser_t: eqtype)
  (#greater_t: eqtype{lesser_t =!= greater_t})
  (total_order_l: t lesser_t)
  (total_order_g: t greater_t)
  (x: either lesser_t greater_t) (y: either lesser_t greater_t) (z: either lesser_t greater_t)
  : Lemma (is_transive_at (to_either_comparer total_order_l total_order_g) x y z) =
  let comparer = to_either_comparer total_order_l total_order_g in
  let is_le = is_less_or_equal comparer in
  match (is_le x y, is_le y z) with
  | (true, true) ->
  begin
    let p_goal: prop = (is_le x z) in
    assert (~(Inr? x /\ Inl? z));
    match (x, z) with
    | (Inl xl, Inr zg) -> assert (p_goal)
    | (Inl xl, Inl zl) -> 
    let open FStar.Tactics.V2 in
    begin
      assert (Inl? y);
      assert (is_less_or_equal total_order_l.comparer (Inl?.v y) zl);
      assert (is_less_or_equal total_order_l.comparer xl (Inl?.v y));
      assert (is_transive_at total_order_l.comparer xl (Inl?.v y) zl);
      assert (is_less_or_equal total_order_l.comparer xl zl);
      assert (p_goal)
    end
    | (Inr xg, Inr zg) -> 
    begin
      assert (Inr? y);
      assert (is_less_or_equal total_order_g.comparer (Inr?.v y) zg);
      assert (is_less_or_equal total_order_g.comparer xg (Inr?.v y));
      assert (is_transive_at total_order_g.comparer xg (Inr?.v y) zg);
      assert (is_less_or_equal total_order_g.comparer xg zg);
      assert (p_goal)
    end
  end
  | _ -> ()

let lemma_to_either_comparer_total
  (#lesser_t: eqtype)
  (#greater_t: eqtype{lesser_t =!= greater_t})
  (total_order_l: t lesser_t)
  (total_order_g: t greater_t)
  (x: either lesser_t greater_t) (y: either lesser_t greater_t)
  : Lemma (is_total_at (to_either_comparer total_order_l total_order_g) x y) =
  let comparer = to_either_comparer total_order_l total_order_g in
  let is_le = is_less_or_equal comparer in
  match (x, y) with
  | (Inl xl, Inr yg) -> assert (is_le x y)
  | (Inr xg, Inl yl) -> assert (is_le y x)
  | (Inl xl, Inl yl) ->
  begin
    let is_le_l = is_less_or_equal total_order_l.comparer in
    assert (is_total_at total_order_l.comparer xl yl);
    assert (is_le_l xl yl \/ is_le_l yl xl)
  end
  | (Inr xg, Inr yg) -> 
  begin
    let is_le_g = is_less_or_equal total_order_g.comparer in
    assert (is_total_at total_order_g.comparer xg yg);
    assert (is_le_g xg yg \/ is_le_g yg xg)
  end


let lemma_to_either_comparer
  (#lesser_t: eqtype)
  (#greater_t: eqtype{lesser_t =!= greater_t})
  (total_order_l: t lesser_t)
  (total_order_g: t greater_t)
  : Lemma (is_eqtype_total_order (to_either_comparer total_order_l total_order_g)) =
  let open FStar.Classical in
  let comparer = to_either_comparer total_order_l total_order_g in
  let p_goal1: prop = (forall x y. are_equality_and_identity_same_at comparer x y) in
  forall_intro_2 (lemma_to_either_comparer_equality total_order_l total_order_g);
  assert (p_goal1);

  let p_goal2: prop = (is_anti_symmetry comparer) in
  forall_intro_2 (lemma_to_either_comparer_anti_symmetry total_order_l total_order_g);
  assert (p_goal2);

  let p_goal3: prop = (is_transive comparer) in
  forall_intro_3 (lemma_to_either_comparer_transivity total_order_l total_order_g);
  assert (p_goal3);

  let p_goal4: prop = (is_total comparer) in
  forall_intro_2 (lemma_to_either_comparer_total total_order_l total_order_g);
  assert (p_goal4)


let to_either
  (#lesser_t: eqtype)
  (#greater_t: eqtype{lesser_t =!= greater_t})
  (total_order_l: t lesser_t)
  (total_order_g: t greater_t)
  : t (either lesser_t greater_t) =
  {
    comparer = to_either_comparer total_order_l total_order_g;
    properties = lemma_to_either_comparer total_order_l total_order_g;
  } 

//---|
