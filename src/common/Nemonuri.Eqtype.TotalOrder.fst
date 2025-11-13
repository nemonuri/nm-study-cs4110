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

let is_total_order #a_t (comparer:comparer_t a_t) : prop =
  let is_le = is_less_or_equal comparer in
  let is_eq = is_equal comparer in
   (forall a1 a2. (is_le a1 a2 /\ is_le a2 a1)  ==> is_eq a1 a2)  (* anti-symmetry *)
 /\ (forall a1 a2 a3. is_le a1 a2 /\ is_le a2 a3 ==> is_le a1 a3)   (* transitivity  *)
 /\ (forall a1 a2. is_le a1 a2 \/ is_le a2 a1)                 (* totality      *)

let is_comparer_total_order #a_t (comparer:comparer_t a_t) : prop =
  (are_equality_and_identity_same comparer) /\ (is_total_order comparer)

let lemma_is_comparer_total_order #a_t (comparer:comparer_t a_t)
  : Lemma (requires is_comparer_total_order comparer)
          (ensures FStar.OrdSet.total_order a_t (is_less_or_equal comparer))
  =
  let open FStar.Classical in
  let is_eq = is_equal comparer in
  (lemma_are_equality_and_identity_same_at #a_t comparer) |> move_requires_2 |> forall_intro_2;
  assert (forall (a1 a2 :a_t). are_equality_and_identity_same_at comparer a1 a2);
  assert (forall (a1 a2 :a_t). (is_eq a1 a2) <==> (a1 = a2))

noeq type t (a_t:eqtype) = {
  comparer: comparer_t a_t;
  properties: squash (is_comparer_total_order comparer);
}

let to_cmp #a_t (total_order:t a_t) : FStar.OrdSet.cmp a_t = 
  FStar.Classical.move_requires lemma_is_comparer_total_order total_order.comparer;
  is_less_or_equal total_order.comparer


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


let lemma_to_either_comparer
  (#lesser_t: eqtype)
  (#greater_t: eqtype{lesser_t =!= greater_t})
  (total_order_l: t lesser_t)
  (total_order_g: t greater_t)
  : Lemma (is_comparer_total_order (to_either_comparer total_order_l total_order_g)) =
  let open FStar.Classical in
  let comparer = to_either_comparer total_order_l total_order_g in
  let p_goal1: prop = (forall x y. are_equality_and_identity_same_at comparer x y) in
  forall_intro_2 (lemma_to_either_comparer_equality total_order_l total_order_g);
  assert (p_goal1);
  let p_goal2: prop = (is_total_order comparer) in
  assume (p_goal2)


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