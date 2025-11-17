module Nemonuri.WellDefinedOrder.Either

open FStar.Order
open Nemonuri.WellDefinedOrder
module Td = Nemonuri.Transitive.Decidable
module Tud = Nemonuri.Transitive
module Swo = Nemonuri.WellDefined.StrictWeakOrder

let to_either_comparer
  (#lesser_t: eqtype)
  (#greater_t: eqtype{lesser_t =!= greater_t})
  (wdo_l: t lesser_t)
  (wdo_g: t greater_t)
  : comparer_t (either lesser_t greater_t) =
  let comparer' (x: either lesser_t greater_t) (y: either lesser_t greater_t) : order =
    match (x, y) with
    | (Inl _, Inr _) -> Lt
    | (Inr _, Inl _) -> Gt
    | (Inl xl, Inl yl) -> wdo_l.comparer xl yl
    | (Inr xg, Inr yg) -> wdo_g.comparer xg yg
  in
  comparer'

let lemma_to_either_comparer
  (#lesser_t: eqtype)
  (#greater_t: eqtype{lesser_t =!= greater_t})
  (wdo_l: t lesser_t)
  (wdo_g: t greater_t)
  : Lemma (is_comparer_well_defined (to_either_comparer wdo_l wdo_g)) =
  let open FStar.Classical in
  let comparer = (to_either_comparer wdo_l wdo_g) in
  let is_equal = to_binrel comparer Eq in
  let is_less = to_binrel comparer Lt in
  let p_goal1 = (Td.is_transitive is_equal) in
  let p_goal2 = (Td.is_symmetric is_equal) in
  let p_goal3 = (Td.is_reflexive is_equal) in
  let p_goal4 = (Td.is_transitive is_less) in
  let p_goal5 = (Td.is_irreflexive is_less) in
  let p_goal6 = (Td.is_transitive (Swo.to_incomparable is_less)) in

  let lemma_goal1 x y z
    : Lemma (requires (is_equal x y) /\ (is_equal y z)) (ensures (is_equal x z)) =
    match (x, y, z) with
    | (Inl xv, Inl yv, Inl zv) ->
    begin
      let ls_equal_ = to_binrel wdo_l.comparer Eq in
      assert (ls_equal_ xv yv /\ ls_equal_ yv zv);
      assert (Td.is_transitive_at ls_equal_ xv yv zv);
      assert (ls_equal_ xv zv)
    end
    | (Inr xv, Inr yv, Inr zv) ->
    begin
      let ls_equal_ = to_binrel wdo_g.comparer Eq in
      assert (ls_equal_ xv yv /\ ls_equal_ yv zv);
      assert (Td.is_transitive_at ls_equal_ xv yv zv);
      assert (ls_equal_ xv zv)
    end
  in
  lemma_goal1 |> move_requires_3 |> forall_intro_3;
  assert (p_goal1);

  let lemma_goal2 x y
    : Lemma (requires (is_equal x y)) (ensures (is_equal y x)) =
    match (x, y) with
    | (Inl xv, Inl yv) -> assert (Td.is_symmetric_at (to_binrel wdo_l.comparer Eq) xv yv)
    | (Inr xv, Inr yv) -> assert (Td.is_symmetric_at (to_binrel wdo_g.comparer Eq) xv yv)
  in
  lemma_goal2 |> move_requires_2 |> forall_intro_2;
  assert (p_goal2);

  assert (p_goal3);

  let lemma_goal4 x y z
    : Lemma (requires (is_less x y) /\ (is_less y z)) (ensures (is_less x z)) =
    match (x, y, z) with
    | (Inl xv, Inl yv, Inl zv) -> assert (Td.is_transitive_at (to_binrel wdo_l.comparer Lt) xv yv zv)
    | (Inr xv, Inr yv, Inr zv) -> assert (Td.is_transitive_at (to_binrel wdo_g.comparer Lt) xv yv zv)
    | (Inl _, _, Inr _) -> ()
  in
  assume (p_goal4);

  assert (p_goal5);

  assume (p_goal6)

let to_either
  (#lesser_t: eqtype)
  (#greater_t: eqtype{lesser_t =!= greater_t})
  (wdo_l: t lesser_t)
  (wdo_g: t greater_t)
  : t (either lesser_t greater_t) =
  {
    comparer = to_either_comparer wdo_l wdo_g;
    lemma_well_defined = lemma_to_either_comparer wdo_l wdo_g;
  }