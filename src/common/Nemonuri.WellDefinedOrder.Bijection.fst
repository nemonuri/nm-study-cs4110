module Nemonuri.WellDefinedOrder.Bijection

open FStar.Order
open Nemonuri.WellDefinedOrder
open Nemonuri.WellDefinedOrder.Lemmas
module Td = Nemonuri.Transitive.Decidable
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
  (wdo: t dom_t)
  : comparer_t codom_t =
  let compare' (x:codom_t) (y:codom_t) : order =
    let (inv_x, inv_y) = get_inverse_2 bijection x y in
    wdo.comparer inv_x inv_y
  in
  compare'

let from_bijection
  (#dom_t:eqtype)
  (#codom_t:eqtype)
  (bijection:B.bijection dom_t codom_t)
  (wdo: t dom_t)
  : t codom_t =
  let open FStar.Classical in
  let comparer = create_comparer_from_bijection bijection wdo in
  let is_equal = to_is_equal comparer in
  let is_less = to_is_less comparer in
  let get_inv = get_inverse bijection in

  let is_equal_transitive_at_intro
    : is_equal_transitive_at_intro_t comparer = fun x y z ->
    begin
      let (inv_x, int_y, inv_z) = (get_inv x, get_inv y, get_inv z) in
      assert (Td.is_transitive_at (to_is_equal wdo.comparer) inv_x int_y inv_z);
      assert (wdo.comparer inv_x inv_z = Eq)
    end
  in
  let is_equal_symmetric_at_intro
    : is_equal_symmetric_at_intro_t comparer = fun x y ->
    begin
      let (inv_x, int_y) = (get_inv x, get_inv y) in
      assert (Td.is_symmetric_at (to_is_equal wdo.comparer) inv_x int_y);
      assert (wdo.comparer int_y inv_x = Eq)
    end
  in
  let is_equal_reflexive_at_intro
    : is_equal_reflexive_at_intro_t comparer = fun _ -> ()
  in
  let is_less_transitive_at_intro
    : is_less_transitive_at_intro_t comparer = fun x y z ->
    begin
      let (inv_x, int_y, inv_z) = (get_inv x, get_inv y, get_inv z) in
      assert (Td.is_transitive_at (to_is_less wdo.comparer) inv_x int_y inv_z);
      assert (wdo.comparer inv_x inv_z = Lt)
    end
  in
  let is_less_irreflexive_at_intro
    : is_less_irreflexive_at_intro_t comparer = fun _ -> ()
  in
  let is_lt_incomparable_eq_right_intro
    : is_lt_incomparable_eq_right_intro_t comparer = fun x y ->
    begin
      let (inv_x, int_y) = (get_inv x, get_inv y) in
      assert (is_lt_incomparable_eq_at wdo.comparer inv_x int_y);
      assert (wdo.comparer inv_x int_y = Eq)
    end
  in
  let is_lt_incomparable_eq_left_intro
    : is_lt_incomparable_eq_left_intro_t comparer = fun x y ->
    begin
      let (inv_x, inv_y) = (get_inv x, get_inv y) in
      assert (wdo.comparer inv_x inv_y = Eq);
      assert (Td.is_symmetric_at (to_is_equal wdo.comparer) inv_x inv_y);
      assert (wdo.comparer inv_y inv_x = Eq)
    end
  in
  {
    comparer = comparer;
    lemma_well_defined = 
      is_comparer_well_defined_intro comparer
        is_equal_transitive_at_intro
        is_equal_symmetric_at_intro
        is_equal_reflexive_at_intro
        is_less_transitive_at_intro
        is_less_irreflexive_at_intro
        is_lt_incomparable_eq_right_intro
        is_lt_incomparable_eq_left_intro;
  }
