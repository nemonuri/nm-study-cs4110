module Nemonuri.Eqtype.FiniteSet

module O = FStar.OrdSet
module TOrd = Nemonuri.Eqtype.TotalOrder

type t (universe_t: eqtype) (total_order:TOrd.t universe_t) : Type0 = O.ordset universe_t (TOrd.to_cmp total_order)

noeq type pack_t = {
  universe_t: eqtype;
  total_order: TOrd.t universe_t;
  finite_set: t universe_t total_order;
}

let are_universe_equal (pack1:pack_t) (pack2:pack_t) : prop =
  pack1.universe_t == pack2.universe_t

let are_distinct_pack (pack1:pack_t) (pack2:pack_t) : prop =
  ~(are_universe_equal pack1 pack2)

type distinct_pack_t (other_pack:pack_t) = (x:pack_t{are_distinct_pack other_pack x})


let is_element (#universe_t:eqtype) #total_order (element:universe_t) (finite_set:t universe_t total_order) : bool = 
  O.mem element finite_set

type element_t (#universe_t:eqtype) #total_order (finite_set:t universe_t total_order) : eqtype = 
  (x:universe_t{is_element x finite_set})

