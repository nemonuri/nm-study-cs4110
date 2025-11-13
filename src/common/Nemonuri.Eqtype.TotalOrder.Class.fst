module Nemonuri.Eqtype.TotalOrder.Class

open FStar.Order
open FStar.Tactics.Typeclasses
open Nemonuri.Eqtype.TotalOrder

class tc (a_t:eqtype) = {
  comparer: comparer_t a_t;
  [@@@no_method]
  properties: squash (are_equality_and_identity_same comparer /\ is_total_order comparer);
}

let to_class #a_t (total_order:t a_t) : tc a_t =
{
  comparer = total_order.comparer;
  properties = total_order.properties;
}


