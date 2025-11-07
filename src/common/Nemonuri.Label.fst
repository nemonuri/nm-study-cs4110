module Nemonuri.Label

type t (label_t: eqtype) = {
  label: label_t
}

noeq type indexless_t = {
  label_t: eqtype;
  label: label_t
}

let hide_index #label_t (label:t label_t)
  : Tot (x:indexless_t{x.label_t == label_t}) =
  {label_t=label_t; label=label.label}

let reveal_index (label:indexless_t)
  : Tot (t label.label_t) =
  {label=label.label}
