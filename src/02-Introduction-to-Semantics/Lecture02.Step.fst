module Lecture02.Step

type binrel_t (state_t:eqtype) = state_t -> state_t -> bool

type small_step_t #state_t (binrel:binrel_t state_t) : state_t -> state_t -> eqtype =
| SmallStep: from:state_t -> to:state_t{binrel from to} -> small_step_t binrel from to

type multi_step_t #state_t (binrel:binrel_t state_t) : state_t -> state_t -> eqtype =
| MultiStepRefl: (last:state_t) -> multi_step_t binrel last last
| MultiStepTrans: 
    #from:state_t -> #to:state_t -> #last:state_t ->
    (premise0: small_step_t binrel from to) ->
    (premise1: multi_step_t binrel to last) ->
    (*conclusion*) multi_step_t binrel from last
  
let is_model_of_multi_step 
  #state_t (binrel:binrel_t state_t) 
  (first:state_t) (last:state_t)
  : prop =
  squash (multi_step_t binrel first last)

let lemma_small_step 
  #state_t (binrel:binrel_t state_t) (from:state_t) (to:state_t)
  : Lemma (requires binrel from to)
          (ensures is_model_of_multi_step binrel from to)
  =
  let small_step : small_step_t binrel from to = SmallStep from to in
  let multi_step_refl = MultiStepRefl to in
  let proof = MultiStepTrans small_step multi_step_refl in
  FStar.Squash.return_squash proof

module Rtc = FStar.ReflexiveTransitiveClosure

type indexless_multi_step_t #state_t (binrel:binrel_t state_t) : eqtype =
{
  first: state_t;
  last: (x:state_t{is_model_of_multi_step binrel first x});
  source: multi_step_t binrel first last;
}

let hide_index 
  #state_t (#binrel:binrel_t state_t) (#first:state_t) (#last:state_t)
  (multi_step:multi_step_t binrel first last)
  : indexless_multi_step_t binrel =
  FStar.Squash.return_squash multi_step;
  assert (is_model_of_multi_step binrel first last);
  {first = first; last = last; source = multi_step}

let reveal_index
  #state_t (#binrel:binrel_t state_t)
  (indexless_multi_step:indexless_multi_step_t binrel)
  : multi_step_t binrel indexless_multi_step.first indexless_multi_step.last =
  indexless_multi_step.source

let lemma_hide_reveal 
  #state_t (#binrel:binrel_t state_t) (#first:state_t) (#last:state_t)
  (multi_step:multi_step_t binrel first last)
  : Lemma ((hide_index multi_step |> reveal_index) == multi_step) =
  ()

let lemma_reveal_hide
  #state_t (#binrel:binrel_t state_t)
  (indexless_multi_step:indexless_multi_step_t binrel)
  : Lemma ((reveal_index indexless_multi_step |> hide_index) == indexless_multi_step) =
  ()

let is_greater_or_equal 
  #state_t (binrel:binrel_t state_t)
  (left:indexless_multi_step_t binrel)
  (right:indexless_multi_step_t binrel)
  : prop =
  (left == right) \/ (* 이게 있어야 'equal' 이지;; *)
  ((reveal_index left) << (reveal_index right))

let lemma_is_greater_or_equal
  #state_t (binrel:binrel_t state_t)
  : Lemma (Rtc.preorder_rel (is_greater_or_equal binrel)) =
  ()

let to_closure #state_t (binrel:binrel_t state_t) =
  Rtc.closure (is_greater_or_equal binrel)


