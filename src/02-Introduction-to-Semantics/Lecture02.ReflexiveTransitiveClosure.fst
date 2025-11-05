module Lecture02.ReflexiveTransitiveClosure

(*
module Br = Lecture02.BinaryRelation
module Rule = Lecture02.InferenceRule
module L = FStar.List.Tot

type label_t =
| Refl
| Trans

type small_step_predicate_t (state_t:eqtype) = Br.binary_predicate_t state_t state_t

let is_rule 
  (state_t:eqtype)
  (x:Rule.t)
  : prop =
  (Rule.__proj__Mkt__item__label_t x == label_t) /\
  (x.model_t == state_t)

type rule_t (state_t:eqtype) =
  x:Rule.t{is_rule state_t x}

let get_refl_rule (state_t:eqtype) : rule_t state_t = {
  label = Refl;
  model_t = state_t;
  premises = [];
  conclusion = fun s -> s = s
}

let get_trans_rule 
  (#state_t:eqtype)
  (small_step_predicate:small_step_predicate_t state_t)
  (pre_state:state_t)
  (rule:rule_t state_t)
  : (x:rule_t state_t{rule << x}) =
  let p1 = small_step_predicate pre_state in
  let next_premises = p1::rule.premises in
  {
    label = Trans;
    model_t = state_t;
    premises = next_premises;
    conclusion = fun s -> (p1 s) /\ (p2 s)
  }


let lemma_refl_rule (state_t:eqtype)
  : Lemma (Rule.is_valid (get_refl_rule state_t)) =
  ()
*)