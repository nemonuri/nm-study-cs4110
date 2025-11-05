module Lecture02.InferenceRule.Class
module L = FStar.List.Tot
module Label = Nemonuri.Label

(* The small‑step operational semantics itself is a relation on configurations—i.e., a subset of Config × Config
   Question: How should we define this relation? Remember that there are an infinite number of configurations and possible steps!
   Answer: Define it inductively, using inference rules:

   An inference rule defines an implication: if all the premises hold, then the conclusion also holds.
*)

open FStar.Tactics.Typeclasses


class t (model_t:Type) (label:Label.t) = {
  premises: list (model_t -> prop);
  conclusion: (model_t -> prop);
}

let all_premises_hold #model_t (model:model_t) (label:Label.t) {|rule:t model_t label|}  : prop =
  (L.for_allP (fun premise -> premise model) rule.premises)

let is_example #model_t (model:model_t) (label:Label.t) {|rule:t model_t label|} : prop =
  (all_premises_hold model label) ==> (rule.conclusion model)

let is_model #model_t (model:model_t) (label:Label.t) {|rule:t model_t label|} : prop =
  (all_premises_hold model label) /\ (rule.conclusion model)

let is_valid (model_t:Type) (label:Label.t) {|rule:t model_t label|} : prop = forall (model:model_t). (is_example model label)
