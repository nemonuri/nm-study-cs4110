module Lecture02.InferenceRule
module L = FStar.List.Tot

(* The small‑step operational semantics itself is a relation on configurations—i.e., a subset of Config × Config
   Question: How should we define this relation? Remember that there are an infinite number of configurations and possible steps!
   Answer: Define it inductively, using inference rules:

   An inference rule defines an implication: if all the premises hold, then the conclusion also holds.
*)

noeq
type t = {
  #label_t: eqtype;
  label: label_t;
  model_t: Type;
  premises: list (model_t -> prop);
  conclusion: (model_t -> prop);
}

let is_example (rule:t) (model:rule.model_t) : prop =
  (L.for_allP (fun premise -> premise model) rule.premises) ==> (rule.conclusion model)

let is_valid (rule:t) : prop = forall (model:rule.model_t). (is_example rule model)
