module Lecture02.Meta.InferenceRule
module L = FStar.List.Tot


noeq type config_t = {
  expression_t: eqtype;
  is_predicate: expression_t -> bool;
  model_t: eqtype;
  is_model_of: (model:model_t) -> (x:expression_t{is_predicate x}) -> bool;
//  instance_t: eqtype;
//  instantiate: (predicate:expression_t{is_predicate predicate}) -> (model:model_t{is_model_of model predicate}) -> instance_t;
//  lift: instance_t -> model_t;
  label_t: eqtype;
}

type predicate_t (config:config_t) = x:config.expression_t{config.is_predicate x}

let is_model_of_all 
  (config: config_t) 
  (model: config.model_t)
  (predicates: list (predicate_t config))
  : bool =
  L.for_all (fun p -> config.is_model_of model p) predicates

let is_model_of_implication
  (config: config_t) 
  (model: config.model_t)
  (premises: list (predicate_t config))
  (conclusion: predicate_t config)
  : bool =
  match (is_model_of_all config model premises) with
  | false -> true
  | true -> config.is_model_of model conclusion

let is_valid_implication
  (config: config_t) 
  (premises: list (predicate_t config))
  (conclusion: predicate_t config)
  : prop =
  forall (model:config.model_t). 
    (is_model_of_implication config model premises conclusion)

type t (config: config_t) : eqtype = {
  premises: list (predicate_t config);
  conclusion: predicate_t config;
  proof: squash (is_valid_implication config premises conclusion);
  label: config.label_t;
}



