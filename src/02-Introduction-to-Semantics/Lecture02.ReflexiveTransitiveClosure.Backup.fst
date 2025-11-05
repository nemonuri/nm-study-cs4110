module Lecture02.ReflexiveTransitiveClosure.Backup

open Lecture02.BinaryRelation { (∈) } 
module Br = Lecture02.BinaryRelation
module Rule = Lecture02.InferenceRule
module RuleBuilder = Lecture02.InferenceRule.Builder
module L = FStar.List.Tot


type step_t (state_t:eqtype) = (state_t & state_t)
type small_step_relation_t (state_t:eqtype) = Br.binary_relation_t (Br.to_set state_t) (Br.to_set state_t)

noeq
type raw_builder_t 
  #state_t (model_t:Type) (small_step_relation:small_step_relation_t state_t) =
| ConclusionOnly: 
    (to_conclusion:model_t -> (step_t state_t)) -> 
    (raw_builder_t model_t small_step_relation)
| AddPremise: 
    (to_premise:model_t -> (step_t state_t)) ->
    (raw_builder_t model_t small_step_relation) ->
    (raw_builder_t model_t small_step_relation)


let rec get_conclusion_from_raw
  #state_t (#model_t:Type) (#small_step_relation:small_step_relation_t state_t)
  (raw_builder:raw_builder_t model_t small_step_relation)
  (model:model_t)
  : Tot (step_t state_t) (decreases raw_builder) =
  match raw_builder with
  | ConclusionOnly tc -> tc model
  | AddPremise tp pre_raw_builder -> get_conclusion_from_raw pre_raw_builder model

let is_example
  #state_t (#model_t:Type) (#small_step_relation:small_step_relation_t state_t)
  (raw_builder:raw_builder_t model_t small_step_relation)
  (model:model_t)
  : prop =
  match raw_builder with
  | ConclusionOnly tc -> let s = tc model in (fst s) = (snd s)
  | AddPremise tp pre_raw_builder ->
  let s1 = tp model in
  let s2 = get_conclusion_from_raw pre_raw_builder model in
  let s3 = get_conclusion_from_raw raw_builder model in
  (s1 ∈ small_step_relation) /\
  ((fst s1) = (fst s3)) /\ ((snd s1) = (fst s2)) /\ ((snd s2) = (snd s3))

let is_valid
  #state_t (#model_t:Type) (#small_step_relation:small_step_relation_t state_t)
  (raw_builder:raw_builder_t model_t small_step_relation)
  : prop =
  forall (model:model_t). (is_example raw_builder model)

type builder_t 
  #state_t (model_t:Type) (small_step_relation:small_step_relation_t state_t) =
  x:(raw_builder_t model_t small_step_relation){is_valid x}

private let rec to_rule_builder_core
  #state_t (#model_t:Type) (#small_step_relation:small_step_relation_t state_t)
  (raw_builder:raw_builder_t model_t small_step_relation) (lub_builder:builder_t model_t small_step_relation)
  : Pure (RuleBuilder.t model_t) 
    (requires (raw_builder == lub_builder) \/ (raw_builder << lub_builder))
    (ensures fun r -> True)
    (decreases raw_builder) =
  match raw_builder with
  | ConclusionOnly to_conclusion -> RuleBuilder.ConclusionOnly {
      meta_proposition_t = step_t state_t;
      apply = to_conclusion;
      hold = fun x -> 
        forall (model:model_t). (get_conclusion_from_raw lub_builder model) = (to_conclusion model)
    }
  | AddPremise to_premise pre_raw_builder ->
    let new_premise : RuleBuilder.meta_proposition_schema_t model_t = {
      meta_proposition_t = step_t state_t;
      apply = to_premise;
      hold = fun x -> (x ∈ small_step_relation)
    } 
    in
    let pre_rule_builder = to_rule_builder_core pre_raw_builder lub_builder in
    RuleBuilder.AddPremise new_premise pre_rule_builder

let to_rule_builder
  #state_t (#model_t:Type) (#small_step_relation:small_step_relation_t state_t)
  (builder:builder_t model_t small_step_relation)
  : Tot (RuleBuilder.t model_t) =
  to_rule_builder_core builder builder

let build
  #state_t (#model_t:Type) (#small_step_relation:small_step_relation_t state_t)
  (builder:builder_t model_t small_step_relation)
  : Rule.t model_t =
  RuleBuilder.build (to_rule_builder builder)

open FStar.Tactics.V2
let lemma_build 
  #state_t (#model_t:Type) (#small_step_relation:small_step_relation_t state_t)
  (builder:builder_t model_t small_step_relation)
  : Lemma (Rule.is_valid (build builder)) =
  //assert (Rule.is_valid (build builder)) by (dump "")
  admit ()
  (* 역시, 이게 그냥은 증명이 안 되네... *)

type label_t =
| Refl
| Trans

let get_label 
  #state_t (#model_t:Type) (#small_step_relation:small_step_relation_t state_t)
  (builder:builder_t model_t small_step_relation)
  : label_t =
  match builder with
  | ConclusionOnly _ -> Refl
  | AddPremise _ _ -> Trans


(* goal: is_multi_step *)




(*
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