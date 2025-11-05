module Lecture02.InferenceRule.Constructor
module C = Lecture02.InferenceRule.Class
module Label = Nemonuri.Label

noeq
type meta_proposition_schema_t (model_t:Type) = {
  meta_proposition_t: Type;
  apply: model_t -> meta_proposition_t;
  hold: meta_proposition_t -> prop
}

let to_prop 
  #model_t (schema:meta_proposition_schema_t model_t)
  : model_t -> prop =
  fun model -> schema.hold (schema.apply model)

noeq
type t (model_t:Type) =
| ConclusionOnly: (conclusion:meta_proposition_schema_t model_t) -> t model_t
| AddPremise: (premise:meta_proposition_schema_t model_t) -> (t model_t) -> t model_t


let rec to_class #model_t (raw:t model_t) (label:Label.t)
  : Tot (C.t model_t label) (decreases raw) =
  match raw with
  | ConclusionOnly c -> {premises = []; conclusion = (to_prop c)}
  | AddPremise p pre_raw -> 
  let pre_class = to_class pre_raw label in
  {
    premises = (to_prop p)::(pre_class.premises);
    conclusion = pre_class.conclusion
  }
