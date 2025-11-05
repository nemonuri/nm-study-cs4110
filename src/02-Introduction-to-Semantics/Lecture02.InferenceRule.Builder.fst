module Lecture02.InferenceRule.Builder
module Ir = Lecture02.InferenceRule

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


let rec build #model_t (builder:t model_t)
  : Tot (Ir.t model_t) (decreases builder) =
  match builder with
  | ConclusionOnly c -> {premises = []; conclusion = (to_prop c)}
  | AddPremise p pre_builder -> 
  let pre_class = build pre_builder in
  {
    premises = (to_prop p)::(pre_class.premises);
    conclusion = pre_class.conclusion
  }
