module Lecture02.ReflexiveTransitiveClosure

open Lecture02.BinaryRelation { (∈) } 
module Br = Lecture02.BinaryRelation
module L = FStar.List.Tot

type step_t (state_t:eqtype) = (state_t & state_t)
type small_step_relation_t (state_t:eqtype) = (state_t & state_t) -> bool
//Br.binary_relation_t (Br.to_set state_t) (Br.to_set state_t)

(*
type expr_t #state_t (small_step_relation:small_step_relation_t state_t) =
| ExprRefl: 
    (conclusion:step_t state_t{(fst conclusion) = (snd conclusion)}) -> 
    expr_t small_step_relation
| ExprTrans: 
    (premise0:step_t state_t{premise0 ∈ small_step_relation}) ->
    (premise1:step_t state_t{(snd premise0) = (fst premise1)}) ->
    (conclusion:step_t state_t{(fst premise0) = (fst conclusion) && (snd premise1) = (snd conclusion)}) ->
    expr_t small_step_relation
*)

type expr_t (state_t:eqtype) =
| ConclusionOnly: (step_t state_t) -> expr_t state_t
| AddPremise: (step_t state_t) -> (expr_t state_t) -> expr_t state_t

let rec expr_count #state_t (expr:expr_t state_t)
  : Tot pos (decreases expr) =
  match expr with
  | ConclusionOnly _ -> 1
  | AddPremise _ pre_expr -> 1 + (expr_count pre_expr)

let get_first_step #state_t (expr:expr_t state_t)
  : Tot (step_t state_t) (decreases expr) =
  match expr with
  | ConclusionOnly _0 -> _0
  | AddPremise _0 _1 -> _0

let rec get_last_step #state_t (expr:expr_t state_t)
  : Tot (step_t state_t) (decreases expr) =
  match expr with
  | ConclusionOnly _0 -> _0
  | AddPremise _0 _1 -> get_last_step _1

private let rec is_valid_expr_core 
  #state_t (expr:expr_t state_t) 
  (small_step_relation:small_step_relation_t state_t)
  (lub_expr:expr_t state_t{expr = lub_expr \/ expr << lub_expr})
  : Tot bool (decreases expr) 
  =
  match expr with
  | ConclusionOnly _0 -> 
  begin
    match expr = lub_expr with 
    | true -> ((fst _0) = (snd _0))
    | false -> ((fst _0) = (get_first_step lub_expr |> fst)) && ((snd _0) = (get_last_step lub_expr |> snd))
  end
  | AddPremise _0 pre_expr -> 
    (_0 |> small_step_relation) && 
    (is_valid_expr_core pre_expr small_step_relation lub_expr)

let is_valid_expr #state_t (expr:expr_t state_t) (small_step_relation:small_step_relation_t state_t)
  : bool =
  is_valid_expr_core expr small_step_relation expr

type valid_expr_t #state_t (small_step_relation:small_step_relation_t state_t) = 
  x:expr_t state_t{is_valid_expr x small_step_relation}

private let rec add_step_core 
  #state_t (#small_step_relation:small_step_relation_t state_t)
  (step:step_t state_t{small_step_relation step})
  (expr:expr_t state_t)
  (lub_expr:valid_expr_t small_step_relation{(expr = lub_expr \/ expr << lub_expr) /\ (snd step) = (fst (get_first_step lub_expr))})
  (popped_steps:list (step_t state_t){small_step_relation step})
  : Tot (expr_t state_t) 
  (*
    (requires (L.length popped_steps) = ((expr_count lub_expr) - (expr_count expr)))
    (ensures fun r -> 
      let r2 = L.fold_right (fun s e -> AddPremise s e) popped_steps r in
      (is_valid_expr (AddPremise step r2) small_step_relation)
    )
  *)
    (decreases expr) 
  =
  match expr with
  | ConclusionOnly _0 -> 
  begin
    match expr = lub_expr with 
    | true -> ConclusionOnly step
    | false -> ConclusionOnly (step |> fst, get_last_step lub_expr |> snd)
  end
  | AddPremise _0 pre_expr -> AddPremise _0 (add_step_core step pre_expr lub_expr (_0::popped_steps))
    
let add_step 
  #state_t (#small_step_relation:small_step_relation_t state_t)
  (step:step_t state_t{small_step_relation step})
  (expr:valid_expr_t small_step_relation{(snd step) = (fst (get_first_step expr))})
  : Tot (valid_expr_t small_step_relation) =
  let r = AddPremise step (add_step_core step expr expr []) in
  assume (is_valid_expr r small_step_relation);
  r

type builder_t
  #state_t (small_step_relation:small_step_relation_t state_t) 
  : (expr:valid_expr_t small_step_relation) -> Type =
| BuildNil:
    (fix:state_t) ->
    builder_t small_step_relation (ConclusionOnly (fix, fix))
| BuildCons:
    (head:step_t state_t{small_step_relation head}) ->
    (#tail_expr:valid_expr_t small_step_relation{(snd head) = (fst (get_first_step tail_expr))}) ->
    (tail:builder_t small_step_relation tail_expr) ->
    builder_t small_step_relation (add_step head tail_expr)

(*
type builder_t 
  #state_t (small_step_relation:small_step_relation_t state_t) 
  : (expr_t small_step_relation) -> Type =
| BuildNil:
    (fix:state_t) ->
    builder_t small_step_relation (ExprRefl (fix, fix))
| BuildCons:
    (head)
    (_0:step_t state_t{_0 ∈ small_step_relation}) ->
    (_1:state_t) ->
    (_2:builder_t small_step_relation)
*)