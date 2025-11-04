module Lecture02.Meta

(* A program in this language is an expression *)

(* Note: 
   이 셋의 차이가 무엇인지?
   1. assume val
   2. assume type
   3. assume new type
*)
assume new
type expression_t : eqtype

type program_t = | Mkprogram: expression:expression_t -> program_t


(* executing a program means evaluating the expression to an integer. *)
assume val evaluate : expression_t -> int

let execute (program:program_t) : int = evaluate program.expression


(* An *operational semantics* describes how a program executes on an abstract machine. *)
assume new 
type abstract_machine_t : eqtype

type singleton_t (#dom_t:Type) (unique_element:dom_t) = x:dom_t{x == unique_element}
type operational_semantic_t = abstract_machine_t -> (singleton_t execute)

(* A *small-step* operational semantics describes 
   how such an execution proceeds in terms of successive reductions—here, of an expression—
   until we reach a value that represents the result of the computation. 
*)
assume val reduced : expression_t -> expression_t -> prop

let is_full_reduced (expression:expression_t) : prop = 
   forall (x:expression_t). ~(expression `reduced` x)

assume val cast_to_int : (expression:expression_t{is_full_reduced expression}) -> int

type small_step_operational_semantic_t = (l:expression_t) -> (r:expression_t{l `reduced` r})

assume val describe : 
   (operational_semantic:operational_semantic_t) ->
   (abstract_machine:abstract_machine_t) ->
   (program:program_t) -> 
   (x:list small_step_operational_semantic_t{
      let result_value = operational_semantic abstract_machine program in
      let result_expr = FStar.List.Tot.fold_left (fun e (s:small_step_operational_semantic_t) -> s e) program.expression x in
      (is_full_reduced result_expr) /\ (cast_to_int result_expr = result_value)
   })

