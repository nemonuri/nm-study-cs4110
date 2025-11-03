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

type execute_t = program_t -> int
val execute : execute_t
let execute (program:program_t) : int = evaluate program.expression











(* An *operational semantics* describes how a program executes on an abstract machine. *)
assume new 
type abstract_machine_t : eqtype

type operational_semantic_t = abstract_machine_t -> execute_t

(*
A *small-step* operational semantics describes how such an execution proceeds in terms of successive reductions
—here, of an expression—until we reach a value that represents the result of the computation. 
*)

