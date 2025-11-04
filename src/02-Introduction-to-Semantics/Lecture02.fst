module Lecture02

(*
1 Arithmetic Expressions

A program in this language is an expression;
executing a program means evaluating the expression to an integer. 
To describe the syntactic structure of this language we will use variables that range over the following domains:

𝑥, 𝑦, 𝑧 ∈ Var
𝑛, 𝑚 ∈ Int
𝑒 ∈ Exp

Var is the set of program variables (e.g., foo, bar, baz, i, etc.). 
Int is the set of constant integers (e.g.,42, 40, 7). 
Exp is the domain of expressions, which we specify using a BNF (Backus–Naur Form) grammar:

𝑒 ::= x
| 𝑛
| 𝑒1 + 𝑒2
| 𝑒1 * 𝑒2
| 𝑥 := 𝑒1 ; 𝑒2


1.1 Representing Expressions

The syntactic structure of expressions in this language can be compactly expressed in OCaml using datatypes:
*)

type exp_t =
  | Var of string
  | Int of int
  | Add of exp_t * exp_t
  | Mul of exp_t * exp_t
  | Assgn of string * exp_t * exp_t

(*

This closely matches the BNF grammar above. 
The abstract syntax tree (AST) of an expression can be obtained by applying the datatype constructors in each case. 
For instance, the AST of expression 2 * (foo + 1) is:

*)

let example_expression1 = Mul (Int 2, Add (Var "foo", Int 1))

(* The state of the abstract machine is often referred to as a *configuration*.

   For our language a configuration must include two pieces of information:

   - a *store* (also known as environment or state), which maps variables to integer values. 
     During program execution, we will refer to the store to determine the values associated with variables, 
     and also update the store to reflect assignment of new values to variables,
   - the *expression* to evaluate. 
*)

type store_t = (exp_var:exp_t{Var? exp_var}) -> option (exp_int:exp_t{Int? exp_int})
type config_t = (store_t & exp_t)

(* The small‑step operational semantics itself is a relation on configurations—i.e., a subset of Config × Config *)
type small_step_t = config_t -> config_t -> bool

open FStar.Tactics.Typeclasses

class config_premise = {
  small_step: small_step_t
}

let ( !> ) {| premise: config_premise |} (pre:config_t) (post:config_t) = premise.small_step pre post

