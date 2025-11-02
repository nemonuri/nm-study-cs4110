module Lecture02

(*
1 Arithmetic Expressions

A program in this language is an expression;
**executing a program** means **evaluating the expression to an integer**. 
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

type exp =
  | Var of string
  | Int of int
  | Add of exp * exp
  | Mul of exp * exp
  | Assgn of string * exp * exp

(*

This closely matches the BNF grammar above. 
The abstract syntax tree (AST) of an expression can be obtained by applying the datatype constructors in each case. 
For instance, the AST of expression 2 * (foo + 1) is:

*)

let example_expression1 = Mul (Int 2, Add (Var "foo", Int 1))