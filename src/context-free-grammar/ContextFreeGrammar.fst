(* Reference: https://en.wikipedia.org/wiki/Context-free_grammar#Formal_definitions *)

module ContextFreeGrammar

module Fs = Nemonuri.Eqtype.FiniteSet
module O = FStar.Order

type symbol_union_t
  (nonterminal_pack: Fs.pack_t)
  (terminal_pack: Fs.distinct_pack_t nonterminal_pack) 
  : eqtype =
| TerminalSymbol: (Fs.element_t nonterminal_pack.finite_set) -> symbol_union_t nonterminal_pack terminal_pack
| NonterminalSymbol: (Fs.element_t terminal_pack.finite_set) -> symbol_union_t nonterminal_pack terminal_pack

type rule_t 
  (nonterminal_pack: Fs.pack_t)
  (terminal_pack: Fs.distinct_pack_t nonterminal_pack) 
  : eqtype =
{
  lhs: Fs.element_t nonterminal_pack.finite_set;
  rhs: list (symbol_union_t nonterminal_pack terminal_pack);
}

(* Reference: https://github.com/FStarLang/FStar/blob/8394ee383d05eabe9adaf2bbf68d403308150b3b/ulib/FStar.Class.TotalOrder.Raw.fst#L74 *)
(*
private let rec compare_rule_agg
  #nonterminal_pack #terminal_pack
  (l: list (symbol_union_t nonterminal_pack terminal_pack))
  (r: list (symbol_union_t nonterminal_pack terminal_pack))
  : Tot O.order (decreases %[l;r]) =
  match (l, r) with
  | ([], []) -> O.Eq
  | ([], _::_) -> O.Lt
  | (_::_, []) -> O.Gt
  | (l_head::l_tail, r_head::r_tail) ->
    match compare_rule_agg l_head r_head with
    | O.Lt -> O.Lt
    | O.Gt -> O.Gt
    | O.Eq -> compare_rule_agg l_tail r_tail
*)

let compare_rule
  #nonterminal_pack #terminal_pack
  (l: rule_t nonterminal_pack terminal_pack)
  (r: rule_t nonterminal_pack terminal_pack)
  : O.order =
  match nonterminal_pack.total_order.comparer l.lhs r.lhs with
  | O.Lt -> O.Lt
  | O.Gt -> O.Gt
  | O.Eq -> O.Eq




noeq type t = {
  nonterminal_pack: Fs.pack_t;
  terminal_pack: Fs.distinct_pack_t nonterminal_pack;

}

