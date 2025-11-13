(* Reference: JAY EARLEY, An Efficient Context-Free Parsing Algorithm *)

module EarleyParser.Language
module O = FStar.OrdSet
module T = FStar.Class.TotalOrder.Raw
open FStar.FunctionalExtensionality { (^->) }
module L = FStar.List.Tot

let is_total_order (a:eqtype) (f: (a -> a -> Tot bool)) : prop =
  squash (O.total_order a f)


(* A language is a set of strings over a finite set of symbols. *)

noeq type config_t = {
  lower_symbol_t: eqtype;
  lower_symbol_comparer: O.cmp lower_symbol_t;
  terminal_set: O.ordset lower_symbol_t lower_symbol_comparer;
  //string_t: (t:eqtype{t == list (x:terminal_symbol_t{O.mem x terminal_symbol_set})});
  is_language: (x:list lower_symbol_t{forall s. O.mem s terminal_set}) ^-> bool;
  upper_symbol_t: (x:eqtype{lower_symbol_t =!= x});
}

let is_terminal (config:config_t) (lower_symbol:config.lower_symbol_t) : bool =
  O.mem lower_symbol config.terminal_set

let is_string (config:config_t) (lower_symbols:list config.lower_symbol_t) : bool =
  L.for_all (is_terminal config) lower_symbols



