(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)

signature TOMEGAPRINT =
sig
  structure IntSyn : INTSYN
  structure Tomega : TOMEGA 
  structure Formatter : FORMATTER

  val formatFor   : Tomega.Dec IntSyn.Ctx * Tomega.For -> Formatter.format
  val forToString : Tomega.Dec IntSyn.Ctx * Tomega.For -> string
  val formatPrg : Tomega.Dec IntSyn.Ctx * Tomega.Prg -> string list -> Formatter.format
(*  val formatLemmaDec: FunSyn.LemmaDec -> Formatter.format *)

  val prgToString : Tomega.Dec IntSyn.Ctx * Tomega.Prg -> string list -> string
(*  val lemmaDecToString : FunSyn.LemmaDec -> string *)
end;  (* signature TOMEGAPRINT *)

