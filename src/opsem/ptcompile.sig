(* Proof-theoretic compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)
(* Modified: Frank Pfenning *)
(* Modified: Kevin Watkins *)

signature PTCOMPILE =
sig

  structure IntSyn: INTSYN
  structure CompSyn: COMPSYN
  sharing IntSyn = CompSyn.IntSyn

  exception Error of string

  val compileClause: bool -> IntSyn.Exp -> CompSyn.ResGoal
  val compileGoal: bool -> IntSyn.Exp -> CompSyn.Goal
  val compileQuery: bool -> IntSyn.Exp -> CompSyn.Query
  val compileConDec: bool -> IntSyn.ConDec -> CompSyn.ResGoal option

end
