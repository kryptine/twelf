
(* Compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

signature COMPILE =
sig

  structure IntSyn: INTSYN
  structure CompSyn: COMPSYN

  exception Error of string

  datatype opt = datatype CompSyn.opt

  val optimize : opt ref

  val install : bool -> IntSyn.cid -> unit

  val sProgReset : unit -> unit

(* Mon Jun 24 09:46:15 2002 -bp : not used
  val compileClause: bool -> (IntSyn.Dec IntSyn.Ctx * IntSyn.Exp)
                          -> (IntSyn.Exp * IntSyn.Dec IntSyn.Ctx * CompSyn.AuxGoal * int * CompSyn.SubGoals)
*)
  val compileCtx: bool -> (IntSyn.Dec IntSyn.Ctx) -> CompSyn.DProg  

  val compileGoal: (IntSyn.Dec IntSyn.Ctx * IntSyn.Exp) -> CompSyn.Goal

end; (* signature COMPILE *)
