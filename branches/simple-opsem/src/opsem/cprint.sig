(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)
(* Modified: Kevin Watkins *)

signature CPRINT =
sig

  structure IntSyn: INTSYN
  structure CompSyn: COMPSYN
  structure FullComp: FULLCOMP

  val goalToString: string -> IntSyn.dctx * CompSyn.Goal -> string
  val clauseToString: string -> IntSyn.dctx * CompSyn.ResGoal -> string
  val sProgToString: unit -> string
  val dProgToString: FullComp.DProg -> string

  val rsolToString : string -> CompSyn.ResGoalSol -> string
  val solToString : string -> CompSyn.GoalSol -> string

end; (* signature CPRINT *)
