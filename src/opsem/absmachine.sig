(* Abstract Machine (signature common to all abstract machines) *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)
(* Modified: Kevin Watkins *)

signature ABSMACHINE =
sig

  structure IntSyn  : INTSYN
  structure CompSyn : COMPSYN
  structure Compile : COMPILE
  sharing Compile.IntSyn = IntSyn
  sharing Compile.CompSyn = CompSyn

  val trail : (unit -> unit) -> unit
  val solve : CompSyn.Query * (IntSyn.Exp -> unit) -> unit
  val gBoundedSolve : int * CompSyn.Goal * int * Compile.DProg *
        (IntSyn.Exp -> unit) -> unit
  val rBoundedSolve : int * CompSyn.ResGoal * int * Compile.DProg *
        (IntSyn.Spine -> unit) -> unit
  val reset : unit -> unit

end;  (* signature ABSMACHINE *)
