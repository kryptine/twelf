(* Tabled Abstract Machine      *)
(* Author: Brigitte Pientka     *)

signature TABLED =
sig

  structure IntSyn  : INTSYN
  structure CompSyn : COMPSYN
  structure TableParam : TABLEPARAM
(*  structure Unify : UNIFY *)

  val solve     : (CompSyn.Goal * IntSyn.Sub) * CompSyn.DProg
                  * (CompSyn.pskeleton -> unit) -> unit

  val nextStage : unit -> bool

  val reset : unit -> unit

(*  val solExists : (IntSyn.Exp * IntSyn.Sub) -> bool *)

  val tableSize : unit -> int
  val suspGoalNo : unit -> int

end;  (* signature TABLED *)

