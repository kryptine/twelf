signature TRACE =
sig

  (* Program interface *)
  structure IntSyn : INTSYN

  type goalTag
  val tagGoal : unit -> goalTag

  datatype Event =
    IntroHyp of IntSyn.Head * IntSyn.Dec
  | DischargeHyp of IntSyn.Head * IntSyn.Dec

  | IntroParm of IntSyn.Head * IntSyn.Dec
  | DischargeParm of IntSyn.Head * IntSyn.Dec

  | Resolved of IntSyn.Head * IntSyn.Head (* resolved with clause c, fam a *)
  | Subgoal of (IntSyn.Head * IntSyn.Head) * (unit -> int) (* clause c, fam a, nth subgoal *)

  | SolveGoal of goalTag * IntSyn.Head * IntSyn.Exp
  | RetryGoal of goalTag * (IntSyn.Head * IntSyn.Head) * IntSyn.Exp
  | FailGoal of goalTag * IntSyn.Head * IntSyn.Exp

  | Unify of (IntSyn.Head * IntSyn.Head) * IntSyn.Exp * IntSyn.Exp (* clause head == goal *)
  | FailUnify of IntSyn.Head * IntSyn.Head

  val signal : IntSyn.dctx * Event -> unit
  val init : unit -> unit		(* initialize trace, break and tag *)

  (* User interface *)
  datatype 'a Spec =
    None
  | Some of 'a list
  | All

  val trace : string Spec -> unit
  val break : string Spec -> unit
  val level : int ref			(* 0 = no tracing, 1 = default, 2 = failure info *)

  val status : unit -> unit
  val reset : unit -> unit		(* remove all tracing and breakpoints *)

end;  (* signature TRACE *)
