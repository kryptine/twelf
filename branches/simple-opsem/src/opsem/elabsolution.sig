signature ELABSOLUTION =
sig

  structure IntSyn : INTSYN
  structure CompSyn : COMPSYN

  exception BadSolution of string

  val elaborate : CompSyn.GoalSol * CompSyn.Query -> IntSyn.Exp
  val elaborateMeta : CompSyn.GoalSol * CompSyn.Goal * int * CompSyn.DProg -> IntSyn.Exp
  val elaborateRMeta : CompSyn.ResGoalSol * CompSyn.ResGoal * int * CompSyn.DProg -> IntSyn.Spine

end
