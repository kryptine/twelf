signature ELABSOLUTION =
sig

  structure IntSyn : INTSYN
  structure CompSyn : COMPSYN

  exception BadSolution of string

  val elaborate : CompSyn.GoalSol * CompSyn.Query -> IntSyn.Exp

end
