(* Compiled Syntax *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Kevin Watkins *)

signature COMPSYN =
sig

  structure IntSyn : INTSYN

  datatype Goal =                       (* Goals                      *)
    Atom of IntSyn.Exp                  (* g ::= p                    *)
  | Impl of ResGoal * IntSyn.Exp        (*     | (r,A,a) => g         *)
            * IntSyn.cid * Goal		
  | All  of IntSyn.Dec * Goal           (*     | all x:A. g           *)

  and ResGoal =                         (* Residual Goals             *)
    Eq     of IntSyn.Exp                (* r ::= p = ?                *)
  | And    of ResGoal                   (*     | r & (A,g)            *)
              * IntSyn.Exp * Goal       
  | In   of ResGoal			(*     | r virt& (A,g)        *)
              * IntSyn.Exp * Goal       
  | Exists of IntSyn.Dec * ResGoal      (*     | exists x:A. r        *)
  | True                                (*     | true                 *)

  and Query =
    QueryGoal of Goal
  | QueryVar  of IntSyn.Exp * IntSyn.Dec * Query

  (* Dynamic programs: context with synchronous clause pool *)
  datatype DProg =
    DProg of (IntSyn.dctx * (ResGoal * IntSyn.Sub * IntSyn.cid) option IntSyn.Ctx)

  datatype GoalSol =
    DynAtom   of int * ResGoalSol
  | SigAtom   of IntSyn.cid * ResGoalSol
  | ConstrSol of int (* which try? *)
  | ImplSol   of GoalSol
  | AllSol    of GoalSol

  and ResGoalSol =
    EqSol
  | AndSol    of ResGoalSol * GoalSol
  | ExistsSol of ResGoalSol
  | TrueSol

  (* Explicit Substitutions *)
  val goalSub   : Goal * IntSyn.Sub -> Goal
  val resGoalSub: ResGoal * IntSyn.Sub -> ResGoal

end;  (* signature COMPSYN *)
