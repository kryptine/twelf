(* Compiled Syntax *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)
(* Modified: Kevin Watkins *)

functor CompSyn (structure IntSyn' : INTSYN)
  : COMPSYN =
struct

  structure IntSyn = IntSyn'

  datatype Goal =                       (* Goals                      *)
    Atom of IntSyn.Exp                  (* g ::= p                    *)
  | Impl of ResGoal * IntSyn.Exp        (*     | (r,A,a) => g         *)
            * IntSyn.cid * Goal		
  | All  of IntSyn.Dec * Goal           (*     | all x:A. g           *)

  and ResGoal =                         (* Residual Goals             *)
    Eq     of IntSyn.Exp                (* r ::= p = ?                *)
  | And    of ResGoal                   (*     | r & (A,g)            *)
              * IntSyn.Exp * Goal       
  | In     of ResGoal                   (*     | r && (A,g)           *)
              * IntSyn.Exp * Goal       
  | Exists of IntSyn.Dec * ResGoal      (*     | exists x:A. r        *)

  and Query =
    QueryGoal of Goal
  | QueryVar  of IntSyn.Exp * IntSyn.Dec * Query

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

  (* Representation invariants for compiled syntax:
     Judgments:
       G |- g goal   g is a valid goal in G
       G |- r resgoal  g is a valid residual goal in G

       G |- A ~> g   A compiles to goal g
       G |- A ~> r   A compiles to residual goal r

     G |- p  goal
     if  G |- p : type, p = H @ S	(* mod whnf *)

     G |- (r, A, a) => g  goal
     if G |- A : type
        G |- r  resgoal
	G |- A ~> r
        a  target head of A (for indexing purposes)

     G |- all x:A. g  goal
     if G |- A : type
        G, x:A |- g  goal

     G |- q  resgoal
     if G |- q : type, q = H @ S	(* mod whnf *)

     G |- r & (A,g)  resgoal
     if G |- A : type
        G |- g  goal
        G |- A ~> g
        G, _:A |- r  resgoal

     G |- exists x:A. r  resgoal
     if  G |- A : type
         G, x:A |- r  resgoal

     G |- exists' x:A. r  resgoal     but exists' doesn't effect the proof-term
     if  G |- A : type
         G, x:A |- r  resgoal
  *)

  (* goalSub (g, s) = g'

     Invariants:
     If   G  |- s : G'    G' |- g : A
     then g' = g[s]
     and  G  |- g' : A
  *)
  fun goalSub (Atom(p), s) = Atom(IntSyn.EClo(p,s))
    | goalSub (Impl(d, A, a, g), s) =
       Impl (resGoalSub (d, s), IntSyn.EClo(A, s), a,
	     goalSub (g, IntSyn.dot1 s))
    | goalSub (All(D, g), s) =
       All (IntSyn.decSub(D,s), goalSub (g, IntSyn.dot1 s))

  (* resGoalSub (r, s) = r'

     Invariants:
     If   G  |- s : G'    G' |- r : A
     then r' = r[s]
     and  G  |- r' : A [s]
  *)
  and resGoalSub (Eq(q), s) = Eq (IntSyn.EClo (q,s))
    | resGoalSub (And(r, A, g), s) =
        And (resGoalSub (r, IntSyn.dot1 s), IntSyn.EClo(A,s), goalSub (g, s))
    | resGoalSub (In(r, A, g), s) =
        In (resGoalSub (r, IntSyn.dot1 s), IntSyn.EClo(A,s), goalSub (g, s))
    | resGoalSub (Exists(D, r), s) =
        Exists (IntSyn.decSub(D, s), resGoalSub (r, IntSyn.dot1 s))

end;  (* functor CompSyn *)
