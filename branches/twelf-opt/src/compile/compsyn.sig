(* Compiled Syntax *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)

signature COMPSYN =
sig

  structure IntSyn : INTSYN

  datatype opt = no | linearHeads | indexing

  val optimize : opt ref

  datatype Goal =                       (* Goals                      *)
    Atom of IntSyn.Exp                  (* g ::= p                    *)
  | Impl of ResGoal * IntSyn.Exp        (*     | (r,A,a) => g         *)
            * IntSyn.Head * Goal		
  | All  of IntSyn.Dec * Goal           (*     | all x:A. g           *)

  (* dynamic clauses *)
  and ResGoal =                         (* Residual Goals             *)
    Eq     of IntSyn.Exp                (* r ::= p = ?                *)
  | Assign of IntSyn.Exp * AuxGoal      (*     | p = ?, where p has   *)
					(* only new vars,             *)  
                                        (* then unify all the vars    *)
  | And    of ResGoal                   (*     | r & (A,g)            *)
              * IntSyn.Exp * Goal       
  | In   of ResGoal			(*     | r virt& (A,g)        *)
              * IntSyn.Exp * Goal       
  | Exists of IntSyn.Dec * ResGoal      (*     | exists x:A. r        *)
  | Axists of IntSyn.Dec * ResGoal	(*     | exists x:_. r        *)

  and AuxGoal =
    Trivial				  (* trivially done *)
  | UnifyEq of IntSyn.dctx * IntSyn.Exp   (* call unify *)
             * IntSyn.Exp * AuxGoal


  (* Static programs -- compiled version for substitution trees *)

  datatype Conjunction = True | Conjunct of Goal * Conjunction 

  datatype CompHead = 
     Head of (IntSyn.Exp * IntSyn.Dec IntSyn.Ctx * AuxGoal * IntSyn.cid)

 (* pskeleton instead of proof term *)
  datatype Flatterm = 
    Pc of int | Dc of int | Csolver

  type pskeleton = Flatterm list  


  (* The dynamic clause pool --- compiled version of the context *)
  (* type dpool = (ResGoal * IntSyn.Sub * IntSyn.cid) option IntSyn.Ctx *)

  (* Dynamic programs: context with synchronous clause pool *)
  datatype DProg = DProg of (IntSyn.dctx * (ResGoal * IntSyn.Sub * IntSyn.Head) option IntSyn.Ctx)

  (* Programs --- compiled version of the signature (no indexing) *)
  datatype ConDec =			(* Compiled constant declaration *)
    SClause of ResGoal	                (* c : A                      *)
  | Void 		                (* Other declarations are ignored  *)

  (* Install Programs (without indexing) *)
  val sProgInstall : IntSyn.cid * ConDec -> unit  
  val sProgLookup: IntSyn.cid -> ConDec
  val sProgReset : unit -> unit

  (* Deterministic flag *)
  val detTableInsert : IntSyn.cid * bool -> unit
  val detTableCheck : IntSyn.cid -> bool
  val detTableReset : unit -> unit

  (* Explicit Substitutions *)
  val goalSub   : Goal * IntSyn.Sub -> Goal
  val resGoalSub: ResGoal * IntSyn.Sub -> ResGoal

  val pskeletonToString: pskeleton -> string

end;  (* signature COMPSYN *)