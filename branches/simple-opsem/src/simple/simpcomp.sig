(* Simple compiler *)
(* Author: Kevin Watkins *)

signature SIMPCOMP =
sig

  structure IntSyn: INTSYN
  structure CompSyn: COMPSYN
  structure SimpSyn : SIMPSYN
  sharing SimpSyn.IntSyn = IntSyn

  (* Dynamic programs: clause pool *)
  (* In the simple compiler there is no context because types
     are unnecessary. *)
  type DProg = CompSyn.DProg * ((SimpSyn.ResGoal * SimpSyn.Sub * IntSyn.cid) option) IntSyn.Ctx

  val compileCtx : bool -> IntSyn.dctx -> DProg

  val installResGoal : IntSyn.cid * CompSyn.ResGoal -> unit
  val install : bool -> IntSyn.cid -> unit
  val reset : unit -> unit
  (*include COMPILE where type DProg = SimpSyn.DProg*)

  (* Static programs --- compiled version of the signature *)
  datatype ConDec =			(* Compiled constant declaration *)
    SClause of SimpSyn.ResGoal          (* c : A                      *)
  | Void 		                (* Other declarations are ignored  *)
  val sProgLookup : IntSyn.cid -> ConDec

  val translGoal : IntSyn.dctx * (CompSyn.Goal * IntSyn.Sub) -> SimpSyn.Goal
  val translResGoal : IntSyn.dctx * (CompSyn.ResGoal * IntSyn.Sub) -> SimpSyn.ResGoal
  val translQuery : IntSyn.dctx * CompSyn.Query -> SimpSyn.Query

end
