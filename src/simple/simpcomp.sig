(* Simple compiler *)
(* Author: Kevin Watkins *)

signature SIMPCOMP =
sig

  include COMPILE

  structure SimpSyn : SIMPSYN

  (* Dynamic programs: clause pool *)
  (* In the simple compiler there is no context because types
     are unnecessary. *)
  type DProg = (SimpSyn.ResGoal * SimpSyn.Sub * IntSyn.cid) IntSyn.Ctx

  (* Static programs --- compiled version of the signature *)
  datatype ConDec =			(* Compiled constant declaration *)
    SClause of SimpSyn.ResGoal          (* c : A                      *)
  | Void 		                (* Other declarations are ignored  *)
  val sProgLookup : IntSyn.cid -> ConDec

  val translQuery : CompSyn.Query -> SimpSyn.Query

end
