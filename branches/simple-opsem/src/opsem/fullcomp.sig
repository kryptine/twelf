(* Full compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)
(* Modified: Frank Pfenning *)
(* Modified: Kevin Watkins *)

signature FULLCOMP =
sig

  structure IntSyn: INTSYN
  structure CompSyn: COMPSYN

  type DProg = CompSyn.DProg

  val compileCtx : bool -> IntSyn.dctx -> DProg

  val installResGoal : IntSyn.cid * CompSyn.ResGoal -> unit
  val install : bool -> IntSyn.cid -> unit
  val reset : unit -> unit
  (*include COMPILE where type DProg = CompSyn.DProg*)

  (* Static programs --- compiled version of the signature *)
  datatype ConDec =			(* Compiled constant declaration *)
    SClause of CompSyn.ResGoal          (* c : A                      *)
  | Void 		                (* Other declarations are ignored  *)

  val sProgLookup: IntSyn.cid -> ConDec

end
