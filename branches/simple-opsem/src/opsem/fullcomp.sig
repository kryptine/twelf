(* Full compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)
(* Modified: Frank Pfenning *)
(* Modified: Kevin Watkins *)

signature FULLCOMP =
sig

  include COMPILE

  (* Dynamic programs: context with synchronous clause pool *)
  datatype DProg = DProg of (IntSyn.dctx * (CompSyn.ResGoal * IntSyn.Sub * IntSyn.cid) option IntSyn.Ctx)

  (* Static programs --- compiled version of the signature *)
  datatype ConDec =			(* Compiled constant declaration *)
    SClause of CompSyn.ResGoal          (* c : A                      *)
  | Void 		                (* Other declarations are ignored  *)

  val sProgInstall : IntSyn.cid * ConDec -> unit
  val sProgLookup: IntSyn.cid -> ConDec
  val sProgReset : unit -> unit

  val compileCtx: IntSyn.Dec IntSyn.Ctx -> DProg
  val compileGoal: IntSyn.Exp -> CompSyn.Goal

end
