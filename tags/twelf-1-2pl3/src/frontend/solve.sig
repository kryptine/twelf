(* Solve and query declarations, interactive top level *)
(* Author: Frank Pfenning *)

signature SOLVE =
sig

  structure IntSyn : INTSYN
  structure ExtSynQ : EXTSYN
  structure Paths : PATHS

  exception AbortQuery of string

  val solve : (IntSyn.name * ExtSynQ.term) * Paths.region -> IntSyn.ConDec

  val query : int option * int option * ExtSynQ.query -> unit (* may raise AbortQuery(msg) *)
  val qLoop : unit -> bool		(* true means normal exit *)

end;  (* signature SOLVE *)