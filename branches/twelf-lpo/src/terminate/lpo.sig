(* Termination checking based on LPOs *)
(* Author: Jeffrey Sarnat, Carsten Schuermann *)

signature LPO =
sig
  exception Error of string

  val reset : unit -> unit
  val installDrop : IntSyn.cid * IntSyn.cid -> unit
  val printDrops : unit -> unit
end