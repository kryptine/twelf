(* Termination checking based on LPOs *)
(* Author: Jeffrey Sarnat, Carsten Schuermann *)

signature LPO =
sig
  exception Error of string
  datatype partialOrder = LT | EQ | NLE 
		     
  val reset : unit -> unit (* for twelf server resets *)
  val installDrop : IntSyn.cid * IntSyn.cid -> unit  (* adds type constants
							to the drop relation *)

  val installOrder : IntSyn.cid * IntSyn.cid -> unit (* adds term constants
							     to the precedence
							     ordering *)
  val isDropped : IntSyn.cid * IntSyn.cid -> bool

  val orderCompare : IntSyn.cid * IntSyn.cid -> partialOrder


end
