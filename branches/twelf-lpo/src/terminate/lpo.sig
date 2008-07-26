(* Termination checking based on LPOs *)
(* Author: Jeffrey Sarnat, Carsten Schuermann *)

signature LPO =
sig
  exception Error of string
  datatype 'a partialOrder = LT of 'a * 'a 
			   | EQ of 'a * 'a 
			   | NLE of 'a * 'a
		     
  val reset : unit -> unit (* for twelf server resets *)
  val installDrop : IntSyn.cid * IntSyn.cid -> unit  (* adds type constants
							to the drop relation *)

  val installOrder : IntSyn.cid * IntSyn.cid -> unit (* adds term constants
							     to the precedence
							     ordering *)
  val isDropped : IntSyn.cid * IntSyn.cid -> bool

  val orderCompare : IntSyn.cid * IntSyn.cid -> IntSyn.Exp partialOrder


end
