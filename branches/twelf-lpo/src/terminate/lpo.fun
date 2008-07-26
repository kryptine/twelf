(* Termination checking based on LPOs *)
(* Author: Jeffrey Sarnat, Carsten Schuermann *)

functor Lpo (structure Subordinate : SUBORDINATE)
	: LPO =
struct
  exception Error of string
  datatype 'a partialOrder = LT of 'a * 'a 
			   | EQ of 'a * 'a 
			   | NLE of 'a * 'a
  local
    open Int
    structure S = Subordinate
    structure I = IntSyn
    fun reset () = ()
    fun installDrop (c1, c2) = ()
	
    (* Invariant :  c1, c2 object level constants *)
    fun installOrder (c1, c2) = 
	print  ("(" ^ Int.toString c1 ^ "," ^  Int.toString c2 ^ ")\n")
	    
    fun orderLookup (cid1, cid2) =
	let
	  val V1 = I.constType cid1
	  val V2 = I.constType cid2
	in
	  (case (compare (cid1, cid2))
	    of LESS => LT (V1,V2)
	     | EQUAL => EQ (V1, V2)
	     | GREATER => NLE (V1, V2))
	end
    fun isDropped (c1, c2) = false
			    
  in
  val reset = reset
  val installDrop = installDrop
  val installOrder = installOrder
  val orderCompare = orderLookup
  val isDropped = isDropped
  end 
end
