(* Termination checking based on LPOs *)
(* Author: Jeffrey Sarnat, Carsten Schuermann *)

functor Lpo (structure Subordinate : SUBORDINATE)
	: LPO =
struct
  exception Error of string
  datatype partialOrder = LT | EQ | NLE
  local
    open Int
    structure S = Subordinate
    fun reset () = ()
    fun installDrop (c1, c2) = ()
	
    (* Invariant :  c1, c2 object level constants *)
    fun installOrder (c1, c2) = 
	print  ("(" ^ Int.toString c1 ^ "," ^  Int.toString c2 ^ ")\n")
	    
    fun orderLookup (c1, c2) = case (compare (c1, c2))
				of LESS => LT
				 | EQUAL => EQ
				 | GREATER => NLE
					      
    fun isDropped (c1, c2) = false
			    
  in
  val reset = reset
  val installDrop = installDrop
  val installOrder = installOrder
  val orderCompare = orderLookup
  val isDropped = isDropped
  end 
end
