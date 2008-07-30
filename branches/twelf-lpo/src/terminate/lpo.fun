(* Termination checking based on LPOs *)
(* Author: Jeffrey Sarnat, Carsten Schuermann *)

functor Lpo (structure Subordinate : SUBORDINATE
	     structure Table : TABLE where type key = IntSyn.cid * IntSyn.cid )
	: LPO =
struct
  exception Error of string
  datatype 'a partialOrder = LT of 'a * 'a 
			   | EQ of 'a * 'a 
			   | NLE of 'a * 'a
  local
    structure T = Table
    structure S = Subordinate
    structure I = IntSyn
		  
    val dropTable = T.new 1171 : unit T.Table

    fun reset () = T.clear dropTable

    fun installDrop cids = 
	T.insert dropTable (cids, ())
	
    (* Invariant :  c1, c2 object level constants *)
    fun installOrder (c1, c2) = 
	print  ("(" ^ Int.toString c1 ^ "," ^  Int.toString c2 ^ ")\n")
	    
    fun orderLookup (cid1, cid2) =
	let
	  val V1 = I.constType cid1
	  val V2 = I.constType cid2
	in
	  (case (Int.compare (cid1, cid2))
	    of LESS => LT (V1,V2)
	     | EQUAL => EQ (V1, V2)
	     | GREATER => NLE (V1, V2))
	end
    fun isDropped (c1, c2) = 
	(case (T.lookup dropTable (c1,c2))
	      of NONE => false
	       | _ => true (* (print ("dropped: (" ^ Int.toString c1 ^", " ^ Int.toString c2 ^ ") \n"); true)*) 
		      )
			    
  in
  val reset = reset
  val installDrop = installDrop
  val installOrder = installOrder
  val orderCompare = orderLookup
  val isDropped = isDropped
  end 
end
