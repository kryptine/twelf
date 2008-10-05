(* Termination checking based on LPOs *)
(* Author: Jeffrey Sarnat, Carsten Schuermann *)

functor Lpo (structure Subordinate : SUBORDINATE
	     structure Table : TABLE where type key = IntSyn.cid * IntSyn.cid )
	: LPO =
struct
  exception Error of string
  datatype partialOrder = LT
			   | EQ
			   | NLE
  local
    structure T = Table
    structure S = Subordinate
    structure I = IntSyn
		  
    val dropTable = T.new 1171 : unit T.Table

    fun reset () = T.clear dropTable

    fun installDrop (cids as (cid1, cid2)) = 
(*	if (S.frozen cid1 orelse (S.frozen cid2))
	     raise Error 
*)
	T.insert dropTable (cids, ())
	
    (* Invariant :  c1, c2 object level constants *)
    fun installOrder (c1, c2) = 
	print  ("(" ^ Int.toString c1 ^ "," ^  Int.toString c2 ^ ")\n")

    fun isDropped (c1, c2) = 
	(case (T.lookup dropTable (c1,c2))
	  of NONE => false
	   | _ => true 
		  )

    fun getDropList n VS =
	let
	  val a' = I.targetFam VS
	  fun getDrop' _ (I.Root _)  = nil
	    | getDrop' m (I.Pi ((I.Dec(_, V), _), V')) = 
			  let
			    val b = (m < n) orelse 
				    isDropped((I.targetFam V), a')
			  in
			    b::(getDrop' (m+1) (V'))
			  end
	in
	  getDrop' 0 VS
	end

    val cidDropList = fn cid => getDropList
				  (I.constImp cid) 
				  (I.constType cid)

	    
    fun orderLookup (cid1, cid2) =
	let
	  val a1 = I.targetFam (I.constType cid1)
	  val a2 = I.targetFam (I.constType cid2)
	in
	  if (S.below(a1,a2) andalso not (S.belowEq(a1,a2)))
	  then LT else
	  (case (Int.compare (cid1, cid2))
	    of LESS => LT
	     | EQUAL => EQ
	     | GREATER => NLE
			  )
	end


			    
  in
  val reset = reset
  val installDrop = installDrop
  val installOrder = installOrder
  val orderCompare = orderLookup
  val isDropped = isDropped
  val typeToDropList = (* fn V => map (fn _ => false) (getDropList 0 V) *)
      getDropList 0 
  val cidDropList = cidDropList
  end 
end
