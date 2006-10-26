structure Planner : PLANNER =
  struct
    local 
      structure I = IntSyn 

      fun plan name = 
	let
	  val cid = valOf (Names.constLookup (valOf (Names.stringToQid name)))
	  val V = I.conDecType (I.sgnLookup cid)
	in
	  print (Print.expToString (I.Null, V))
	end
    in
      val plan = plan 
    end
  end