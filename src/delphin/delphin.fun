(* Delphin Frontend *)
(* Author: Carsten Schuermann *)
(* Modified by Richard Fontana *)

functor Delphin (structure Tomega : TOMEGA
		 structure Parser : PARSER
		 structure DextSyn : DEXTSYN
		 structure Parse : PARSE
		   sharing Parse.DextSyn = DextSyn
		 structure Twelf : TWELF) : DELPHIN =
struct
  local
    val prompt = "- "
    
    fun loadFile (s1, s2) =
      let 
	val _ = Twelf.loadFile s1
	val (DextSyn.Ast EDs) = Parse.gparse s2
	val P = Trans.transDecs EDs
      in 
	()
      end

    fun top () = 
      let 
        val _ = print "Delphin, Version 1.0, March 2002\n"
      in
        loop ()
      end     

    and loop () = 
      let 
         val _ = print prompt
         val (DextSyn.Ast ED) = Parse.sparse ()
         val res = Trans.transDecs ED   
      in 
         loop ()
      end

  in
    val loadFile = loadFile
    val top = top
  end
end  (* functor Delphin *)
