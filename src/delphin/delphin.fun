(* Delphin Frontend *)
(* Author: Carsten Schuermann *)
(* Modified by Richard Fontana *)

functor Delphin (structure Tomega : TOMEGA
		 structure Parser : PARSER
		 structure DextSyn : DEXTSYN
		 structure Parse : PARSE
		   sharing Parse.DextSyn = DextSyn
		 structure Twelf : TWELF
		 structure Trans : TRANS
		   sharing Trans.DextSyn = DextSyn) : DELPHIN =
struct
  local
    val version = "Delphin, Version 0.1, January 2003"

    val prompt = "Delphin> "
    
    fun loadFile (s1, s2) =
      let 
	val _ = Twelf.loadFile s1
	val (DextSyn.Ast EDs) = Parse.gparse s2
	val P = Trans.transDecs EDs
      in 
	()
      end

    fun top () = loop ()

    and loop () = 
      let 
         val _ = print prompt
         val (DextSyn.Ast ED) = Parse.sparse ()
         val res = Trans.transDecs ED   
      in 
         loop ()
      end

  in
    val version = version
    val loadFile = loadFile
    val top = top
  end
end  (* functor Delphin *)
