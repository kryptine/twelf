(* Delphin Frontend *)
(* Author: Carsten Schuermann *)
(* Modified by Richard Fontana *)

functor Delphin ((* structure Tomega : TOMEGA *)
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


    (* Added by ABP - Temporary to run tests *)
    structure I = IntSyn
    structure T = Tomega

  (* input:
      elfFile = .elf file to load
      funcList = list of functions that need to be loaded
                 first element is the function that will be called
      arg = LF object which is the argument
      isDef = if false, it is a Const
   *)

    fun runSimpleTest elfFile funcList arg isDef = 
      let

	fun test (names as [name]) =
	  (let 
	     val La = map (fn x => valOf (Names.constLookup (valOf (Names.stringToQid x)))) names
	     val (lemma, projs, sels) = Converter.installPrg La
	     val P = Tomega.lemmaDef lemma
	     val F = Converter.convertFor La	       
	     val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F))
	     val _ = TextIO.print ("\n" ^ TomegaPrint.funToString ((map (fn (cid) => IntSyn.conDecName (IntSyn.sgnLookup cid)) La,
						     projs), P) ^ "\n")	
	   in P
	   end)
	  | test names =
	  (let 
	     val La = map (fn x => valOf (Names.constLookup (valOf (Names.stringToQid x)))) names
	     val (lemma, projs, sels) = Converter.installPrg La
	     val P = Tomega.lemmaDef lemma
	     val F = Converter.convertFor La	       
	     val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F))
	     val _ = TextIO.print ("\n" ^ TomegaPrint.funToString ((map (fn (cid) => IntSyn.conDecName (IntSyn.sgnLookup cid)) La,
						     projs), P) ^ "\n")	
	   in Tomega.lemmaDef (hd sels)
	   end)

	val _ = Twelf.loadFile elfFile
	val P = test funcList
(*	val _ = TextIO.print ("\n" ^ TomegaPrint.funToString (([name], []), P) ^ "\n") *)

	val x = valOf (Names.constLookup (valOf (Names.stringToQid arg)))

	val P' = if isDef then (T.Redex(P, T.AppExp (I.Root (I.Def x, I.Nil), T.Nil))) else (T.Redex(P, T.AppExp (I.Root (I.Const x, I.Nil), T.Nil))) 

	val result = Opsem.evalPrg P'
	val _ = TextIO.print "\n\nEOC\n\n"
	val _ = TextIO.print (TomegaPrint.prgToString (I.Null, result))
	val _ = TextIO.print "\n"
      in
	()
      end

    fun eval P = Opsem.evalPrg P


    (* **************************************** *)


  in
    val version = version
    val loadFile = loadFile
    val top = top

    val runSimpleTest = runSimpleTest
    val eval = eval

  end
end  (* functor Delphin *)
