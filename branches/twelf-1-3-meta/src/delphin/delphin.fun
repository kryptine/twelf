(* Delphin Frontend *)
(* Author: Carsten Schuermann *)

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

    val prompt = "> "
    
    fun loadFile (s1, s2) =
      let 
	val _ = Twelf.reset ()
	val _ = Twelf.loadFile s1
	val _ = Trans.internalizeSig ()
	val (DextSyn.Ast EDs) = Parse.gparse s2
	val _ = print "* parsing completed\n"
	val P = Trans.transDecs EDs
	val P' = Trans.externalizePrg P 
	val _  = TomegaTypeCheck.checkPrg (IntSyn.Null, (P, Tomega.True))
	val V  = Opsem.evalPrg P'
      in 
	V
      end

    fun top () = loop ()

    and loop () = 
      let 
         val _ = print prompt
         val (DextSyn.Ast ED) = Parse.sparse ()
(*         val res = Trans.transDecs ED    *)
      in 
         loop ()
      end


    (* Added by ABP - Temporary to run tests *)
    structure I = IntSyn
    structure T = Tomega

  (* input:
      sourcesFile = .elf file to load
      funcList = list of functions that need to be loaded
                 first element is the function that will be called
      arg = LF object which is the argument
   *)

    fun runSimpleTest sourcesFile funcList args  = 
      let

	fun test (names as [name]) =
	  (let 
	     val La = map (fn x => valOf (Names.constLookup (valOf (Names.stringToQid x)))) names
	     val (lemma, projs, sels) = Converter.installPrg La
	     val P = Tomega.lemmaDef lemma
(*	     val P = Redundant.convert (Tomega.lemmaDef lemma) *)
	     val F = Converter.convertFor La	       
	     val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F))
	     val _ = TextIO.print ("\n" ^ TomegaPrint.funToString ((map (fn (cid) => IntSyn.conDecName (IntSyn.sgnLookup cid)) La,
						     projs), P) ^ "\n")	
	   in (P, F)
	   end)
	  | test names =
	  (let 
	     val La = map (fn x => valOf (Names.constLookup (valOf (Names.stringToQid x)))) names
	     val (lemma, projs, sels) = Converter.installPrg La
	     (* val P = Tomega.lemmaDef lemma *)
	     val P = Redundant.convert (Tomega.lemmaDef lemma)
	     val F = Converter.convertFor La	       

	     val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F))
	     val _ = TextIO.print ("\n" ^ TomegaPrint.funToString ((map (fn (cid) => IntSyn.conDecName (IntSyn.sgnLookup cid)) La,
						     projs), P) ^ "\n")	
	   in (Tomega.lemmaDef (hd sels), F)
	   end)

	fun checkDec (u, D as T.UDec (I.Dec (_, V))) =  (print "$"; TypeCheck.typeCheck (I.Null, (u, V)))
(*	  | checkDec (u, D as PDec (_, T.All (D, F')))) = ???  *)
	  
	  

	fun makeSpine ([], F) = (T.Nil, F)
	  | makeSpine (x :: L, F' as T.And (F1, F2)) =
	    let 
	      val (S', F') =  makeSpine (L, Normalize.normalizeFor (F', T.Dot (T.Exp (I.Root (I.Def x, I.Nil)), T.id)))
	    in
	      (T.AppExp (I.Root (I.Def x, I.Nil), S'), F')
	    end

	  | makeSpine (x :: L, T.All ((D, _), F')) = 
	    let 
	      val _ = checkDec(I.Root (I.Def x, I.Nil), D)
	      val (S', F') =  makeSpine (L, Normalize.normalizeFor (F', T.Dot (T.Exp (I.Root (I.Def x, I.Nil)), T.id)))
	    in
	      (T.AppExp (I.Root (I.Def x, I.Nil), S'), F')
	    end
	val _ = Twelf.make sourcesFile
	val (P, F) = test funcList

	val _ = print ((TomegaPrint.forToString (I.Null, F)) ^ "\n")
(*	val _ = TextIO.print ("\n" ^ TomegaPrint.funToString (([name], []), P) ^ "\n") *)

	val xs = map (fn a => valOf (Names.constLookup (valOf (Names.stringToQid a)))) args

	val  (S', F') = makeSpine (xs, F) 
	val P' = T.Redex(P, S')

	val _ = TomegaTypeCheck.checkPrg (I.Null, (P', F'))


(*	val P' = if isDef then (T.Redex(P, T.AppExp (I.Root (I.Def x, I.Nil), T.
Nil))) else (T.Redex(P, T.AppExp (I.Root (I.Const x, I.Nil), T.Nil))) 
*)

	  (*
	val _ = TextIO.print "\n"
	val _ = TextIO.print (TomegaPrint.prgToString (I.Null, P'))
	val _ = TextIO.print "\n"
	   *)


(*  T.AppExp (I.Root (I.Def x, I.Nil), T.Nil) *)
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
