(* Translator from Delphin external syntax to Delphin internal syntax *)
(* Author:  Carsten Schuermann, Richard Fontana *)


functor Trans (structure DextSyn' : DEXTSYN) (* : TRANS *) =

struct

  structure DextSyn = DextSyn'
  structure D = DextSyn'
  
  structure L = Lexer
  structure I = IntSyn 
  structure LS = Stream  
  structure T = Tomega
  

  exception Error of string
  local 

   (* checkEOF f = r 
       
      Invariant:
      If   f is the end of stream
      then r is a region
	 
      Side effect: May raise Parsing.Error
    *)   

    fun checkEOF (LS.Cons ((L.EOF, r), s')) = r (* region information useless 
						   since it only refers to string --cs *)
      | checkEOF (LS.Cons ((t, r), _))  = 
          Parsing.error (r, "Expected `}', found " ^ L.toString t)  
         (* Note that this message is inapplicable when we use  
            checkEOF in stringToterm --rf *)



                                                            
    (* stringToDec s = dec

       Invariant:
       If   s is a string representing a declaration,
       then dec is the result of parsing it
       otherwise Parsing.error is raised.
    *)
    fun stringTodec s = 
      let 
        val f = LS.expose (L.lexStream (TextIO.openString s))
	val ((x, yOpt), f') = ParseTerm.parseDec' f
	val r2 = checkEOF f'
	val dec = (case yOpt		(* below use region arithmetic --cs !!!  *)
		     of NONE => ReconTerm.dec0 (x, r2)
	              | SOME y => ReconTerm.dec (x, y, r2))
      in
	dec
      end



    fun stringToblocks s =
      let 
        val f = LS.expose (L.lexStream (TextIO.openString s))
        val (dl, f') = ParseTerm.parseCtx' f
      in
        dl
      end

    (* stringToWorlds s = W

       Invariant:
       If   s is a string representing an expression,
       then W is the result of parsing it
       otherwise Parsing.error is raised.
    *)
    fun stringToWorlds s = 
        let 
          val f = LS.expose (L.lexStream (TextIO.openString s))
	  val (t, f') = ParseTerm.parseQualIds' f
	  val r2 = checkEOF f'
        in
	  t
        end

    fun transTerm (D.Rtarrow (t1, t2)) = 
        let 
	  val (s1, c1) = transTerm t1
	  val (s2, c2) = transTerm t2
	in
	  (s1 ^ " -> " ^ s2, c1 @ c2)
	end
      | transTerm (D.Ltarrow (t1, t2)) = 
        let 
	  val (s1, c1) = transTerm t1
	  val (s2, c2) = transTerm t2
	in
	  (s1 ^ " <- " ^ s2, c1 @ c2)
	end
      | transTerm (D.Type) = ("type", nil)
      | transTerm (D.Id s) = (s, nil)
      | transTerm (D.Pi (D, t)) = 
        let 
	  val (s1, c1) = transDec D
	  val (s2, c2) = transTerm t
	in
	  ("{" ^ s1 ^ "}" ^ s2, c1 @ c2)
	end
      | transTerm (D.Fn (D, t)) =
        let 
	  val (s1, c1) = transDec D
	  val (s2, c2) = transTerm t
	in
	  ("[" ^ s1 ^ "]" ^ s2, c1 @ c2)
	end
      | transTerm (D.App (t1, t2)) =
        let 
	  val (s1, c1) = transTerm t1
	  val (s2, c2) = transTerm t2
	in
	  (s1 ^ " " ^ s2, c1 @ c2)
	end
      | transTerm (D.Omit) = ("_", nil)
      | transTerm (D.Paren (t)) =
	let 
	  val (s, c) = transTerm t
	in
	  ("(" ^  s ^ ")", c)
	end
      | transTerm (D.Of (t1, t2)) = 
	let
	  val (s1, c1) = transTerm t1
	  val (s2, c2) = transTerm t2
	in
	  (s1 ^ ":" ^ s2, c1 @ c2)
	end
(*      | transTerm (D.Dot (D.Id s1, s2)) = 
	("PROJ#" ^ s1 ^ "#" ^ s2, nil)
      | transTerm (D.Dot (D.Paren (D.Of (D.Id s1, t)), s2)) = 
	("PROJ#" ^ s1 ^ "#" ^ s2, [(s1, t)])
*)
	  
    and transDec (D.Dec (s, t)) = 
        let
	  val (s', c) = transTerm t
	in 
	  (s ^ ":" ^ s', c)
	end

    fun transWorld (D.WorldIdent s) =
	   (* We should use the worlds we have defined in Tomega, but this
	      is not good enough, because worlds are not defined
	      by a regualar expression.  Therefore this is a patch *)
        let
          val qid = Names.Qid (nil, s)
	  val cid = (case Names.constLookup qid
			            of NONE => raise Names.Error ("Undeclared label "
                                         ^ Names.qidToString (valOf (Names.constUndef qid))
                                         ^ ".")
                                     | SOME cid => cid)	
	in
	  [cid]
	end
      | transWorld (D.Plus (W1, W2)) = transWorld W1 @ transWorld W2
      | transWorld (D.Concat (W1, W2)) = transWorld W1 @ transWorld W2
      | transWorld (D.Times W) = transWorld W

    fun transFor' (Psi, D) = 
        let
	  val G = I.Decl (I.Null, D)
	  val ReconTerm.JWithCtx (I.Decl (I.Null, D'), ReconTerm.JNothing) = 
	    ReconTerm.reconWithCtx (Psi, ReconTerm.jwithctx(G, ReconTerm.jnothing))
	in D'
	end

    (* transFor (ExtDctx, ExtF) = (Psi, F)
     
       Invariant:
       If   |- ExtDPsi extdecctx
       and  |- ExtF extfor
       then |- Psi <= ExtDPsi
       and  Psi |- F <= ExtF
    *)  
    fun transFor (Psi, D.True) = T.True
      | transFor (Psi, D.And (EF1, EF2)) = 
          T.And (transFor (Psi, EF1), transFor (Psi, EF2))
      | transFor (Psi, D.Forall (D, F)) =
        let 
	  val (D'', nil) = transDec D
	  val D' = transFor' (Psi, stringTodec (D''))
	in
	   T.All ((T.UDec D', T.Explicit), transFor (I.Decl (Psi, D'), F))
        end
      | transFor (Psi, D.Exists (D, F)) =
        let 
	  val (D'', nil) = transDec D
	  val D' = transFor' (Psi, stringTodec (D''))
	in
	   T.Ex ((D', T.Explicit), transFor (I.Decl (Psi, D'), F))
        end
      | transFor (Psi, D.ForallOmitted (D, F)) =
        let 
	  val (D'', nil) = transDec D
	  val D' = transFor' (Psi, stringTodec (D''))
	in
	   T.All ((T.UDec D', T.Implicit), transFor (I.Decl (Psi, D'), F))
        end
      | transFor (Psi, D.ExistsOmitted (D, F)) =
        let 
	  val (D'', nil) = transDec D
	  val D' = transFor' (Psi, stringTodec (D''))
	in
	   T.Ex ((D', T.Implicit), transFor (I.Decl (Psi, D'), F))
        end
      | transFor (Psi, D.World (W, EF)) = 
	   T.World (T.Worlds (transWorld W), transFor (Psi, EF))
	   





    (* stringToTerm s = U

       Invariant:
       If   s is a string representing an expression,
       then U is the result of parsing it
       otherwise Parsing.error is raised.
    *)
    fun stringToterm s = 
        let 
          val f = LS.expose (L.lexStream (TextIO.openString s))
	  val (t, f') = ParseTerm.parseTerm' f
	  val r2 = checkEOF f'
        in
	  t
        end




    (* head (dH) = n

       Invariant:
       n is the name of the function head dH
    *)
    fun head (D.Head s) = s
      | head (D.AppLF (H, _)) = head H
      | head (D.AppMeta (H, _)) = head H

    (* lamClosure (F, P) = P'

       Invariant:
       If   . |- F formula
       and  . |- F = all D1. ... all Dn. F' formula 
	 for  . |- F' formula that does not commence with a universal quantifier
       and . |- P :: F' 
       then P' = lam D1 ... lam Dn P
    *)
    fun lamClosure (T.All ((D, _), F), P) = T.Lam (D, lamClosure (F, P))
      | lamClosure (_, P) = P


    fun exists (c, []) = raise Error "Current world is not subsumed"
      | exists (c, c' :: cids) = if c = c' then () else exists (c, cids)

    fun subsumed ([], cids') = ()
      | subsumed (c :: cids, cids') = (exists (c, cids'); subsumed (cids, cids'))


    fun checkForWorld (T.World (W as T.Worlds cids, F), t', T.Worlds cids') = 
        let 
  	  val _ =  subsumed (cids', cids)
	(* check that W is at least as large as W' *)
	in 
	  (F, t', W) 
	end
      | checkForWorld FtW = FtW



    (* append (Psi1, Psi2) = Psi3
     
       Invariant:
       If   |- Psi1 ctx
       and  |- Psi2 ctx
       then |- Psi3 = Psi1, Psi2 ctx
    *)
    fun append (Psi, I.Null) = Psi
      | append (Psi, I.Decl (Psi', T.UDec (I.Dec (_, V)))) =
          I.Decl (append (Psi, Psi'), T.UDec (I.Dec (NONE, V)))
      


    fun parseTerm ((Psi, env), (s, V)) =
        let 
	  val (term', c) = transTerm s
	  val term = stringToterm (term')
	  val ReconTerm.JOf ((U, occ), (_, _), L) =
	    ReconTerm.reconWithCtx (T.coerceCtx Psi, ReconTerm.jof' (term, V))
	in
	  U
	end

    fun parseDec ((Psi, env), s) =
        let 
	  val (dec', c) = transDec s
	  val dec = stringTodec (dec')
	  val ReconTerm.JWithCtx (I.Decl(I.Null, D), ReconTerm.JNothing) =
	    ReconTerm.reconWithCtx (T.coerceCtx Psi, ReconTerm.jwithctx (I.Decl(I.Null, dec), ReconTerm.jnothing))
	in
	  D
	end



    (* transDecs ((Psi, env), dDs, sc, W) = x
       
       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  W is the valid world
       and  sc is the success continuation that expects
	    as input: (Psi', env') 
	              where Psi' is the context after translating dDs
		      and   Psi' |- env' environment
			    are all variables introduced until this point
	    as output: anything. 
       then eventually x = ().     --cs
    *)

    fun transDecs ((Psi, env), _, D.Empty, sc, W) = (sc (Psi, env, W))
      | transDecs ((Psi, env), SOME condec, D as D.FunDecl (FunD, Ds), sc, W) =  (transFun1 ((Psi, env), condec, D, sc, W)) 
      | transDecs ((Psi, env), NONE, D.FormDecl (FormD, Ds), sc, W) = (transForDec ((Psi, env), FormD, Ds, sc, W))
      | transDecs ((Psi, env), NONE, D.ValDecl (ValD, Ds), sc, W) = (transValDec ((Psi, env), ValD, Ds, sc, W))
      | transDecs _ = raise Error "Constant declaration must be followed by a constant definition"

    and transHead (D.Head s, args) = transHead' ((T.lemmaFor (T.lemmaName s), T.id), args)
      | transHead (D.AppLF (h, t), args) = transHead (h, t::args)

    and transHead' ((T.World (_, F), s), args) = transHead' ((F, s), args) 
      | transHead' ((T.All ((T.UDec (I.Dec (_, V)), T.Implicit), F'), s), args) =
	  transHead' ((F', T.Dot (T.Exp (I.EVar (ref NONE, I.Null, I.EClo (V, T.coerceSub s), ref nil)), s)), args)
      | transHead' ((T.All ((T.UDec (I.Dec (_, V)), T.Explicit), F'), s), t :: args) =
	let
	  val (term', c) = transTerm t
	  val term = stringToterm (term')
	  val ReconTerm.JOf ((U, occ), (_, _), L) =
	    ReconTerm.reconWithCtx (I.Null, ReconTerm.jof' (term, I.EClo (V, T.coerceSub s)))
	in
	  transHead' ((F', T.Dot (T.Exp U, s)), args)
	end
      | transHead' ((F, s), nil) = (F, s)

    and transPattern (p, (T.Ex ((I.Dec (_, V), T.Implicit), F'), s)) =
	  transPattern (p, (F', T.Dot (T.Exp (I.EVar (ref NONE, I.Null, I.EClo (V, T.coerceSub s), ref nil)), s)))
      | transPattern (D.PatInx (t, p), (T.Ex ((I.Dec (_, V), T.Explicit), F'), s)) =
	let
	  val (term', c) = transTerm t
	  val term = stringToterm (term')
	  val ReconTerm.JOf ((U, occ), (_, _), L) =
	    ReconTerm.reconWithCtx (I.Null, ReconTerm.jof' (term, I.EClo (V, T.coerceSub s)))
	in
	  T.PairExp (U, transPattern (p, (F', T.Dot (T.Exp U, s))))
	end
      | transPattern (D.PatUnit, (F, s)) = T.Unit    
					(* other cases should be impossible by invariant
					 F should be F.True
					 --cs Sun Mar 23 10:38:57 2003 *)


    (* transFun1 ((Psi, env), dDs, sc, W) = x
       
       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  the top declaration is a function declaration 
       and  W is the valid world
       and  sc is the success continuation that expects
	    as input: (Psi', env') 
	              where Psi' is the context after translating dDs
		      and   Psi' |- env' environment
			    are all variables introduced until this point
	    as output: anything.  
       then eventually x = ().     --cs
    *)
    and transFun1 ((Psi, env), D, D.FunDecl (D.Fun (eH, eP), Ds), sc, W) =
        let
	  val s = head eH
	  val _ = print ("\n[fun " ^ s ^ " ")
	  val Psi' = I.Decl (Psi, D)
	  val env' = map (fn (U, V, name) => (I.EClo (U, I.Shift 1), I.EClo (V, I.Shift 1), name)) env
  	in
	  transFun2 ((Psi', env'), s, D.FunDecl (D.Bar (eH, eP), Ds), sc, fn Cs => T.Case (T.Cases Cs), W)
	end
      | transFun1 _ = raise Error "Function declaration expected"


    (* transFun2 ((Psi, env), s, dDs, sc, k, W) = x
       
       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  s is the name of the function currently being translated
       and  the top declaration is a function declaration 
       and  the top declaration is a function declaration 
       and  W is the valid world
       and  sc is the success continuation that expects
	    as input: (Psi', env') 
	              where Psi' is the context after translating dDs
		      and   Psi' |- env' environment
			    are all variables introduced until this point
	    as output: anything.  
       and  k is the continuation that expects
	    as input: Cs a list of cases
	    as ouput: A program P that corresponds to the case list Cs
       then eventually x = ().     --cs
    *)
    and transFun2   ((Psi, env), s, D.FunDecl (D.Bar (eH, eP), Ds), sc, k, W) =
          transFun3 ((Psi, env), s, eH, eP, Ds, sc,  k, W)
      | transFun2   ((Psi, env), s, Ds, sc, k, W) =
	  let 
       	    val _ = print "]\n"
	    val F = T.lemmaFor (T.lemmaName s)
	    val P = transDecs  ((Psi, env), NONE, Ds, sc, W)
	    val D = T.PDec (SOME s, F)
	    val P' = lamClosure (F, k nil)
	  in
	    T.Let (D, P', P)
	  end

    (* transFun3 ((Psi, env), s, eH, eP, Ds, sc, k, W) = x
       
       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  s is the name of the function currently being translated
       and  eH is the head of the function
       and  eP its body
       and  W is the valid world
       and  Ds are the remaining declarations
       and  sc is the success continuation that expects
	    as input: (Psi', env') 
	              where Psi' is the context after translating dDs
		      and   Psi' |- env' environment
			    are all variables introduced until this point
	    as output: anything.  
       and  k is the continuation that expects
	    as input: Cs a list of cases
	    as ouput: A program P that corresponds to the case list Cs
       then eventually x = ().     --cs
    *)
    and transFun3 ((Psi, env), s, eH, eP, Ds, sc, k, W) =
        let 
	  val _ = print "[case ..."
	  val _ = if (head eH) <> s
		  then raise Error "Functions don't all have the same name"
		  else ()
          val _ = Names.varReset (I.Null)
	  val (F, t) = transHead (eH, nil)
	  val _ = print "+"
(*      	  val F' = Normalize.normalizeFor (F, t) *)
	  val (Psi', t') = Abstract.abstractTomegaSub t
	  val m = I.ctxLength Psi'
	  val _ = print (Int.toString m)
	  val env''  =  map (fn (U, V, name) => (I.EClo (U, I.Shift m), I.EClo (V, I.Shift m), name)) env
	  val Psi'' = append (Psi, Psi')
(*	  val _ = print (TomegaPrint.forToString (Names.ctxName (T.coerceCtx Psi''), myF) ^ "\n") *)
	  val P = transProgI ((Psi'', env''), eP, (F, t'), W)
	  val _ = print "]"
	in
	  transFun2 ((Psi, env), s, Ds, sc, fn Cs => k ((Psi'', t', P) :: Cs), W)
	end

    (* transForDec ((Psi, env), eDf, dDs, sc, W) = x
       
       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  Psi |- eDf is a theorem declaration.
       and  W is the valid world
       and  dDs are the remaining declarations
       and  sc is the success continuation that expects
	    as input: (Psi', env') 
	              where Psi' is the context after translating dDs
		      and   Psi' |- env' environment
			    are all variables introduced until this point
	    as output: anything.  
       then eventually x = ().     --cs
    *)
    and transForDec ((Psi, env), D.Form (s, eF), Ds, sc, W) = 
        let

	  val G = Names.ctxName (T.coerceCtx Psi)
	  val F = transFor (G, eF)   
	  val F' = Normalize.normalizeFor (F, T.id)
	  val _ = print s
	  val _ = print " :: "
	  val _ = print (TomegaPrint.forToString (T.embedCtx G, F') ^ "\n") 
	  val _ = TomegaTypeCheck.checkFor (Psi, F')
	in
	  (T.lemmaAdd (T.ForDec (s, F'));
           T.lemmaFor (T.lemmaName s); 
	   transDecs ((Psi, env), SOME (T.PDec (SOME s, F')), Ds, sc, W))
 	end


    (* transValDec ((Psi, env), dDv, dDs, sc, W) = x
       
       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  Psi |- dDv value declaration
       and  W is the valid world
       and  dDs are the remaining declarations
       and  sc is the success continuation that expects
	    as input: (Psi', env') 
	              where Psi' is the context after translating dDs
		      and   Psi' |- env' environment
			    are all variables introduced until this point
	    as output: anything.  
       then eventually x = ().     --cs
    *)
    and transValDec ((Psi, env), D.Val (EPat, eP, eFopt), Ds, sc, W) =
        let 

	  val _ = print "[val ..."
          val (P, (F', t')) = (case eFopt 
	                         of NONE => transProgS ((Psi, env), eP, W, nil)
			          | SOME eF => let
						 val F' = transFor (T.coerceCtx Psi, eF)
						 val P' =  transProgIN ((Psi, env), eP, F', W)
					       in
						 (P', (F', T.id))
					       end)

	  val F'' = Normalize.normalizeFor (F', t')
	  val Pat = transPattern (EPat, (F', t'))
      	  val D = T.PDec (NONE, F'')
	  val (Psi', Pat') = Abstract.abstractTomegaPrg (Pat)
	  val m = I.ctxLength Psi'
	  val t = T.Dot (T.Prg Pat', T.id)
	  val env''  = map (fn (U, V, name) => (I.EClo (U, I.Shift m), I.EClo (V, I.Shift m), name)) env
	  val Psi'' = append (Psi, Psi')
          val P'' = transDecs ((Psi'', env''), NONE, Ds, sc, W)
	in
	  T.Let (D, P, T.Case (T.Cases [ (* (Psi'', t', P'') *)])) 
	end



    (* transProgS ((Psi, env), ExtP, F, W) = P 
       transProgI ((Psi, env), ExtP, W) = (P, F)
       Invariant:
       If   ExtP contains free variables among (Psi, env)
       and  ExtP is a program defined in (Psi, env)
       and  W is a world
       and  Exists Psi |- F : formula
       then Psi |- P :: F
    *)
    and transProgI ((Psi, env), eP, Ft, W) =
          transProgIN ((Psi, env), eP, Normalize.normalizeFor Ft, W)

    and transProgIN ((Psi, env), D.Unit, T.True, W) = T.Unit
      | transProgIN ((Psi, env), P as D.Inx (s, EP), T.Ex ((I.Dec (_, V), T.Explicit), F'), W) =
        let 
	  val U = parseTerm ((Psi, env), (s, V))
	  val P' = transProgI ((Psi, env), EP, (F', T.Dot (T.Exp U, T.id)), W)
        in
          T.PairExp (U, P')
        end
      | transProgIN ((Psi, env), D.Let (eDs, eP), F, W) =
          transDecs ((Psi, env), NONE, eDs, fn (Psi', env', W') => 
		     transProgI ((Psi', env'), eP, (F, T.Shift (I.ctxLength Psi' - I.ctxLength Psi)),W'), W)
      | transProgIN ((Psi, env), D.Choose (eD, eP), F, W) =
	  let 
	    val D' = parseDec ((Psi, env), eD)
	    val env''  = map (fn (U, V, name) => (I.EClo (U, I.Shift 1), I.EClo (V, I.Shift 1), name)) env
	    val Psi'' = I.Decl (Psi, T.UDec D')
	  in
	    T.Choose (T.Lam (T.UDec D', transProgI ((Psi'', env''), eP, (F, T.Shift 1), W)))
	    end
      | transProgIN ((Psi, env), D.New (eD, eP), F, W) =
	  let 
	    val D' = parseDec ((Psi, env), eD)
	    val env''  = map (fn (U, V, name) => (I.EClo (U, I.Shift 1), I.EClo (V, I.Shift 1), name)) env
	    val Psi'' = I.Decl (Psi, T.UDec D')
	  in
	    T.New (T.Lam (T.UDec D', transProgI ((Psi'', env''), eP, (F, T.Shift 1), W)))
	  end
      | transProgIN ((Psi, env), P as D.AppTerm (EP, s), F, W) =
        let
	  val (P', (F', _)) = transProgS ((Psi, env), P, W, nil)
	  val ()  = ()   (* check that F == F' *)
        in
          P'
        end  	


(*      | transProgIN ((Psi, env), D.Pair (EP1, EP2), T.And (F1, F2), W) =
        let 
	  val P1 = transProgIN ((Psi, env), EP1, F1, W)
	  val P2 = transProgIN ((Psi, env), EP2, F2, W)	
	in
          T.PairPrg (P1, P2)
	end
      | transProgIN ((Psi, env), P as D.AppProg (EP1, EP2), F, W) =
	let
	  val (P', (F', _)) = transProgS ((Psi, env), P, W)
	  val ()  = ()   (* check that F == F' *)
	in
	  P'
	end  
      | transProgIN ((Psi, env), P as D.AppTerm (EP, s), F, W) =
        let
	  val (P', (F', _)) = transProgS ((Psi, env), P, W)
	  val ()  = ()   (* check that F == F' *)
        in
          P'
        end  
      | transProgIN ((Psi, env), P as D.Inx (s, EP), T.Ex (I.Dec (_, V), F'), W) =
        let 
	  val (U, V) = parseTerm ((Psi, env), s)
	  val P' = transProgI ((Psi, env), EP, (F', T.Dot (T.Exp U, T.id)), W)
        in
          T.PairExp (U, P')
        end
      | transProgIN ((Psi, env), D.Const name, F, W) =
	let
	  val lemma = T.lemmaName name
	  val F' = T.lemmaFor lemma
	  val () = ()    (* check that F == F' *)
	in
	  T.Root (T.Const lemma, T.Nil)
	end

(*      | transProgIN (Psi, D.Lam (s, EP)) =
        let 
	  val dec = stringTodec s
          val (I.Decl (Psi, (D, _, _)), P, F') = transProgI (I.Decl (ePsi, dec), EP)
        in 
          (Psi, T.Lam (T.UDec D, P), T.All (D, F'))
        end
*)


      | transProgIN ((Psi, env), D.New (s, EP), F, W) =
          let
            val G = Names.ctxName (T.coerceCtx Psi)
            val _ = print (Print.ctxToString (I.Null, G) ^ "\n")
            val (U, V) = parseTerm ((Psi, env), s ^ " type")
            val _ = print (Print.expToString (G, U) ^ "\n")
 
          fun extract (G, Us) = extractW (G, Whnf.whnf Us)
          and extractW (G, (I.Pi ((D as I.Dec (_, _), _), V'), s)) =
                extract (I.Decl(G, I.decSub (D, s)), (V', I.dot1 s))
            | extractW (G, _) = G

          val G' = extract (I.Null, (U, I.id))
          val Dlist = T.ctxToBDecs (T.coerceCtx Psi, G', W)

          fun project ((G, env), []) = (env, 1)   (* is this the right starting point --cs *)
            | project ((G, env), x :: N) =
              let
                val (env', k) = project ((G, env), N)
                val U = I.Root (I.Proj (I.Bidx 1, k), I.Nil)
                val V =  TypeCheck.infer' (G, U)
              in
                ((U, V, x) :: env', k+1)
              end

          fun extend ((Psi', env'), []) = (Psi', env')
            | extend ((Psi', env'), (N, D) :: Dlist') =
              let
                val (Psi'', env'') = extend ((Psi', env'),  Dlist')
                val Psi''' = I.Decl (Psi'', T.UDec D)
                val I.BDec (_, (cid, s)) = D
                val G''' = T.coerceCtx Psi'''
                val env''' = map (fn (U, V, name) => (I.EClo (U, I.shift), I.EClo (V, I.shift), name)) env''
                val (env'''', _) = project ((G''', env'''), N)
              in
                (Psi''',  env'''')
               end

           val (Psi', env') = extend ((Psi, env), Dlist)
           val _ = printCtx (Names.ctxName (T.coerceCtx Psi'), env')

          fun universalClosure ([], F) = F
            | universalClosure ((_, D) :: Ds, F)  = T.All (T.UDec D, universalClosure (Ds, F))

          val (P', (F, t)) = transProgS ((Psi, env), EP, W)

          in
            T.Unit 
          end

*)
   and transProgS ((Psi, env), D.Unit, W, args) =
         (T.Unit, (T.True, T.id))
     | transProgS ((Psi, env), D.AppTerm (EP, s), W, args) =
	 transProgS ((Psi, env), EP, W, s :: args)
     | transProgS ((Psi, env), D.Const name, W, args) = 
	 let
	   val lemma = T.lemmaName name
	   val F = T.lemmaFor lemma
	   val (S, Fs') = transProgS'  ((Psi, env), (F, T.id), W, args)
	 in
	   (T.Root (T.Const lemma, S), Fs')
	 end
	    
(*      | transProgS ((Psi, env), D.AppTerm (EP, s), W) =
        let
          val (P', (T.All ((T.UDec (I.Dec (_, V)), _), F'), t)) = transProgS ((Psi, env), EP, W)
	  val U = parseTerm ((Psi, env), (s, V))
	  val (F'', t'', _) = checkForWorld (F', T.Dot (T.Exp U, t), W)
        in
          (T.Redex (P', T.AppExp (U, T.Nil)),  (F'', t''))
        end
      | transProgS ((Psi, env), D.Const name, W) =
	let
	  val lemma = T.lemmaName name
	  val (F, t, _) = checkForWorld (T.lemmaFor lemma, T.id, W)
	in
	  (T.Root (T.Const lemma, T.Nil), (F, t))
	end

*)

    and transProgS' ((Psi, env), (T.World (_, F), s), W, args) = transProgS' ((Psi, env), (F, s), W, args) 
      | transProgS' ((Psi, env), (T.All ((T.UDec (I.Dec (_, V)), T.Implicit), F'), s), W, args) =
        let
	  val G = T.coerceCtx Psi
	  val X = I.newEVar (G, I.EClo (V, T.coerceSub s))
(*	  val X = I.EVar (ref NONE, I.Null, I.EClo (V, T.coerceSub s), ref nil) *)
          val (S, Fs') = transProgS' ((Psi, env), (F', T.Dot (T.Exp X, s)), W, args)
	in
	  (T.AppExp (Whnf.normalize (X, I.id), S), Fs')
	end
      | transProgS' ((Psi, env), (T.All ((T.UDec (I.Dec (_, V)), T.Explicit), F'), s), W, t :: args) =
	let
	  val U = parseTerm ((Psi, env), (t, I.EClo (V, T.coerceSub s)))
	  val (S, Fs') = transProgS' ((Psi, env), (F', T.Dot (T.Exp U, s)), W, args)
(*	  val (F'', s'', _) = checkForWorld (F', T.Dot (T.Exp U, s), W) *)
	in
          (T.AppExp (U, S), Fs')
	end
      | transProgS' ((Psi, env), (F, s), _,nil) = (T.Nil, (F, s))


(*
     | transProgS ((Psi, env), D.Pair (EP1, EP2), W) =
        let 
          val (P1, (F1, t1)) = transProgS ((Psi, env), EP1, W)
          val (P2, (F2, t2)) = transProgS ((Psi, env), EP2, W)
	in
          (T.PairPrg (P1, P2), (T.And (F1, F2), T.comp (t1, t2)))
	end

     | transProgS ((Psi, env), D.AppProg (EP1, EP2), W) =
	let
	  val (P1, (T.And (F1, F2), t)) = transProgS ((Psi, env), EP1, W)
	  val P2 = transProgIN ((Psi, env), EP2, T.FClo (F1, t), W)
	  val (F'', t'', W) = checkForWorld (F2, t, W)
	in
	  (T.Redex (P1, T.AppPrg (P2, T.Nil)), (F'', t''))
	end  


      | transProgS ((Psi, env), P as D.Inx (s, EP), W) =  raise Error "Cannot infer existential types"

(*      | transProgS ((Psi, env), D.Lam (s, EP), W) =
        let 
	  val dec = stringTodec s
          val (I.Decl (Psi', (D, _, _)), P, F) = transProgI (I.Decl (Psi, dec), EP)
          val (F', t', _) = checkForWorld (F, T.id, W)
        in 
          (T.Lam (T.UDec D, P), (T.All (D, F'), t'))
        end
*)
      | transProgS ((Psi, env), D.New (s, eP), W)  = 
	let
     	  val _ = print "["
	  val G = Names.ctxName (T.coerceCtx Psi) 
          val _ = print (Print.ctxToString (I.Null, G) ^ "\n") 
          val (U, V) = parseTerm ((Psi, env), s ^ " type")
(*        val _ = print (Print.expToString (G, U) ^ "\n") *)

          fun extract (G, Us) = extractW (G, Whnf.whnf Us)
          and extractW (G, (I.Pi ((D as I.Dec (_, _), _), V'), s)) =
                extract (I.Decl(G, I.decSub (D, s)), (V', I.dot1 s))
            | extractW (G, _) = G

          val G' = extract (I.Null, (U, I.id))
          val Dlist = T.ctxToBDecs (T.coerceCtx Psi, G', W)

          fun project ((G, env), []) = (env, 1)   (* is this the right starting point --cs *)
            | project ((G, env), x :: N) =
              let
                val (env', k) = project ((G, env), N)
                val U = I.Root (I.Proj (I.Bidx 1, k), I.Nil)
                val V =  TypeCheck.infer' (G, U)
              in
                ((U, V, x) :: env', k+1)
              end
                 
          fun extend ((Psi', env'), []) = (Psi', env')
            | extend ((Psi', env'), (N, D) :: Dlist') =
              let
                val (Psi'', env'') = extend ((Psi', env'),  Dlist')
                val Psi''' = I.Decl (Psi'', T.UDec D)
                val I.BDec (_, (cid, s)) = D
                val G''' = T.coerceCtx Psi'''
                val env''' = map (fn (U, V, name) => 
                    (I.EClo (U, I.shift), I.EClo (V, I.shift), name)) env''
                val (env'''', _) = project ((G''', env'''), N)
              in
                (Psi''',  env'''')
               end

          val (Psi', env') = extend ((Psi, env), Dlist)
          val _ = printCtx (Names.ctxName (T.coerceCtx Psi'), env')

          fun universalClosure ([], F) = F
            | universalClosure ((_, D) :: Ds, F)  = T.All (T.UDec D, universalClosure (Ds, F))

          val (P', (F, t)) = transProgS ((Psi, env), eP, W)
          val F' = Normalize.normalizeFor (F, t)
          val F'' = universalClosure (Dlist, F')
          val P'' = lamClosure (F'', P')
        in
          (P'', (F'', T.id))
        end
*)
  in 
    val transFor = fn F => let val  F' = transFor (I.Null, F) in F' end

(*    val makePattern = makePattern *)
(*    val transPro = fn P => let val (P', _) = transProgS ((I.Null, []), P, T.Worlds []) in P' end *)

    val transDecs = fn Ds => transDecs ((I.Null, []), NONE, Ds, fn (Psi, env, W) => T.Unit, T.Worlds []) 

  end 
end (* functor Trans *)
