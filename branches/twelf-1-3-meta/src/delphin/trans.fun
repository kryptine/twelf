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
          transTerm (t1) ^ " -> " ^ transTerm (t2) 
      | transTerm (D.Ltarrow (t1, t2)) = 
	  transTerm (t1) ^ " <- " ^ transTerm (t2)
      | transTerm (D.Type) = "type"
      | transTerm (D.Id s) = s
      | transTerm (D.Pi (D, t)) = 
	  "{" ^ transDec D ^ "}" ^ transTerm (t) 
      | transTerm (D.Fn (D, t)) =
	  "[" ^ transDec D ^ "]" ^ transTerm (t)
      | transTerm (D.App (t1, t2)) =
	  transTerm t1 ^ " " ^ transTerm t2
      | transTerm (D.Omit) = "_"
      | transTerm (D.Paren (t)) = 
	  "(" ^ transTerm t ^ ")"
	  
    and transDec (D.Dec (s, t)) = s ^ ":" ^ (transTerm t)

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
	  val D' = transFor' (Psi, stringTodec (transDec D))
	in
	   T.All ((T.UDec D', T.Explicit), transFor (I.Decl (Psi, D'), F))
        end
      | transFor (Psi, D.Exists (D, F)) =
        let 
	  val D' = transFor' (Psi, stringTodec (transDec D))
	in
	   T.Ex ((D', T.Explicit), transFor (I.Decl (Psi, D'), F))
        end
      | transFor (Psi, D.ForallOmitted (D, F)) =
        let 
	  val D' = transFor' (Psi, stringTodec (transDec D))
	in
	   T.All ((T.UDec D', T.Implicit), transFor (I.Decl (Psi, D'), F))
        end
      | transFor (Psi, D.ExistsOmitted (D, F)) =
        let 
	  val D' = transFor' (Psi, stringTodec (transDec D))
	in
	   T.Ex ((D', T.Implicit), transFor (I.Decl (Psi, D'), F))
        end
      | transFor (Psi, D.World (W, EF)) = 
	   T.World (T.Worlds (transWorld W), transFor (Psi, EF))
	   



(*

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


    (* weaken (G, a) = w'

       Invariant:
       If   a is a type family
       then G |- w' : G'
       and  forall x:A in G'  A subordinate to a
     *)
    fun weaken (I.Null, a) = I.id
      | weaken (I.Decl (G', D as I.Dec (name, V)), a) =
	let
	  val w' = weaken (G', a)
	in
	  if Subordinate.belowEq (I.targetFam V, a) then I.dot1 w'
	  else I.comp (w', I.shift)
	end

    fun listToCtx (G, [], s) = G
      | listToCtx (G, D :: L', s) = 
          listToCtx (I.Decl (G, I.decSub (D, s)), L', I.dot1 s)

    fun raiseDec (l, s, D as I.Dec (x, V)) =
        let 
	  val (_, L) = I.constBlock l
	  val G = listToCtx (I.Null, L, s)
	  val a = I.targetFam V
	  val w = weaken (G, a)
	  val iw = Whnf.invert w 	          (* G' |- iw : G     *)
	  val G' = Whnf.strengthen (iw, G)
	  val V' = Abstract.raiseType (G', V)
	in
	  I.Dec (x, V')
	end

    fun push (D0 as T.UDec (I.BDec (_, (l, s))) , T.All (T.UDec (D as I.Dec (_, V)), F)) =  
        let 
	  val D' = raiseDec (l, s, D)
	in
	  T.All (T.UDec D', T.All (D0, F))
	end
      | push (D0 as T.UDec (I.BDec (_, (l, s))) , T.Ex (D as I.Dec (_, V), F)) =  
        let 
	  val D' = raiseDec (l, s, D)
	in
	  T.Ex (D', T.All (D0, F))
	end
      | push (D0, T.World (W, F)) = 
	  T.World (W, push (D0, F))
      | push (D0, T.True) = (print "-"; T.True)



    (* collectPattern *)
    (* make (Psi, Pat, (F, t)) = P

       Invariant:
       If   |- Psi ctx
       and  Psi |- F[s] formula
       and  Psi'' |- Pat :: F[t] pattern
       then Psi'  |- P == Pat :: F[s]
    *)
    fun makePattern  (DPat, Ft) = 
        let
	  val _ = print "|"
	  val F' = Normalize.normalizeFor Ft
	in
	  makePatternN (DPat, F')
	end
    and makePatternN (D.PatInx (D.Term s, Pat), F' as T.Ex (I.Dec (_, V), F)) = 
        let 
val _ = print "+"
	  val t = stringToterm (s)
val _ = print "NEXT LINE is the problem"
	  val (U, L) = TpRecon.termToPattern ((t, V), Paths.Loc ("", Paths.Reg (1,1))) 
	               (* fix location information *)
val _ = print "+"
	  val Pat' = makePattern (Pat, (F, T.Dot (T.Exp U, T.id)))
val _ = print "+"
        in
	  T.PairExp (U, Pat')
        end
      | makePatternN (D.PatPair (Pat1, Pat2), T.And (F1, F2)) =  
(print "^";
          T.PairPrg (makePatternN (Pat1, F1), makePatternN (Pat2, F2)))
      | makePatternN (D.PatVar (D.MDec (name, NONE)), F) =
(print "%";
          T.EVar (I.Null, ref NONE, F))
      | makePatternN (D.PatVar (D.MDec (name, SOME EF)), F) =
          let 
val _ = print "!";
            val (_, F') = transFor (I.Null, EF)  (* ? *)
	    val _ = ()  (* CHECK that F == F' *)
          in
            T.EVar (I.Null, ref NONE, F)
          end
      | makePatternN ( D.PatUnderscore, F) =
(print "@";
	  T.EVar (I.Null, ref NONE, F) )
      | makePatternN (D.PatUnit, T.True) = 
(print "&";
	  T.Unit)
      | makePatternN (DPat, T.All (D0 as T.UDec (I.BDec _), F)) =
(print "=";
	  makePatternN (DPat, push (D0, F)))

    (* collectPrg (K, P) = K'

       Invariant:
       If   K is a list of collected EVars
       and  P is a program (or a pattern)
            that contains all EVars in P
       then K' is also a list of collected EVars
       and  K' > K
    *)
    fun collectPrg (K, T.PairExp (M, P)) =
          collectPrg (Abstract.collectExp (K, M), P)
      | collectPrg (K, T.PairPrg (P1, P2)) =
	  collectPrg (collectPrg (K, P2), P1)
      | collectPrg (K, T.Root (H, S))= 
	  collectSpine (K, S)
      | collectPrg (K, T.Redex (P, S))= 
	  collectSpine (collectPrg (K, P), S)
      | collectPrg (K, T.EVar (_,_,_)) = K   
      | collectPrg (K, T.Unit) = K			

    (* collectSpine (K, S) = K'

       Invariant:
       If   K is a list of collected EVars
       and  S is a spine
       then K' is also a list of collected EVars 
            that contains all EVars in S
       and  K' > K
    *)
    and collectSpine (K, T.Nil) = K
      | collectSpine (K, T.AppExp (U, S)) = collectSpine (Abstract.collectExp (K, U), S) 


    (* collectSub (K, s) = K'

       Invariant:
       If   K is a list of collected EVars
       and  s is a substitution
       then K' is also a list of collected EVars 
            that contains all EVars in s
       and  K' > K
    *)
    fun collectSub (K, T.Shift _) = K 
      | collectSub (K, T.Dot (T.Exp U, t)) =
          collectSub (Abstract.collectExp (K, U), t)
      | collectSub (K, T.Dot (T.Prg P, t)) = 
	  collectSub (collectPrg (K, P), t)

 
    (* abstractPrg (K, P) = P'

       Invariant:
       If   K is a list of collected EVars
       and  P is a program
	    whose EVars are all contained in K
       then P' is a program that does not 
	    contain any EVars 
       and  {{K}} |- P' :: F for some formula F
    *)
    fun abstractPrg (K, T.PairExp (U, P)) =
          T.PairExp(Abstract.abstractExp (K, U), 
		    abstractPrg (K, P))
      | abstractPrg (K, T.PairPrg (P1, P2)) =
	  T.PairPrg(abstractPrg (K, P1), 
		    abstractPrg (K, P2))
      | abstractPrg (K, X as T.EVar (_,_,_)) = X
      | abstractPrg (K, T.Unit) = T.Unit
      | abstractPrg (K, T.Root (H, S)) = 
	  T.Root (abstractHead (K, H),
		  abstractSpine (K, S))
      | abstractPrg (K, T.Redex (P, S)) =
	  T.Redex (abstractPrg (K, P),
		   abstractSpine (K, S))
      | abstractPrg (K, T.Case O) = T.Case O  (* think about it *)
      | abstractPrg (K, T.Let (D, P1, P2)) =
	  T.Let (abstractDec (K, D), 
		 abstractPrg (K, P1),
		 abstractPrg (K, P2))

    (* abstractDec (K, D) = D'

       Invariant:
       If   K is a list of collected EVars
       and  D is a declaration
	    whose EVars are all contained in K
       then D' is a declaration that does not 
	    contain any EVars 
       and  {{K}} |- D valid 
    *)
    and abstractDec (K, D) = D

    (* abstractSpine (K, S) = S'

       Invariant:
       If   K is a list of collected EVars
       and  S is a spine
	    whose EVars are all contained in K
       then S' is a spine that does not 
	    contain any EVars 
       and  {{K}} |- S : V > V'   for some V, V'
    *)
    and abstractSpine (K, T.Nil) = T.Nil
      | abstractSpine (K, T.AppExp (U, S)) = 
          T.AppExp (Abstract.abstractExp (K, U), 
		    abstractSpine (K, S))
      | abstractSpine (K, T.AppPrg (P, S)) = 
	  T.AppPrg (abstractPrg (K, P),
		    abstractSpine (K, S))

    (* abstractHead (K, H) = H'

       Invariant:
       If   K is a list of collected EVars
       and  H is a head
	    whose EVars are all contained in K
       then H' is a head that does not 
	    contain any EVars 
       and  {{K}} |- H :: F  for some F
    *)
    and abstractHead (K, T.Const l) =  
          T.Const l
      | abstractHead (K, T.Var k) = 
	  T.Var k

    (* abstractSub (K, t) = t'

       Invariant:
       If   K is a list of collected EVars
       and  t is a substitution
	    whose EVars are all contained in K
       then t' is a substitution that does not 
	    contain any EVars 
       and  {{K}} |- t' :: Psi  for some context Psi
    *)
    and abstractSub (K, T.Shift 0) = T.Shift (Abstract.length K)
      | abstractSub (K, T.Dot (T.Exp U, t)) =
           T.Dot (T.Exp (Abstract.abstractExp (K, U)),
		  abstractSub (K, t))
      | abstractSub (K, T.Dot (T.Prg P, t)) =
           T.Dot (T.Prg (abstractPrg (K, P)),
		  abstractSub (K, t))

    (* abstractEnv (K, G) Xs env = env'

       Invariant:
       If   K is a collected list of free EVars
       and  G is the context that corresponds to K
       and  Xs is a list of EVars named by the user
       and  G |- env environment
       then G |- env' is an environment
       that contains all abstracted versions of Evars an X 
       and  it extends env
    *)
    fun abstractEnv (K, G) [] env = env
      | abstractEnv (K, G) ((U, name) :: Xs) env = 
        let 
	  val U' = Abstract.abstractExp (K, U)
	  val V' = TypeCheck.infer' (G, U')
	  val _ = TypeCheck.typeCheck (G, (U', V'))
	in
	  (U', V', name) :: abstractEnv (K, G) Xs env 
	end

    (* lookup n env = (U, V) 
  
       Invariant:
       env (n) : V
               = U 
    *)
    fun lookup n [] = raise Error "Free variable found"
      | lookup n ((U, V,  n') :: env) = 
        (if n=n' then (U, V) else lookup n env)

    (* isClosedSub (Psi, t) = ()
     
       Invariant:
       If   Psi |- t : Psi'
       and  Psi is closed
       then this function returns with ()
       otherwise, an exception is raised.
     *)
    fun isClosedSub (Psi, T.Shift _) = ()
      | isClosedSub (Psi, T.Dot (T.Exp U, t)) =
        if Abstract.closedExp (T.coerceCtx Psi, (U, I.id)) then isClosedSub (Psi, t)
	else raise Error "Sub: Could not infer all variables"

    fun isClosedPrg P =
        if Abstract.length (collectPrg (Abstract.nothing, P)) = 0 then ()
	else raise Error "Prg: Could not infer all variables"

    (* createEVarSub (Psi', Psi) = t

       Invariant:
       Psi' |- t : Psi
    *)
    and createEVarSub (Psi', I.Null) = T.Shift (I.ctxLength Psi')
      | createEVarSub (Psi', I.Decl (Psi, T.UDec (I.Dec (_, V)))) =  
	let 
	  val t = createEVarSub (Psi', Psi)
	  val V' = I.EClo (V, T.coerceSub t)
	  val X = I.newEVar (T.coerceCtx Psi', V')
	in
	  T.Dot (T.Exp X, t)
	end
      (* some other cases will be added later --cs *)

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
    fun lamClosure (T.All (D, F), P) = T.Lam (D, lamClosure (F, P))
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

    (* typeOfFun dH k = (F', t')

       Invariant:
       If   Psi |- dH U1 ... Un is a Head
       and  U1 ... Un are programs or LF objects
       and  k is continuation that expects 
	    as input: (F, t)  
	              where  Psi  |- t :: Psi'
		      and    Psi' |- F for
		      and    Psi  |- dH :: F [t]
	    as output (F', t') 
	              where  Psi  |- t' :: Psi''
		      and    Psi'' |- F' for
		      and    Psi  |- dH U1 ... Un :: F' [t']
       then
    *)
    fun typeOfFun (D.Head s, W) k = 
       k (checkForWorld (T.lemmaFor (T.lemmaName s), T.id, W)) 
  
      | typeOfFun (D.AppLF (EH, D.Term s), W) k = 
         
          typeOfFun (EH, W)
	     (fn 
                  (T.All (T.UDec (I.Dec (_, V)), F'), t, W') => (
  		      let 
                        val term = case (String.sub (s, 0)) of 
                                     #"#" => stringToterm (String.substring (s, 1, String.size(s)-1))
                                   |  _   => stringToterm s
              
                        val (U, L) = TpRecon.termToPattern ((term, I.EClo (V, T.coerceSub t)),
		 				       Paths.Loc ("", Paths.Reg (1,1)))
 	     
                        (* fix location information *)
                      in k (checkForWorld (F', T.Dot (T.Exp U, t), W')) 
                      end
		      )
		  | (T.FClo (F, t'), t, W') => (k (checkForWorld (F, T.comp (t', t), W'))) 
 	          | (T.Ex _, _, _) => raise Error "more arguments than expected"
	          | (T.True, _, _) => raise Error "more arguments than expected"
	          | (T.And _, _, _) => 
                        raise Error "Function type expected, Product type found"
                  | (_,_,_) => raise Error "\nmissing case\n") 

      (* some cases are missing  --cs *) 



    fun printSub (G, T.Shift k) = print ("^" ^ (Int.toString k) ^ ")")
      | printSub (G, T.Dot (T.Exp U, t)) = (print (Print.expToString (G, U)); print ", "; printSub (G, t))
      | printSub (G, T.Dot (T.Idx k, t)) =  (print (Int.toString k); printSub (G, t))
      | printSub (G, T.Dot (T.Prg P, t)) =  (print "Prg, "; printSub (G, t))
 
      
    fun printCtx (G, env) = 
      let 
	val _ = print "\n[Ctx/Env:\n"
	val _ = print (Print.ctxToString (I.Null, G));
	val _ = print "\n";
	val _ = map (fn (U, V, name) => print (name ^ "=" ^ Print.expToString (G, U) ^ ":" ^ Print.expToString (G, V) ^ "\n")) env
	val _ = print "]"
       in 
	 ()
       end
       


    (* append (Psi1, Psi2) = Psi3
     
       Invariant:
       If   |- Psi1 ctx
       and  |- Psi2 ctx
       then |- Psi3 = Psi1, Psi2 ctx
    *)
    fun append (Psi, I.Null) = Psi
      | append (Psi, I.Decl (Psi', T.UDec (I.Dec (_, V)))) =
          I.Decl (append (Psi, Psi'), T.UDec (I.Dec (NONE, V)))
      

    (* bridgeSub (n, m) = s
     
       Invariant:
       If   . |- Psi ctx
       and  . |- Psi' ctx
       and  n = | Psi |
       and  m = | Psi' |
       then Psi, Psi' |- s : Psi'
    *)
    fun bridgeSub (n, 0) = T.Shift n
      | bridgeSub (n, m) = T.dot1 (bridgeSub (n, m-1))


      
    fun makectx (I.Null, nil) = I.Null
      | makectx (I.Decl (Psi, T.UDec (I.Dec (_, V))), nil) = 
          I.Decl (makectx (Psi, nil), T.UDec (I.Dec (NONE, V)))
      | makectx (Psi, (U, V, name) :: env) = 
	  I.Decl (makectx (Psi, env), T.UDec (I.Dec (SOME name, I.EClo (V, I.Shift (length env)))))
		
    fun makestring (I.Null, s) = s
      | makestring (I.Decl (G, I.Dec (SOME n, V)), s) = 
          makestring (G,  "[" ^ n ^ ":" ^ Print.expToString (G, V) ^ "]" ^ s)
 

    fun makesub (Psi, []) = T.id
      | makesub (Psi, (U, V, name) :: env) = T.Dot (T.Exp U, makesub (Psi, env))

    fun strip (0, (U, V)) = (U, V)
      | strip (n, (I.Lam (_, U), I.Pi (_, V))) = strip (n-1, (U, V))

    fun parseTerm ((Psi, env), s) =
        let 
          val _ = print "#\n"
	  val _ = Names.varReset (I.Null)
	  val Psi' = makectx (Psi, env)
	  val s1 = makestring (Names.ctxName (T.coerceCtx Psi'), s)
          val term = stringToterm s1
	  val (_, U0, V0, occ) = TpRecon.termToExp (I.Null, term)
	  val (U1, V1) = strip (I.ctxLength Psi + length env, (U0, V0))
	  val t = makesub (Psi, env)
	in 
	  (I.EClo (U1, T.coerceSub t), I.EClo (V1, T.coerceSub t))
	end



    datatype Var 
      = Normal of string
      | Proj of string * string


*)
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

    fun transDecs ((Psi, env), D.Empty, sc, W) = (sc (Psi, env, W))
  (*    | transDecs ((Psi, env), D as D.FunDecl (FunD, Ds), sc, W) =  (transFun1 ((Psi, env), D, sc, W)) *)
      | transDecs ((Psi, env), D.FormDecl (FormD, Ds), sc, W) = (transForDec ((Psi, env), FormD, Ds, sc, W))
(*      | transDecs ((Psi, env), D.ValDecl (ValD, Ds), sc, W) = (transValDec ((Psi, env), ValD, Ds, sc, W)) *)

(*
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
    and transFun1 ((Psi, env), D.FunDecl (D.Fun (eH, eP), Ds), sc, W) =
        let
	  val s = head eH
	  val _ = print ("\n[fun " ^ s ^ " ")
          
  	in
	  transFun2 ((Psi, env), s, D.FunDecl (D.Bar (eH, eP), Ds), sc, fn Cs => T.Case (T.Cases Cs), W)
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
       	    val _ = print "]"
	    val F = T.lemmaFor (T.lemmaName s)
	    val P = transDecs  ((Psi, env), Ds, sc, W)
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
	  val _ = print "[case ...\n"
	  val _ = if (head eH) <> s
		  then raise Error "Functions don't all have the same name"
		  else ()
          val _ = Names.varReset (I.Null)

(*
          fun printHead h =
             case h of
               D.Head s => print ("Head " ^ s ^ "\n")
             | D.AppLF (h', t) => (print ("AppLF\n"); printHead h'; let val (D.Term t') = t in
                        print (t' ^ "\n") end)

          val _ = printHead eH
*)

   	  val (F, t, W') = typeOfFun (eH, W) (fn (F, t, W) => (F, t, W))

      	  val _ = Normalize.normalizeFor (F, t)
	  val K' = collectSub (Abstract.nothing, t)
	  val G' = Abstract.abstractCollected K'
	  val Psi' = T.embedCtx G'
	  val n = I.ctxLength Psi
	  val m = I.ctxLength Psi'


	  val t' = abstractSub (K', t)
	  val env'  =  map (fn (U, V, name) => (I.EClo (U, I.Shift m), I.EClo (V, I.Shift m), name)) env
	  val env'' = abstractEnv (K', G') (Names.namedEVars ()) env'
	  val Psi'' = append (Psi, Psi')

(* Operation add parameter variables begin *)
 	  val _ = print "\n++++\n"


          fun extractLabel ([]) = ([], [])
            | extractLabel (#"#"::s) = extractLabel s
            | extractLabel (x::s) =
              if x = #"_" then ([], s)
              else 
                let 
                  val (s1, s2) = extractLabel s
                in 
                  (x :: s1, s2)
                end

	      
	  fun makeVar s = 
	    (case (extractLabel (String.explode s))
	       of (s1, []) => Normal (String.implode s1)
	        | (s1, s2) => Proj (String.implode s1, String.implode s2))

         
	  val Ns = Names.namedEVars ()

	  val _ = map (fn (_, x) => (case makeVar x 
		                       of Normal s  => print  ("Normal variable: " ^ s)
					| Proj (l, s) => print ("Projection from Block " ^ l ^ " at " ^ s)
					)) Ns

 	  val _ = print "\n++++"
(* Operation add parameter variables end *)

	  val myF = Normalize.normalizeFor (F, t')
	  val _ = print (TomegaPrint.forToString (Names.ctxName (T.coerceCtx Psi''), myF) ^ "\n") 
	  val P = transProgI ((Psi'', env''), eP, (F, t'), W')

	  val _ = print "]"
	in
	  transFun2 ((Psi, env), s, Ds, sc, fn Cs => k ((Psi'', t', P) :: Cs), W)
	end
*)
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
	  val F = transFor (I.Null, eF)   
					(* fix the context I.Null from
                                           external to internal form--cs *)
	  val G = Names.ctxName (T.coerceCtx Psi)
	  val _ = Normalize.normalizeFor (F, T.id)
	  val _ = print s
	  val _ = print " :: "
	  val _ = print (TomegaPrint.forToString (T.embedCtx G, F) ^ "\n") 
	in
	  (T.lemmaAdd (T.ForDec (s, F));
           T.lemmaFor (T.lemmaName s); 
	   transDecs ((Psi, env), Ds, sc, W))
 	end

(*
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

	  val _ = Names.varReset I.Null
    
          val (P, (F', t')) = (case eFopt 
	                         of NONE => transProgS ((Psi, env), eP, W)
			          | SOME eF => let 
				                 val (_, F') = transFor (I.Null, eF)   
						      (* rewrite the code for transFor, 
						         I.Null too restrictive
							 in its current form, this
							 offers only limited functionality --cs*)
						 val P' =  transProgIN ((Psi, env), eP, F', W)
					       in
						 (P', (F', T.id))
					       end)
   
          val _ = Names.varReset I.Null
	  val G = Names.ctxName (T.coerceCtx Psi)
	  val _ = printCtx (G, env) 
	  val F'' = Normalize.normalizeFor (F', t')
	  val _ = print (TomegaPrint.forToString (G, F'') ^ "\n") 
	  val _ = Names.varReset I.Null
	  val t0 = createEVarSub (I.Null, Psi)
	  val Pat = makePattern (EPat, (F'', t0))
	  val t = T.Dot (T.Prg Pat, t0)
	  val s0 = T.coerceSub t0
	  val K' = collectSub (Abstract.nothing, t)
	  val G' = Abstract.abstractCollected K'
(*	  val G'n = Names.ctxName G'*)
	  val Psi' = T.embedCtx G'
	  val t' = abstractSub (K', t)
(*	  val _ = printSub (G'n, t') *)
	  val env' = map (fn (U, V, name) => (Abstract.abstractExp (K', I.EClo (U, s0)), 
					      Abstract.abstractExp (K', I.EClo (V, s0)), 
						name)) env
(*	  val _ = printCtx (G'n, []) *)
	  val env'' = abstractEnv (K', G') (Names.namedEVars ()) env'
          val P'' = transDecs ((Psi', env''), Ds, sc, W)
      	  val D = T.PDec (NONE,  F'')
	  val _ = print "]"
	in
	  T.Let (D, P, T.Case (T.Cases [(Psi', t', P'')])) 
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
        let
	  val _= print "["
	  val _ = Normalize.normalizeFor Ft
	  val _= print "]"
	in	 
          transProgIN ((Psi, env), eP, Normalize.normalizeFor Ft, W)
	end



    and transProgIN ((Psi, env), D.Unit, T.True, W) = T.Unit
      | transProgIN ((Psi, env), D.Pair (EP1, EP2), T.And (F1, F2), W) =
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
      | transProgIN ((Psi, env), D.Let (eDs, eP), F, W) =
        let
          val D = T.PDec (SOME "temp", T.FVar (I.Null, ref NONE))
	in
          transDecs ((Psi, env), eDs, fn (Psi', env', W') => 
		     transProgI ((Psi', env'), eP, (F, T.Shift (I.ctxLength Psi' - I.ctxLength Psi)),W'), W)
        end
          (* T.Let (D, T.Empty, transProgIN ((Psi', env'), eP, F))  *)


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


   and transProgS ((Psi, env), D.Unit, W) =
          (T.Unit, (T.True, T.id))

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

      | transProgS ((Psi, env), D.AppTerm (EP, s), W) =
        let
          val (P', (T.All (T.UDec (I.Dec (_, V)), F'), t)) = transProgS ((Psi, env), EP, W)
	  val (U, V) = parseTerm ((Psi, env), s)
	  val (F'', t'', _) = checkForWorld (F', T.Dot (T.Exp U, t), W)
        in
          (T.Redex (P', T.AppExp (U, T.Nil)),  (F'', t''))
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
      | transProgS ((Psi, env), D.Const name, W) =
	let
	  val lemma = T.lemmaName name
	  val (F, t, _) = checkForWorld (T.lemmaFor lemma, T.id, W)
	in
	  (T.Root (T.Const lemma, T.Nil), (F, t))
	end

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

    val transDecs = fn Ds => transDecs ((I.Null, []), Ds, fn (Psi, env, W) => T.Unit, T.Worlds []) 

  end 
end (* functor Trans *)








