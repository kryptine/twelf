(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)


functor Opsem ( structure Whnf : WHNF
	       structure Abstract : ABSTRACT
	       structure Subordinate : SUBORDINATE
	       structure Normalize : NORMALIZE
	       structure TomegaTypeCheck : TOMEGATYPECHECK
	       structure TomegaPrint : TOMEGAPRINT
	       structure Converter : CONVERTER
	       structure Unify : UNIFY
		   ) : OPSEM = 

struct
  structure T = Tomega
  structure I = IntSyn
  structure S = Subordinate    
  structure A = Abstract

  exception Error of string



(*  local -- removed ABP 1/19/03 *)

  exception NoMatch
    
(* 
 matchPrg is used to see if two values can be 'unified' for
   purpose of matching case

 matchPrg (Psi, P1, P2) = ()

    Invariant:
    If P1 has no EVARs and P2 possibly does.
    and Psi  |- P1 :: F
    and Psi |- P1 value
    and Psi |- P2 :: F
    and Psi |- P2 value
     then if Psi |- P1 == P2 matchPrg terminates
       otherwise exception NoMatch is raised
*)
    fun matchPrg (Psi, P1, P2) = 
      matchVal (Psi, (P1, T.id), Normalize.normalizePrg (P2, T.id))
      (* ABP -- normalizePrg invariant does not state what happens to non-free EVArs,
       and there are some embedded under PClo... *)
	 
    and matchVal (Psi, (T.Unit, _), T.Unit) = ()

      | matchVal (Psi, (T.PairPrg (P1, P1'), t1), T.PairPrg (P2, P2')) = 
         (matchVal (Psi, (P1, t1), P2);
	  matchVal (Psi, (P1', t1), P2'))

      | matchVal (Psi, (T.PairBlock (B1, P1), t1), T.PairBlock (B2, P2)) = 
	 (matchVal (Psi, (P1, t1), P2);
	  Unify.unifyBlock (T.coerceCtx Psi, I.blockSub (B1, T.coerceSub t1), B2)
	  handle Unify.Unify _ => raise NoMatch)

      | matchVal (Psi, (T.PairExp (U1, P1), t1), T.PairExp (U2, P2)) = 
	 (matchVal (Psi, (P1, t1), P2); 
	  Unify.unify (T.coerceCtx Psi, (U1, T.coerceSub t1), (U2, I.id))
	  handle Unify.Unify _ => raise NoMatch)

      | matchVal (Psi, (T.PClo (P, t1'), t1), Pt) =  
	  matchVal (Psi, (P, T.comp (t1', t1)), Pt)

      (* Added by ABP *)
   
      | matchVal (Psi, (P',t1), T.PClo(T.PClo (P, t2), t3)) =  
	 (* ABP -- Do we need this? I added it *)
	 matchVal (Psi, (P',t1), T.PClo(P, T.comp (t2, t3)))

      | matchVal (Psi, (P',t1), T.PClo(T.EVar (_, r as ref NONE, _), t2)) =  
	 let
	   val iw = T.invertSub t2
	 in
	   (* ABP -- just make sure this is right *)
	   r := SOME (T.PClo (P', T.comp(t1, iw)))
	 end

      | matchVal (Psi, (P', t1), T.EVar (_, r as ref NONE, _)) =  
	 r := SOME (T.PClo (P', t1))

      | matchVal (Psi, (V,t), T.EVar ((D, r as ref (SOME P), F))) =  
	 (* ABP -- this should never occur, since we normalized it to start *)
	 matchVal (Psi, (V,t), P) 

     | matchVal _ = raise NoMatch


(* raisePrg is used in handling of NEW construct 
   raisePrg (G, P, F) = (P', F'))  

       Invariant:
       If   Psi, G |- P in F
       and  Psi |- G : blockctx
       then Psi |- P' in F'
       and  P = raise (G, P')   (using subordination)
       and  F = raise (G, F')   (using subordination)
*)
and raisePrg (G, T.Unit) = T.Unit
      | raisePrg (G, T.PairPrg (P1, P2)) =
        let 
	  val P1' = raisePrg (G, P1)
	  val P2' = raisePrg (G, P2)
	in
	  T.PairPrg (P1', P2')
	end
      | raisePrg (G, T.PairExp (U, P)) =
	let 
	  val V = TypeCheck.infer' (G, U)
	  val w = S.weaken (G, I.targetFam V)
                                                   (* G  |- w  : G'    *)
	  val iw = Whnf.invert w 	            (* G' |- iw : G     *)
	  val G' = Whnf.strengthen (iw, G)        (* Psi0, G' |- B'' ctx *)

	  val U' = A.raiseTerm (G', I.EClo (U, iw))
	  val P' = raisePrg (G, P)
	in
	  T.PairExp (U', P')
	end



   (* evalPrg (Psi, (P, t)) = V
     
       Invariant:
       If   Psi' |- P :: F
       and  Psi |- t :: Psi'
       and  |- Psi ctx[block]
       and  Psi |- P :: F'
       and  Psi |- P[t] evalsto V
       and  Psi |- F[t] == F'
    *)
    and evalPrg (Psi, (T.Unit, t)) = (print "\nevalPrg1" ; T.Unit)

      | evalPrg (Psi, (T.PairExp (M, P), t))  = (print "\nevalPrg2" ;
	  T.PairExp (I.EClo (M, T.coerceSub t), evalPrg (Psi, (P, t))))

      | evalPrg (Psi, (T.PairBlock (B, P), t)) = (print "\nevalPrg3" ;
          T.PairBlock (I.blockSub (B, T.coerceSub t), evalPrg (Psi, (P, t))))

      | evalPrg (Psi, (T.PairPrg (P1, P2), t)) = (print "\nevalPrg4" ;
	  T.PairPrg (evalPrg (Psi, (P1, t)), evalPrg (Psi, (P2, t))))

      | evalPrg (Psi, (T.Redex (P, S), t)) = (print "\nevalPrg5" ;
	  evalRedex (Psi, evalPrg (Psi, (P, t)), (S, t)))

      | evalPrg (Psi, (T.Root (T.Var k, S), t)) =(print "\nevalPrg6" ;
          (case T.varSub (k, t) 
	    of T.Prg P =>  evalRedex (Psi, evalPrg (Psi, (P, T.id)), (S, t))
	      ))

      | evalPrg (Psi, (T.Root (T.Const lemma, S), t)) = (print "\nevalPrg7" ;
	    evalPrg (Psi, (T.Redex(T.lemmaDef lemma, S), t)))

      | evalPrg (Psi, (T.Lam (D, P), t)) = (print "\nevalPrg8" ;
	  T.Lam (T.decSub (D, t), T.PClo (P, T.dot1 t))) 

      | evalPrg (Psi, (P' as T.Rec (D, P), t)) =  (print "\nevalPrg9" ;
	 evalPrg (Psi, (P, T.Dot (T.Prg (T.PClo (P', t)), t))))


      | evalPrg (Psi, (T.PClo (P, t'), t)) = (print "\nevalPrg10" ;
	  evalPrg (Psi, (P, T.comp (t', t))))

      | evalPrg (Psi, (T.Case (T.Cases O), t')) = (print "\nevalPrg11" ;
						   (* this is ugly.
						    * don't do reverse *)
	 (* reverse list O, so it looks at the
	   cases in the same order it is printed 
	   *)		  
	  match (Psi, t', T.Cases (rev O)))

      | evalPrg (Psi, (T.EVar ((D, r as ref (SOME P), F)), t)) =  (print "\nevalPrg12" ;
	  evalPrg (Psi, (P, t)))

      | evalPrg (Psi, (T.Let (D, P1, P2), t)) = (print "\nevalPrg13" ;
	  let
	    val V = evalPrg (Psi, (P1, t)) 
	  in 
	    evalPrg (Psi, (P2, T.Dot (T.Prg V, t)))
						 
	  end)

      | evalPrg (Psi, (T.New (T.Lam (D, P)), t)) = (print "\nevalPrg14" ;
	   let 
	     val _ = print "["
	     val D' = T.decSub (D, t)
	     val T.UDec (D'') = D'
	     val D''' = T.UDec (Names.decName (T.coerceCtx Psi, D''))  (* unnecessary naming, remove later --cs *)
	     val V = evalPrg (I.Decl (Psi, D'''), (P, T.dot1 t))
	     val _ = print "."
	     val B = T.coerceCtx (I.Decl (I.Null, D'''))
	     val _ = print "."
	     val (G, t') = Converter.deblockify B
	     val _ = print "."
						    
	     val _ = print (TomegaPrint.prgToString (I.Decl (Psi, D'''), V))
	     val _ = print "."

	     val newP = raisePrg (G, Normalize.normalizePrg (V, t'))
	     val _ = print (TomegaPrint.prgToString (Psi, newP))
	     val _ = print "]\n"
	   in 
	     newP
	   end)


   (* other cases should not occur -cs *)


 (* match is used to handle Case statements
  match (Psi, t1, O) = V
     
       Invariant:
       If   Psi |- t1 :: Psi''
       and  Psi'' |- O :: F
       and  |- Psi ctx[block]
       then if t1 matches O then Psi |- t ~ O evalPrgs to W
	    otherwise exception NoMatch is raised.
    *)
    and match (Psi, t1, T.Cases ((Psi', t2, P) :: C)) =
        let 
	  (* val I.Null = Psi *)
	  val t = createVarSub (Psi, Psi') (* Psi |- t : Psi' *)
					(* Psi' |- t2 : Psi'' *)

	  
	  val t' = T.comp (t2, t)
	in
	  ( matchSub (Psi, t1, t'); print "\nFOUND CASE\n" ;
	   evalPrg (Psi, (P, Normalize.normalizeSub t)))
	  handle NoMatch => match (Psi, t1, T.Cases C)	  
	end

      (* What do you want to do if it doesn't match anything *)
      (* can't happen when total function - ABP *)
      (* | match (Psi, t1, T.Cases Nil) = raise Domain  *)



    (* createVarSub (Psi, Psi') = t

       Invariant:
       If   |- Psi ctx[block]
       and  |- Psi' ctx
       then Psi |- t :: Psi'
    *)
    and createVarSub (Psi, I.Null) = T.Shift(I.ctxLength(Psi))

      | createVarSub (Psi, Psi'' as I.Decl (Psi', T.PDec (name, F))) =  
        let 
	  val _ = print "\nHELLO 1"
	  val t = createVarSub (Psi, Psi')
	  val t' = T.Dot (T.Prg (T.newEVar (Psi, Normalize.normalizeFor(F,t))), t) 
(*	  val t' = T.Dot (T.Prg (T.newEVar (Psi, F)), t) *)
	in
	  t'
	end

      | createVarSub (Psi, I.Decl (Psi', T.UDec (I.Dec (name, V)))) =  
        let 
	  val _ = print "\nHELLO 2"
	  val t = createVarSub (Psi, Psi')
	in

	  T.Dot (T.Exp (I.EVar (ref NONE, T.coerceCtx Psi, I.EClo (V, T.coerceSub t), ref [])), t)  
(*	  T.Dot (T.Exp (I.EVar (ref NONE, T.coerceCtx Psi, V, ref [])), t)   *)
	end 

      (* abp *)
      | createVarSub (Psi, I.Decl (Psi', T.UDec (I.BDec (name, (cid, s))))) =	
	let
	  val _  = print "\nHELLO 3"
	  val t = createVarSub (Psi, Psi')
	in
          T.Dot (T.Block (I.LVar (ref NONE, I.id, (cid, I.comp (s,  T.coerceSub t)))), t)
(*          T.Dot (T.Block (I.LVar (ref NONE, I.id, (cid, s))), t) *)
	end 


 (* matchSub (t1, t2) = ()
       
       Invariant:
       If   Psi  |- t1 :: Psi'
       and  Psi  |- t2 :: Psi'
       and  Psi  |- t1 == t2 :: Psi'
       and  |- Psi ctx [block]
       then function returns ()
	    otherwise exception NoMatch is raised
    *)
    and matchSub (Psi, T.Shift a, T.Shift b) =  if (a=b) then () else raise NoMatch
                                           (* previously just () -- ABP *)
      | matchSub (Psi, T.Shift n, t as T.Dot _) =  
          matchSub (Psi, T.Dot (T.Idx (n+1), T.Shift (n+1)), t)

      | matchSub (Psi, t as T.Dot _, T.Shift 0) =  (print "\nBecause of what" ; ()) (* Just because ABP 2/5/03 *)


      | matchSub (Psi, t as T.Dot _, T.Shift n) =   (print "\nBecause of who?" ; 
          matchSub (Psi, t, T.Dot (T.Idx (n+1), T.Shift (n+1))))

      | matchSub (Psi, T.Dot (T.Exp U1, t1), T.Dot (T.Exp U2, t2)) = 
	  (matchSub (Psi, t1, t2);
	   Unify.unify (T.coerceCtx Psi, (U1, I.id), (U2, I.id)) handle Unify.Unify s => raise NoMatch)

      | matchSub (Psi, T.Dot (T.Exp U1, t1), T.Dot (T.Idx k, t2)) =  
	  ( matchSub (Psi, t1, t2);
	   Unify.unify (T.coerceCtx Psi, (U1, I.id), (I.Root (I.BVar k, I.Nil), I.id)) handle Unify.Unify _ => raise NoMatch) 

      | matchSub (Psi, T.Dot (T.Idx k, t1), T.Dot (T.Exp U2, t2)) =  
	  ( matchSub (Psi, t1, t2); 
	   Unify.unify (T.coerceCtx Psi, (I.Root (I.BVar k, I.Nil), I.id), (U2, I.id)) handle Unify.Unify _ => raise NoMatch )


      | matchSub (Psi, T.Dot (T.Prg P1, t1), T.Dot (T.Prg P2, t2)) = 
	  ( matchSub (Psi, t1, t2); 
	   matchPrg (Psi, P1, P2))
      | matchSub (Psi, T.Dot (T.Prg P1, t1), T.Dot (T.Idx k, t2)) = 
	  (matchSub (Psi, t1, t2);
	   matchPrg (Psi, P1, T.Root (T.Var k, T.Nil)))
      | matchSub (Psi, T.Dot (T.Idx k, t1), T.Dot (T.Prg P2, t2)) = 
	  (matchSub (Psi, t1, t2);
	   matchPrg (Psi, T.Root (T.Var k, T.Nil), P2))
      | matchSub (Psi, T.Dot (T.Idx k1, t1), T.Dot (T.Idx k2, t2)) =
	  (if k1 = k2 then matchSub (Psi, t1, t2) else raise NoMatch)

    (* evalRedex (Psi, V, (S, t)) = V'
     
       Invariant:
       If   Psi  |- V :: F1
       and  Psi' |- S :: F2 > F3
       and  Psi  |- t :: Psi'
       and  Psi' |- F1 == F2[t]
       and  |- Psi ctx[block]
       and  Psi |- P :: F'
       and  Psi |- V . (S[t]) evalsto V''
       then Psi |- V' == V'' : F3[t]
    *)

  and evalRedex (Psi, V, (T.Nil, _)) = (print "\nevalRedex1" ; V)
    | evalRedex (Psi, V, (T.SClo (S, t1), t2)) =(print "\nevalRedex2" ; 
          evalRedex (Psi, V, (S, T.comp (t1, t2))))
    | evalRedex (Psi, T.Lam (T.UDec (I.Dec (_, A)), P'), (T.AppExp (U, S), t)) =  (print "\nevalRedex3" ;     
	  evalRedex (Psi, evalPrg (Psi, (P', T.Dot (T.Exp (I.EClo (U, T.coerceSub t)), T.id))), (S, t))) 

    | evalRedex (Psi, T.Lam (T.UDec _, P'), (T.AppBlock (B, S), t)) = (print "\nevalRedex4" ; 
          evalRedex (Psi, evalPrg (Psi, (P', T.Dot (T.Block (I.blockSub (B, T.coerceSub t)), T.id))), (S, t)))

    | evalRedex (Psi, T.Lam (T.PDec _, P'), (T.AppPrg (P, S), t)) = (print "\nevalRedex5" ; 
	  let
	    val V = evalPrg (Psi, (P, t))
	    val V' = evalPrg (Psi, (P', T.Dot (T.Prg V, T.id)))
	  in
	    evalRedex (Psi, V', (S, t))
	  end)

  (* in -- removed local *)
    val evalPrg = fn P => evalPrg (I.Null, (P, T.id))  
  
  (* end -- removed local *)

end



