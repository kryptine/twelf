(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)


functor Opsem ((*! structure IntSyn' : INTSYN !*)
               (*! structure Tomega' : TOMEGA !*)
               (*! sharing Tomega'.IntSyn = IntSyn' !*)
	       structure Whnf : WHNF
	       (*! sharing Whnf.IntSyn = IntSyn' !*)
	       structure Abstract : ABSTRACT
               (*! sharing Abstract.IntSyn = IntSyn'!*)
	       structure Subordinate : SUBORDINATE
	       (*! sharing Subordinate.IntSyn = IntSyn'!*)
	       structure Normalize : NORMALIZE
	       (*! sharing Normalize.Tomega = Tomega' !*)
	       structure TypeCheck : TYPECHECK
	       (*! sharing TypeCheck.IntSyn = IntSyn' !*)
	       structure TomegaTypeCheck : TOMEGATYPECHECK
	       (*! sharing TomegaTypeCheck.IntSyn = IntSyn' !*)
	       (*! sharing TomegaTypeCheck.Tomega = Tomega' !*)
	       structure TomegaPrint : TOMEGAPRINT
	       (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
	       (*! sharing TomegaPrint.Tomega = Tomega' !*)
	       structure Converter : CONVERTER
	       (*! sharing Converter.IntSyn = IntSyn' !*)
	       (*! sharing Converter.Tomega = Tomega' !*)
	       structure Print : PRINT
	       (*! sharing Print.IntSyn = IntSyn' !*)
	       structure Unify : UNIFY
	       (*! sharing Tomega'.IntSyn = Unify.IntSyn !*)
		   ) : OPSEM = 

struct
  (*! structure Tomega = Tomega' !*)
  (*! structure IntSyn = IntSyn' !*)
  structure T = Tomega
  structure I = IntSyn
  structure S = Subordinate    
  structure A = Abstract

  exception Error of string

  local
    
    exception NoMatch


   fun matchPrg (Psi, P1, P2) = 
(*       let 
	 val V = evalPrg (Psi, (P1, T.id))
       in *)
         matchVal (Psi, (P1, T.id), 
		   Normalize.normalizePrg (P2, T.id))
(*       end *)
    (* matchVal (Psi, V1, V2) = ()
  
       Invariant:
       If   Psi |- V1 :: F
       and  Psi |- V1 value
       and  Psi |- V2 :: F
       and  Psi |- V2 value
       then if  Psi |- P1 == P2 matchPrg terminates
	    otherwise exception NoMatch is raised
    *)
	 
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
     | matchVal (Psi, (P', t1), T.EVar (_, r as ref NONE, _)) = 
	 (r := SOME (T.PClo (P', t1)))
     | matchVal (Psi, (T.Rec _, _), T.PairPrg _) = raise Domain
	

(*
     | matchVal (Psi, (T.EVar (_, r as ref (SOME (T.PClo _)), _), t1), P2) = raise Domain

*)
     | matchVal (Psi, (T.EVar (_, r as ref (SOME P1), _), t1), P2) = raise Domain
	 (* abp  
	 (matchVal (Psi, (P1,t1), P2)) *)

     | matchVal (Psi, (T.Rec (_, P1) ,t1), T.PairExp (U2, P2)) = raise Domain

     | matchVal _ = raise NoMatch




    (* raisePrg (G, P, F) = (P', F')) 
 
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
    and evalPrg (Psi, (T.Unit, t)) = T.Unit
      | evalPrg (Psi, (T.PairExp (M, P), t)) = 
	  T.PairExp (I.EClo (M, T.coerceSub t), evalPrg (Psi, (P, t)))
      | evalPrg (Psi, (T.PairBlock (B, P), t)) =
          T.PairBlock (I.blockSub (B, T.coerceSub t), evalPrg (Psi, (P, t)))
      | evalPrg (Psi, (T.PairPrg (P1, P2), t)) =
	  T.PairPrg (evalPrg (Psi, (P1, t)), evalPrg (Psi, (P2, t)))
      | evalPrg (Psi, (T.Redex (P, S), t)) =
	  (print "last"; evalRedex (Psi, evalPrg (Psi, (P, t)), (S, t)))
      | evalPrg (Psi, (T.Root (T.Var k, S), t)) =
          (print "root"; case T.varSub (k, t) 
             of T.Prg V =>  evalRedex (Psi, evalPrg (Psi, (V, T.id)), (S, t)))
      | evalPrg (Psi, (T.Root (T.Const lemma, _), t)) =
          T.lemmaDef lemma
      | evalPrg (Psi, (T.Lam (D, P), t)) =
	  T.Lam (T.decSub (D, t), T.PClo (P, T.dot1 t))
	  (* Need to add support for the NEW construct *)

      | evalPrg (Psi, (P' as T.Rec (D, P), t)) = 
	  evalPrg (Psi, (P, T.Dot (T.Prg (T.PClo (P', t)), t)))

      | evalPrg (Psi, (T.PClo (P, t'), t)) =
	  evalPrg (Psi, (P, T.comp (t', t)))
      | evalPrg (Psi, (T.Case O, t')) =
          match (Psi, t', O)

      | evalPrg (Psi, (T.EVar ((D, r as ref (SOME P), F)), t)) =
	  evalPrg (Psi, (P, t))

      | evalPrg (Psi,(T.EVar ((D, ref NONE, F)), t)) = 
	  raise Domain

   (* Let case *)
      | evalPrg (Psi, (T.Let (D, P1, P2), t)) =
	  let val V = evalPrg (Psi, (P1, t))
	      val _ = print (TomegaPrint.prgToString (Psi, V))
	  in 

	    evalPrg (Psi, (P2, T.Dot (T.Prg V, t)))
	  end

      | evalPrg (Psi, (T.New (T.Lam (D, P)), t)) = 
	  (* abp 	  raise Domain    *)
	  ( print "\nNew" ; 
	   let 
	     val D' = T.decSub (D, t)
	     val V = evalPrg (I.Decl (Psi, D'), (P, T.dot1 t))
	       (* Carsten to fix..  Formula is set to T.True..  not so good *)
	     val newP = raisePrg (T.coerceCtx (I.Decl (I.Null, D')), V)
	   in 
	     newP
	   end )


   (* other cases should not occur -cs *)
   (* | evalPrg (Psi, (T.EVar ((D, r as ref NONE, F)), t))
	 let 
	    X = T.EVar (Psi, ref NONE, T. FClo (F, t))
	 in
	    r := T.PClo (X, t
	    
	 evalPrg (Psi, (P, t))
   *)	  



 (* match (Psi, t, O) = V
     
       Invariant:
       If   Psi |- t1 :: Psi''
       and  Psi'' |- O :: F
       and  |- Psi ctx[block]
       then if t1 matches O then Psi |- t ~ O evalPrgs to W
	    otherwise exception NoMatch is raised.
    *)
    and match (Psi, t1, T.Cases ((Psi', t2, P) :: C)) =
        let 
	  val t = createVarSub (Psi, Psi') (* Psi |- t : Psi' *)
					(* Psi' |- t2 : Psi'' *)

	  val t' = T.comp (t2, t)
(*	  val  _ = TomegaTypeCheck.checkSub (Psi, t, Psi') *)
	in
	  (print "\n["; matchSub (Psi, t1, t'); print "\n]";
	   evalPrg (Psi, (P, Normalize.normalizeSub t)))
(*abp	  handle NoMatch => (print "\n}";match (Psi, t, T.Cases C)) *)
	  handle NoMatch => (print "\n}";match (Psi, t1, T.Cases C))
	  
	end

      | match (Psi, t1, T.Cases Nil) = raise Domain



    (* createVarSub (Psi, Psi') = t

       Invariant:
       If   |- Psi ctx[block]
       and  |- Psi' ctx
       then Psi |- t :: Psi'
    *)
    and createVarSub (Psi, I.Null) = T.Shift(I.ctxLength(Psi))

      | createVarSub (Psi, I.Decl (Psi', T.PDec (name, F))) =
        let 
	  val t = createVarSub (Psi, Psi')
	in
          T.Dot (T.Prg (T.EVar (Psi, ref NONE, Normalize.normalizeFor (F, t))), t)
	end

      | createVarSub (Psi, I.Decl (Psi', T.UDec (I.Dec (name, V)))) =
        let 
	  val t = createVarSub (Psi, Psi')
	in
	  T.Dot (T.Exp (I.EVar (ref NONE, T.coerceCtx Psi, I.EClo (V, T.coerceSub t), ref [])), t)  
	end 

      (* abp *)
      | createVarSub (Psi, I.Decl (Psi', T.UDec (I.BDec (name, (cid, s))))) =	
	let
	  val t = createVarSub (Psi, Psi')
	in
          T.Dot (T.Block (I.LVar (ref NONE, I.id, (cid, s))), t)
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
    and matchSub (Psi, T.Shift _, T.Shift _) = ()
      | matchSub (Psi, T.Shift n, t as T.Dot _) =
          (print "\nX"; matchSub (Psi, T.Dot (T.Idx (n+1), T.Shift (n+1)), t))
      | matchSub (Psi, t as T.Dot _, T.Shift n) =
          matchSub (Psi, t, T.Dot (T.Idx (n+1), T.Shift (n+1)))
      | matchSub (Psi, T.Dot (T.Exp U1, t1), T.Dot (T.Exp U2, t2)) =
	  ((matchSub (Psi, t1, t2); (* print "\nE:"; print (Print.expToString (T.coerceCtx Psi, U1) ^ " =?= " ^ Print.expToString (T.coerceCtx Psi, U2) ^ "\n"); *)
	    
	   Unify.unify (T.coerceCtx Psi, (U1, I.id), (U2, I.id)); print "\nU") handle Unify.Unify s => (print s; raise NoMatch))
      | matchSub (Psi, T.Dot (T.Exp U1, t1), T.Dot (T.Idx k, t2)) =
	  (matchSub (Psi, t1, t2);
	   Unify.unify (T.coerceCtx Psi, (U1, I.id), (I.Root (I.BVar k, I.Nil), I.id)) handle Unify.Unify _ => raise NoMatch)
      | matchSub (Psi, T.Dot (T.Idx k, t1), T.Dot (T.Exp U2, t2)) =
	  (matchSub (Psi, t1, t2);
	   Unify.unify (T.coerceCtx Psi, (I.Root (I.BVar k, I.Nil), I.id), (U2, I.id)) handle Unify.Unify _ => raise NoMatch)
      | matchSub (Psi, T.Dot (T.Prg P1, t1), T.Dot (T.Prg P2, t2)) =
	  (matchSub (Psi, t1, t2); print "\nP" ;
	   matchPrg (Psi, P1, P2))
      | matchSub (Psi, T.Dot (T.Prg P1, t1), T.Dot (T.Idx k, t2)) =
	  (matchSub (Psi, t1, t2); print "\n1";
	   matchPrg (Psi, P1, T.Root (T.Var k, T.Nil)))
      | matchSub (Psi, T.Dot (T.Idx k, t1), T.Dot (T.Prg P2, t2)) =
	  (matchSub (Psi, t1, t2); print "\n2";
	   matchPrg (Psi, T.Root (T.Var k, T.Nil), P2))
      | matchSub (Psi, T.Dot (T.Idx k1, t1), T.Dot (T.Idx k2, t2)) =
	  if k1 = k2 then matchSub (Psi, t1, t2) else raise NoMatch

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

  and evalRedex (Psi, V, (T.Nil, _)) = V
    | evalRedex (Psi, V, (T.SClo (S, t1), t2)) = 
          evalRedex (Psi, V, (S, T.comp (t1, t2)))
    | evalRedex (Psi, T.Lam (T.UDec (I.Dec (_, A)), P'), (T.AppExp (U, S), t)) = (print "\n*"; TypeCheck.typeCheck (T.coerceCtx Psi, (I.EClo(U, T.coerceSub t), A));
	  evalRedex (Psi, evalPrg (Psi, (P', T.Dot (T.Exp (I.EClo (U, T.coerceSub t)), T.id))), (S, t)))
    | evalRedex (Psi, T.Lam (T.UDec _, P'), (T.AppBlock (B, S), t)) =
          evalRedex (Psi, evalPrg (Psi, (P', T.Dot (T.Block (I.blockSub (B, T.coerceSub t)), T.id))), (S, t))
    | evalRedex (Psi, T.Lam (T.PDec _, P'), (T.AppPrg (P, S), t)) =
	  let
	    val V = evalPrg (Psi, (P, t))
	    val V' = evalPrg (Psi, (P', T.Dot (T.Prg V, T.id)))
	  in
	    evalRedex (Psi, V', (S, t))
	  end

  in
    val evalPrg = fn P => evalPrg (I.Null, (P, T.id))  
  
  end
end



