(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)


functor Opsem (structure Tomega' : TOMEGA
	       structure Normalize : NORMALIZE
		 sharing Normalize.Tomega = Tomega'
	       structure Unify : UNIFY
		 sharing Tomega'.IntSyn = Unify.IntSyn) : OPSEM = 

struct
  structure Tomega = Tomega'
  structure T = Tomega
  structure I = Tomega.IntSyn
  
  exception Error of string

  local
    
    exception NoMatch


   fun matchPrg (Psi, P1, P2) = matchVal (Psi, evalPrg (Psi, (P1, T.id)),
					   evalPrg (Psi, (P2, T.id))) 

    (* matchVal (Psi, V1, V2) = ()
  
       Invariant:
       If   Psi |- V1 :: F
       and  Psi |- V1 value
       and  Psi |- V2 :: F
       and  Psi |- V2 value
       then if  Psi |- P1 == P2 matchPrg terminates
	    otherwise exception NoMatch is raised
    *)

 and matchVal (Psi, T.Unit, T.Unit) = ()
   | matchVal (Psi, T.PairPrg (P1, P1'), T.PairPrg (P2, P2')) =
	  (matchVal (Psi, P1, P2);
	   matchVal (Psi, P1', P2'))
   | matchVal (Psi, T.PairBlock (B1, P1), T.PairBlock (B2, P2)) =
	  (matchVal (Psi, P1, P2);
           Unify.unifyBlock (I.blockSub (B1, I.id), I.blockSub (B2, I.id)))
   | matchVal (Psi, T.PairExp (U1, P1), T.PairExp (U2, P2)) =
	  (matchVal (Psi, P1, P2);
	   Unify.unify (T.coerceCtx Psi, (U1, I.id), (U2, I.id)))
   | matchVal _ = raise NoMatch



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
	  evalRedex (Psi, evalPrg (Psi, (P, t)), (S, t))
      | evalPrg (Psi, (T.Root (T.Var k, _), t)) =
          (case T.varSub (k, t) 
             of T.Prg V => V)
      | evalPrg (Psi, (T.Root (T.Const lemma, _), t)) =
          T.lemmaDef lemma
      | evalPrg (Psi, (T.Lam (D, P), t)) =
	  T.Lam (T.decSub (D, t), T.PClo (P, t))
	  (* special case for D = BDec (c, s), we need to abstract here --cs*)
      | evalPrg (Psi, (P' as T.Rec (D, P), t)) = 
	  evalPrg (Psi, (P, T.Dot (T.Prg P', t)))
      | evalPrg (Psi, (T.PClo (P, t'), t)) =
	  evalPrg (Psi, (P, T.comp (t', t)))
      | evalPrg (Psi, (T.Case O, t')) =
          match (Psi, t', O)
(* was:     | evalPrg (Psi, (T.Case (t, O), t')) =
	  match (Psi, T.comp (t, t'), O) *)
      | evalPrg (Psi, (T.EVar ((D, r as ref (SOME P), F)), t)) =
	  evalPrg (Psi, (P, t))
   
   (* other cases should not occur -cs *)
   (* | evalPrg (Psi, (T.EVar ((D, r as ref NONE, F)), t))
	 let 
	    X = T.EVar (Psi, ref NONE, T. FClo (F, t))
	 in
	    r := T.PClo (X, t
	    
	 evalPrg (Psi, (P, t))
   *)	  
  (* need Let case  *) 


 (* match (Psi, t, O) = V
     
       Invariant:
       If   Psi |- t :: Psi'
       and  Psi' |- O :: F
       and  |- Psi ctx[block]
       then if t matches O then Psi |- t ~ O evalPrgsto W
	    otherwise exception NoMatch is raised.
    *)
    and match (Psi, t1, T.Cases ((Psi', t2, P) :: C)) =
        let 
	  val  t = t1 (* diffSub (Psi, Psi', t1, t2)  *)
	in
	  evalPrg (Psi, (P, t))
	  handle T.NoMatch => match (Psi, t, T.Cases C) 
	end


(* diffSub (Psi', Psi, t1, t2) = t
       
       Invariant:
       If   Psi'  |- t1 :: Psi
       and  Psi'' |- t2 :: Psi
       and  |- Psi' ctx[block]
       then Psi'  |- t :: Psi''  if such a t exists
	    otherwise exception NoMatch is raised
       and  Psi'  |- t2 o t :: Psi 
    *)
    and diffSub (Psi', Psi'', t1, t2) = 
        let 
	  val t = createVarSub (Psi', Psi'')
	  val t2' = T.comp (t2, t)
	in 
	  (matchSub (Psi', t1, t2');
	   Normalize.normalizeSub t) 
	end
      



    (* createVarSub (Psi, Psi') = t

       Invariant:
       If   |- Psi ctx[block]
       and  |- Psi' ctx
       then Psi |- t :: Psi'
    *)
    and createVarSub (Psi, I.Null) = T.id
      | createVarSub (Psi, I.Decl (Psi', T.PDec (name, F))) =
          T.Dot (T.Prg (T.EVar (Psi, ref NONE, F)), 
		 createVarSub (Psi, Psi')) 
      | createVarSub (Psi, I.Decl (Psi', T.UDec (I.BDec (name, (cid, s))))) =	
          T.Dot (T.Block (I.LVar (ref NONE, (cid, s))),
		 createVarSub (Psi, Psi'))  
      | createVarSub (Psi, I.Decl (Psi', T.UDec (I.Dec (name, V)))) =
	  T.Dot (T.Exp (I.EVar (ref NONE, T.coerceCtx Psi, V, ref [])),
		 createVarSub (Psi, Psi'))  
     

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
          matchSub (Psi, T.Dot (T.Idx (n+1), T.Shift (n+1)), t)
      | matchSub (Psi, t as T.Dot _, T.Shift n) =
          matchSub (Psi, t, T.Dot (T.Idx (n+1), T.Shift (n+1)))
      | matchSub (Psi, T.Dot (T.Exp U1, t1), T.Dot (T.Exp U2, t2)) =
	  (Unify.unify (T.coerceCtx Psi, (U1, I.id), (U2, I.id));
	   matchSub (Psi, t1, t2))
     | matchSub (Psi, T.Dot (T.Exp U1, t1), T.Dot (T.Idx k, t2)) =
	  (Unify.unify (T.coerceCtx Psi, (U1, I.id), (I.Root (I.BVar k, I.Nil), I.id));
	   matchSub (Psi, t1, t2))
     | matchSub (Psi, T.Dot (T.Idx k, t1), T.Dot (T.Exp U2, t2)) =
	  (Unify.unify (T.coerceCtx Psi, (I.Root (I.BVar k, I.Nil), I.id), (U2, I.id));
	   matchSub (Psi, t1, t2))
     | matchSub (Psi, T.Dot (T.Prg P1, t1), T.Dot (T.Prg P2, t2)) =
	  (matchPrg (Psi, P1, P2);
	   matchSub (Psi, t1, t2))
     | matchSub (Psi, T.Dot (T.Prg P1, t1), T.Dot (T.Idx k, t2)) =
	  (matchPrg (Psi, P1, T.Root (T.Var k, T.Nil));
	   matchSub (Psi, t1, t2))
     | matchSub (Psi, T.Dot (T.Idx k, t1), T.Dot (T.Prg P2, t2)) =
	  (matchPrg (Psi, T.Root (T.Var k, T.Nil), P2);
	   matchSub (Psi, t1, t2))
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
    | evalRedex (Psi, T.Lam (T.UDec _, P'), (T.AppExp (U, S), t)) =
	  evalRedex (Psi, evalPrg (Psi, (P', T.Dot (T.Exp (I.EClo (U, T.coerceSub t)), T.id))), (S, t))
    | evalRedex (Psi, T.Lam (T.UDec _, P'), (T.AppBlock (B, S), t)) =
          evalRedex (Psi, evalPrg (Psi, (P', T.Dot (T.Block (I.blockSub (B, T.coerceSub t)), T.id))), (S, t))
    | evalRedex (Psi, T.Lam (T.PDec _, P'), (T.AppPrg (P, S), t)) =
	  evalRedex (Psi, evalPrg (Psi, (P', T.Dot (T.Prg (T.PClo (P, t)), T.id))), (S, t))

  in
    val evalPrg = fn P => evalPrg (I.Null, (P, T.id))  
  
  end
end



