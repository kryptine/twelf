(* Type checking for Tomega *)
(* Author: Carsten Schuermann *)
(* Modified: Yu Liao *)

functor TomegaTypeCheck
  ((*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   structure TypeCheck : TYPECHECK
   (*! sharing TypeCheck.IntSyn = IntSyn' !*)
   structure Conv : CONV
   (*! sharing Conv.IntSyn = IntSyn' !*)
   structure Normalize : NORMALIZE
   (*! sharing Normalize.IntSyn = IntSyn' !*)
   (*! sharing Normalize.Tomega = Tomega' !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Print : PRINT
   (*! sharing Print.IntSyn = IntSyn' !*)
   structure TomegaPrint : TOMEGAPRINT
   (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
   (*! sharing TomegaPrint.Tomega = Tomega' !*)
   structure Subordinate : SUBORDINATE
   (*! sharing Subordinate.IntSyn = IntSyn' !*)
   structure Weaken : WEAKEN
   (*! sharing Weaken.IntSyn = IntSyn' !*)
       ) : TOMEGATYPECHECK = 
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)

  exception Error of string 
  
  local 
    structure I = IntSyn
    structure T = Tomega
    structure S = Subordinate    



    fun chatter chlev f =
        if !Global.chatter >= chlev
	  then print (f ())
	else ()

     fun normalizeHead (T.Const lemma, t) = T.Const lemma
      | normalizeHead (T.Var k, t) =
        (case T.varSub (k, t)
	   of T.Idx (k') => T.Var (k'))
	(* no other cases can occur *)


    (* inferCon (Psi, (H, t)) = (F', t')
     
       Invariant:
       If   Psi  |- t : Psi1 
       and  Psi1 |- H : F
       then Psi  |- F'[t'] == F[t]
    *)
    fun inferCon (Psi, T.Const lemma) = inferLemma lemma
      | inferCon (Psi, T.Var k) = 
	  case T.ctxDec (Psi, k) of T.PDec (_, F') => F' 


    (* inferSpine (Psi, (S, t1), (F, t2)) = (F', t')
     
       Invariant:
       If   Psi  |- t1 : Psi1 
       and  Psi1 |- S : F' > F''
       and  Psi  |- t2 : Psi2
       and  Psi2 |- F for
       and  Psi  |- F'[t1] == F[t2]
       then Psi  |- F''[t1] == F'[t']
    *)
    and inferSpine (Psi, S, Ft) = inferSpineW (Psi, S, Normalize.whnfFor Ft)
    and inferSpineW (Psi, T.Nil, (F, t)) = (F, t)
      | inferSpineW (Psi, T.AppExp (M, S), (T.All (T.UDec (I.Dec (_, A)), F), t)) =
	let 
	  val _ = chatter 4 (fn () => "[appExp")
	  val G = T.coerceCtx (Psi)
	  val _ = TypeCheck.typeCheck (G, (M, I.EClo (A, T.coerceSub t)))
	  val _ = chatter 4 (fn () => "]")
	in 
	  inferSpine (Psi, S, (F, T.Dot(T.Exp(M), t)))
	end
      | inferSpineW (Psi, T.AppBlock (I.Bidx k, S),
		     (T.All (T.UDec (I.BDec (_, (cid, s))), F2), t2)) =
	let 
	  val T.UDec (I.BDec(_, (cid', s')))= T.ctxDec(Psi, k)
	  val (G', _) = I.conDecBlock (I.sgnLookup cid')
	  val _ = if (cid <> cid') then raise Error("Block label incompatible") else ()
	  val s'' = T.coerceSub (T.comp (T.embedSub s, t2))
	  val _ = Conv.convSub (s', s'') 
	in 
	    inferSpine (Psi, S, (F2, T.Dot(T.Block(I.Bidx k), t2)))
	end
      | inferSpineW (Psi, T.AppPrg (P, S), (T.All (T.PDec (_, F1), F2), t)) =
	let 
	    val _ = checkPrg (Psi, (P, (F1, t)))
	in 
	    inferSpine (Psi, S, (F2, T.dot1 t))
	end
      | inferSpineW (Psi, _, _) = raise Error "applied, but not of function type."


    and inferPrg (Psi, T.Lam (D, P)) = 
        let 
	  val F = inferPrg (I.Decl (Psi, D), P)
	in
	  T.All (D, F)
	end
      | inferPrg (Psi, T.New P) =
	let
	  val T.All (T.UDec (D as (I.BDec _)), F) = inferPrg (Psi, P)
	in
	  F (* raise (D, F) *)
	end
      | inferPrg (Psi, T.PairExp (U, P)) =
	let 
	  val V = TypeCheck.infer' (T.coerceCtx Psi, U)
	  val F = inferPrg (Psi, P)
	in
	  T.Ex (I.Dec (NONE, V), F)
	end
      | inferPrg (Psi, T.PairBlock (I.Bidx k, P)) =
        (* Blocks T.Inst, and T.LVar excluded for now *)
	let 
	  val D = I.ctxLookup (T.coerceCtx Psi, k)
	  val F = inferPrg (Psi, P)
	in
	  T.Ex (D, F)
	end
      | inferPrg (Psi, T.PairPrg (P1, P2)) = 
	let 
	  val F1 = inferPrg (Psi, P1)
	  val F2 = inferPrg (Psi, P2)
	in
	  T.And (F1, F2)
	end
      | inferPrg (Psi, T.Unit) = T.True
      | inferPrg (Psi, T.Root (H, S)) = 
	let
	  val F1 = inferCon (Psi, H)
	  val F2 = inferSpine (Psi, S, (F1, T.id))
	in 
	  Normalize.normalizeFor F2
	end
      | inferPrg (Psi, T.Redex (P, S)) = 
	let
	  val F1 = inferPrg (Psi, P)
	  val F2 = inferSpine (Psi, S, (F1, T.id))
	in 
	  Normalize.normalizeFor F2
	end
      | inferPrg (Psi, T.Rec (D as T.PDec (_, F), P)) = 
	let
	  val _ = checkPrg (I.Decl (Psi, D), (P, (F, T.id)))
	in
	  F
	end
(*      | inferPrg (Psi, T.Case (F, Omega)) = 
	let 
	  val  _ = checkCases (Omega, F)
	in
	  F
	end 
      | inferPrg (Psi, T.PClo (P, t)) =
	let 
	  val Psi' = inferCtx (Psi, t)
	  val F = inferPrg (Psi', P)
	in
	  F
	end

            Problem: inferCtx cannot work because of dependencies -- cs
*)
      | inferPrg (Psi, T.Let (D as T.PDec (_, F1), P1, P2)) =
	let 
	  val _ = checkPrg (Psi, (P1, (F1, T.id)))
	  val F2 = inferPrg (I.Decl (Psi, D), P2)
	in 
	  F2
	end

	
(*

    (* inferFront (Psi, Ft) = D
       
       Invariant:
       If  Psi |- Ft front
       
   *)
    and inferFront (Psi, T.Idx k) = 
      | inferFront (Psi, T.Prg P) = 
      | inferFront (Psi, T.Exp U) = T.UDec (I.Dec (NONE, TypeCheck.infer U))
      | inferFront (Psi, T.Block (I.Bidx k)) = 
          T.UDec (I.BDec ( 


    (* inferSub (Psi, t) = Psi'
     
       Invariant:
       If    Psi  |- t : Psi1 
       then  |- Psi' = Psi1 ctx
    *)
    and inferSub (Psi, T.Shift k) = 
  	if k = I.ctxLength Psi then T.id
	else inferSub (Psi, T.Dot (T.Idx (k+1), T.Shift (k+1)))
      | inferSub (Psi, T.Dot (Ft, t)) =
          I.Decl (inferSub (Psi, t), inferFront (Psi, Ft))

*)
    (* checkPrg (Psi, P, F) = ()
     
       Invariant:
       If   Psi  |- t1 : Psi1 
       and  Psi1 |- P : F'
       and  Psi  |- F for     (F in normal form)
       and  P does not contain any P closures
       then checkPrg returns () iff F'[t1] == F[id]
    *)
    and checkPrg (Psi, (P, Ft)) = checkPrgW (Psi, (P, Normalize.whnfFor Ft))
    and checkPrgW (_, (T.Unit, (T.True, _))) =
        let 
	  val _ = chatter 4 (fn () => "[true]")
	in
          ()
	end
      | checkPrgW (Psi, (T.Root (H, S), (F, t))) =
	let
	  val F' = inferCon (Psi, H)
	  val Ft'' = inferSpine (Psi, S, (F', T.id))
	  val _ = convFor (Psi, Ft'', (F, t))
	in 
	  ()
	end

      | checkPrgW (Psi, (T.Lam (D as T.PDec (x, F1), P), (T.All (T.PDec (x', F1'), F2), t))) = 
	let 
	  val _ = chatter 4 (fn () => "[lam[p]")
	    val _ = convFor (Psi, (F1, T.id), (F1', t))
	  val _ = chatter 4 (fn () => "]")
	in 
	    checkPrg (I.Decl (Psi, D), (P, (F2, T.dot1 t)))
	end
      | checkPrgW (Psi, (T.Lam (T.UDec D, P), (T.All (T.UDec D', F), t2))) =
	let 
	  val _ = chatter 4 (fn () => "[lam[u]")
	  val _ = Conv.convDec ((D, I.id), (D', T.coerceSub t2))
	  val _ = chatter 4 (fn () => "]")
	in  
	    checkPrg (I.Decl (Psi , T.UDec D), (P, (F, T.dot1 t2)))
	end
      | checkPrgW (Psi, (T.PairExp (M, P), (T.Ex(I.Dec(x, A), F2), t))) =
	let 
	  val _ = chatter 4 (fn () => "[pair [e]")
	  val G = T.coerceCtx Psi
	  val _ = TypeCheck.typeCheck(G, (M, I.EClo (A, T.coerceSub(t))))
	  val _ = chatter 4 (fn () => "]")
	in 
	    checkPrg(Psi, (P, (F2, T.Dot (T.Exp M, t))))
	end
      | checkPrgW (Psi, (T.PairBlock (I.Bidx k, P), (T.Ex (I.BDec (_, (cid, s)), F2), t))) =
	let
	  val T.UDec (I.BDec(_, (cid', s'))) = T.ctxDec (Psi, k)
	  val (G', _) = I.conDecBlock (I.sgnLookup cid)
	  val _ = if (cid' <> cid) then raise Error ("Block label mismatch") else ()
	  val _ = convSub (Psi, T.embedSub s', T.comp(T.embedSub(s), t), T.revCoerceCtx(G'))  
	in 
	  checkPrg(Psi, (P, (F2, T.Dot(T.Block(I.Bidx k), t))))
	end
      | checkPrgW (Psi, (T.PairPrg (P1, P2), (T.And( F1, F2), t))) =
	let
	  val _ = chatter 4 (fn () => "[and")	  
	  val _ = checkPrg (Psi, (P1, (F1, t)))
	  val _ = chatter 4 (fn () => "...")	  
	  val _ = checkPrg (Psi, (P2, (F2, t)))
	  val _ = chatter 4 (fn () => "]")

	in
	  ()
	end
      | checkPrgW (Psi, (T.Case Omega, Ft)) = 
	  checkCases (Psi, (Omega, Ft))
      | checkPrgW (Psi, (T.Rec (D as T.PDec (x, F), P), (F', t))) =
	let 
	  val _ = chatter 4 (fn () => "[rec")
	  val _ = convFor(Psi, (F, T.id), (F', t))
	  val _ = chatter 4 (fn () => "]\n")
	in 
	    checkPrg (I.Decl(Psi, D), (P, (F', t)))
	end
      | checkPrgW (Psi, (T.Let (D as T.PDec(_, F1), P1, P2), (F2, t))) = 
					(* Psi |- let xx :: F1 = P1 in P2 : F2' *)
	                                (* Psi |- t : Psi' *)
					(* Psi' |- F2 for *)
					(* Psi |- F2' = F2[t] *)
					(* Psi |- F1 :: for *)
					(* Psi |- P1 :: F1' *)
	                                (* Psi, D |- P2 :: (F2' [^]) *)
					(* Psi' |- F2' :: for *)
					(* Psi, D |- t o ^ :: Psi' *)
	let 
	  val _ = chatter 4 (fn () => "[let")
	  val _ = checkPrg (Psi, (P1, (F1, T.id)))
					(* Psi |- F1 == F1' for *)
	  val _ = chatter 4 (fn () => ".")
	  val _ = checkPrg (I.Decl (Psi, D), (P2, (F2, T.comp (t, T.shift))))
	  val _ = chatter 4 (fn () => "]\n")
	in
	  ()
	end
      | checkPrgW (Psi, (T.New (T.Lam (D as T.UDec (I.BDec (_, (cid, s))), P)), (F, t))) =
	  (print "* Temporary incompleteness;  code is written but not yet clean\n") 
      | checkPrgW (Psi, (T.Redex (P1, P2), (F, t))) =
	  (print "* Temporary incompleteness; redex not checkable")
(*	let 

	  fun makeCtx (G, (nil, s)) = G
	    | makeCtx (G, (D::L, s)) = 
	       makeCtx (I.Decl (G, I.decSub (D, s)), (L, I.dot1 s))
	       
	  fun drop n Vs = dropW n (Whnf.whnf Vs)
	  and dropW 0 (V, s) = (V, s)
	    | dropW n (I.Pi (_, V), s) = drop (n-1) (V, I.dot1 s)


    (* strengthen (t, G) = G'

       Invariant:
       If   G'' |- t : G    (* and t strsub *)
       then G' |- t : G  and G' subcontext of G
    *)
	  fun strengthenPi (Shift n (* = 0 *), V) = (V, I.Null)
	    | strengthenPi (Dot (Idx k (* k = 1 *), t), Decl (G, D), V) =
  	      let 
		val t' = comp (t, invShift)
		val (I.Pi (D', V'), G') = strengthenPi (t', G)
		val _ = TypeCheck.typeCheck (G', D, D')
 
	      in
		(* G |- D dec *)
		(* G' |- t' : G *)
		(* G' |- D[t'] dec *)
		(I.Pi (D', V'), Decl (G', decSub (D, t')))
	      end
	    | strengthenPi (Dot (Undef, t), Decl (G, D), V) = 
  	      let 
		val t' = t
		val (I.Pi (D', V'), G') = strengthenPi (t', G)
		val _ = TypeCheck.typeCheck (G', D, D')
 
	      in
	        (V', G')
	      end
	    | strengthenPi (Shift n, G) = 
	        strengthenPi (Dot (Idx (n+1), Shift (n+1)), G)


	  (* removeFor (Gpi, (F, s)) = F'
	   
	     Invariant:
	     If   Psi |- Gpi ctx
	     and  Psi |- F[s] formula
	     then Psi, Gpi |- F' formula
	  *)
	  fun removeFor (Gpi, (T.True, _)) = T.True
	    | removeFor (Gpi, (T.All (T.UDec (I.Dec (x, V)), F), s)) = 
	      let 
		val w = S.weaken (Gpi, I.targetFam V)
                                                        (* Gpi  |- w  : G'    *)
		val iw = Whnf.invert w 	                (* G' |- iw : G     *)
		val G' = Whnf.strengthen (iw, Gpi)        (* Psi0, G' |- B'' ctx *)
		val g = I.ctxLength G'
		val (V', s') = drop g (V, s)
		val V'' = I.EClo (V', I.comp (s', w))                (* Gpi |- V : type *)
		val F' = removeFor (Gpi, (F, I.dot1 s))
	      in
		T.All (T.UDec (I.Dec (x, V'')), F')
	      end
	    | removeFor (Gpi, (T.Ex (I.Dec (x, V), F), s)) = 
	      let 
		val w = S.weaken (Gpi, I.targetFam V)
                                                        (* Gpi  |- w  : G'    *)
		val iw = Whnf.invert w 	                (* G' |- iw : G     *)
		val G' = Whnf.strengthen (iw, Gpi)        (* Psi0, G' |- B'' ctx *)
		val g = I.ctxLength G'
		val (V', s') = drop g (V, s)
		val V'' = I.EClo (V', I.comp (s', w))                (* Gpi |- V : type *)
		val F' = removeFor (Gpi, (F, I.dot1 s))
	      in
		T.Ex (I.Dec (x, V''), F')
	      end

	    fun makeSub (0, t) = t
	      | makeSub (n, t) = 
	          makeSub (n-1, T.Dot (T.Exp (I.Root (I.Proj (I.Bidx 1, n), I.Nil)), t))

	  val (Gsome, Lpi) = I.conDecBlock (I.sgnLookup cid) 
 				       	                (* Psi |- s : Gsome*)
	  val Gpi = makeCtx (I.Null, (Lpi, s))          (* Psi |- Gpi ctx *)
	  val _ = TypeCheck.typeCheckCtx (Gpi)
	    
	  val F' = removeFor (Gpi, (F, T.coerceSub t))  (* Psi, Gpi |- F' for *)
	  val t' = makeSub (List.length Lpi, T.Shift (I.ctxLength Psi + 1))
	in
	  checkPrgW (I.Decl (Psi, D), (P, (F', t')))
	end
*)


(* raise Domain *)
(*      | checkPrg (G, ((T.Redex (P, T.Nil), s), Fs)) = checkPrg (G, ((P, s), Fs)) *)
(*      | checkPrg (G, ((T.Redex (P, T.AppExp(M, S)), s), (F2, s2))) =  -- Yu Liao *)
(*      | checkPrg (G, ((T.PClo(P1,s1), s11), (F2, s2))) = checkPrg (G, ((P1, T.comp(s1, s11)), (F2, s2))) *)



    (* checkCases (Psi, (Omega, (F, t2))) = ()
       Invariant:
       and  Psi |- Omega : F'
       and  Psi |- F' for
       then checkCases returns () iff Psi |- F' == F [t2] formula
    *)
    and checkCases (Psi, (T.Cases nil, (F2, t2))) = ()
      | checkCases (Psi, (T.Cases ((Psi', t', P) :: Omega), (F2, t2))) =
	let 
					(* Psi' |- t' :: Psi *)
	  val _ = chatter 4 (fn () => "[case... ")
	  val _ = chatter 4 (fn () => "sub... ")
	  val _ = checkSub(Psi', t', Psi)
	  val _ = chatter 4 (fn () => "prg... ")
	  val t2' = T.comp(t2, t')
	  val _ = checkCtx Psi
	  val _ = checkCtx Psi'
	  val _ = chatter 4 (fn () => "]")
	  val _ = checkPrg (Psi', (P, (F2, t2')))
	  val _ = chatter 4 (fn () => "]\n")

	  val _ = checkCases (Psi, ((T.Cases Omega), (F2, t2)))
	in 
	  ()
	end 



    and  inferLemma lemma = 
	( case (T.lemmaLookup lemma) 
	    of T.ForDec (_, F) => F 
	     | T.ValDec (_,_,F) => F)



    (* convFor (Psi, (F1, t1), (F2, t2)) = ()

       Invariant:
       If   Psi |- t1 :: Psi1
       and  Ps1 |- F1 for
    *)

    and convFor (Psi, Ft1, Ft2) = convForW (Psi, Normalize.whnfFor Ft1, Normalize.whnfFor Ft2)
    and convForW (_, (T.True, _), (T.True, _)) = ()
      | convForW (Psi, 
		  (T.All (D as T.UDec( I.Dec (_, A1)), F1), t1), 
		  (T.All (     T.UDec( I.Dec (_, A2)), F2), t2)) =
	let
	  val G = T.coerceCtx (Psi)
	  val s1 = T.coerceSub t1
	  val s2 = T.coerceSub t2
	  val _ = Conv.conv((A1, s1), (A2, s2))
	  val _ = TypeCheck.typeCheck(G, (I.EClo (A1, s1), I.Uni I.Type))
	  val _ = TypeCheck.typeCheck(G, (I.EClo (A2, s2), I.Uni I.Type))
	  val D' = T.decSub (D, t1)
	  val _ = convFor (I.Decl(Psi, D'), (F1, T.dot1 t1), (F2, T.dot1 t2))
	in
	  ()
	end
      | convForW (Psi, 
		  (T.All (D as T.UDec (I.BDec(_, (l1, s1))), F1), t1), 
		  (T.All(T.UDec (I.BDec(_, (l2, s2))), F2), t2)) =
	let 
	  val _ = if l1 <> l2 then raise Error "Contextblock clash" else ()
	  val (G', _) = I.conDecBlock (I.sgnLookup l1)
	  val _ = convSub (Psi, 
			   T.comp (T.embedSub s1, t1),
			   T.comp (T.embedSub s2, t2), T.embedCtx G')  
	  val D' = T.decSub (D, t1)
	  val _ = convFor (I.Decl (Psi, D'), (F1, T.dot1 t1), (F2, T.dot1 t2))
	in
	  ()
	end
      | convForW (Psi, 
		  (T.Ex (D as I.Dec (_, A1), F1), t1), 
		  (T.Ex (     I.Dec (_, A2), F2), t2)) =
	let
	  val G = T.coerceCtx (Psi)
	  val s1 = T.coerceSub t1
	  val s2 = T.coerceSub t2
	  val _ = Conv.conv ((A1, s1), (A2, s2))
	  val _ = TypeCheck.typeCheck (G, (I.EClo (A1, s1), I.Uni I.Type))
	  val _ = TypeCheck.typeCheck (G, (I.EClo (A2, s2), I.Uni I.Type))
	  val D' = I.decSub (D, s1)
	  val _ = convFor (I.Decl(Psi, T.UDec D'), (F1, T.dot1 t1), (F2, T.dot1 t2))
	in 
	  ()
	end
      | convForW (Psi, 
		  (T.Ex (D as I.BDec(name, (l1, s1)), F1), t1), 
		  (T.Ex (     I.BDec(_,    (l2, s2)), F2), t2)) =
	let 
	  val _ = if l1 <> l2 then raise Error "Contextblock clash" else ()
	  val (G', _) = I.conDecBlock (I.sgnLookup l1)
	  val s1 = T.coerceSub t1
	  val _ = convSub (Psi, 
			   T.comp (T.embedSub s1, t1), 
			   T.comp (T.embedSub s2, t2), T.embedCtx G')
	  val D' = I.decSub (D, s1)
	  val _ = convFor (I.Decl(Psi, T.UDec D'), (F1, T.dot1 t1), (F2, T.dot1 t2))
	in
	  ()
	end
      | convForW (Psi, 
		  (T.And(F1, F1'), t1), 
		  (T.And(F2, F2'), t2)) =
	let
	  val _ = convFor (Psi, (F1,  t1), (F2,  t2))
	  val _ = convFor (Psi, (F1', t1), (F2', t2)) 
	in 
	  ()
	end
      | convForW (Psi, 
		  (T.All(D as T.PDec(_, F1), F1'), t1), 
		  (T.All(     T.PDec(_, F2), F2'), t2)) =
	let 
	  val _ = convFor (Psi, (F1, t1), (F2, t2))
	  val D' = T.decSub (D, t1)
	  val _ = convFor (I.Decl (Psi, D'), (F1', T.dot1 t1), (F2', T.dot1 t2)) 
	in
	  ()  
	end
      | convForW _ = raise Error "Typecheck error"

    and convSub(G, T.Shift k1, T.Shift k2, G') = if k1=k2 then () else raise Error "Sub not equivalent"
      | convSub(G, T.Shift k, s2 as T.Dot _, G') = convSub(G, T.Dot(T.Idx(k+1), T.Shift(k+1)), s2, G')
      | convSub(G, s1 as T.Dot _, T.Shift k, G') = convSub(G, s1, T.Dot(T.Idx(k+1), T.Shift(k+1)), G')
      | convSub(G, T.Dot(T.Idx k1, s1), T.Dot(T.Idx k2, s2), I.Decl(G', _)) = 
	if k1=k2 (* For s1==s2, the variables in s1 and s2 must refer to the same cell in the context -- Yu Liao *)
	then convSub(G, s1, s2, G')
	else raise Error "Sub not equivalent" 
      | convSub(G, T.Dot(T.Exp M1, s1), T.Dot(T.Exp M2, s2), I.Decl(G', T.UDec(I.Dec(_, A)))) =
	let
	    val _ = TypeCheck.checkConv (M1, M2) (* checkConv doesn't need context G?? -- Yu Liao *)
	    val _ = TypeCheck.typeCheck (T.coerceCtx(G), (M1, A))
	in
	    convSub(G, s1, s2, G')
	end
      | convSub(G, T.Dot(T.Block (I.Bidx v1), s1), T.Dot(T.Block(I.Bidx v2), s2), I.Decl(G', T.UDec (I.BDec (_, (l,s)))))=
	let
	    val T.UDec (I.BDec(_, (l1, s11)))= T.ctxDec(G, v1)	
	    val T.UDec (I.BDec(_, (l2, s22)))= T.ctxDec(G, v2)			 
	    val _ = if l1 = l2 then () else raise Error "Sub not equivalent"
	    val _ = if l1 = l then () else raise Error "Sub not equivalent"
	    val (G'', _) = I.conDecBlock (I.sgnLookup l)
	    val _ = convSub (G, T.embedSub s11, T.embedSub s22, T.revCoerceCtx(G''))
  	    val _ = convSub (G, T.embedSub s11, T.embedSub s, T.revCoerceCtx(G''))
	in
	    convSub(G, s1, s2, G')
	end
      | convSub(G, T.Dot(T.Prg P1, s1), T.Dot(T.Prg P2, s2), I.Decl(G', T.PDec(_, F))) =
	let
	    val _ = isValue P1
	    val _ = isValue P2
	    val _ = convValue (G, P1, P2, F)
	in
	    convSub(G, s1, s2, G')
	end
      | convSub(G, T.Dot(T.Idx k1, s1), T.Dot(T.Exp M2, s2), I.Decl(G', T.UDec(I.Dec(_, A)))) =
	let
	    val _ = TypeCheck.checkConv (I.Root(I.BVar k1, I.Nil), M2) (* checkConv doesn't need context G?? -- Yu Liao ::: No, it doesn't, because context is for typing, not for execution *)
	    val _ = TypeCheck.typeCheck (T.coerceCtx(G), (M2, A))
	in
	    convSub(G, s1, s2, G')
	end
      | convSub(G, T.Dot(T.Exp M1, s1), T.Dot(T.Idx k2, s2), I.Decl(G', T.UDec(I.Dec(_, A)))) =
	let
	    val _ = TypeCheck.checkConv (M1, I.Root(I.BVar k2, I.Nil)) (* checkConv doesn't need context G?? -- Yu Liao *)
	    val _ = TypeCheck.typeCheck (T.coerceCtx(G), (M1, A))
	in
	    convSub(G, s1, s2, G')
	end
(* What is the meaning of I.Bidx??? Is it necessary to have the following case?? *)
(*        | convSub(G, T.Dot(T.Idx k1, s1), T.Dot(T.Block(I.Bidx v2), s2), I.Decl(G', T.BDec(l,s))) = *)
(*  	let *)
(*  	    val T.BDec(l1, s11)= T.ctxDec(G, v1)	 *)
(*  	    val T.BDec(l2, s22)= T.ctxDec(G, v2)			  *)
(*  	    val _ = if l1 = l2 then () else raise Error "Sub not equivalent" *)
(*  	    val _ = if l1 = l then () else raise Error "Sub not equivalent" *)
(*  	    val (G'', _) = I.conDecBlock (I.sgnLookup l) *)
(*  	    val _ = convSub (G, s11, s22, T.revCoerceCtx(G'')) *)
(*    	    val _ = convSub (G, s11, s, T.revCoerceCtx(G'')) *)
(*  	in *)
(*  	    convSub(G, s1, s2, G') *)
(*  	end *)
      | convSub(G, T.Dot(T.Idx k1, s1), T.Dot(T.Prg P2, s2), I.Decl(G', T.PDec(_, F))) =
	let
	    val _ = isValue P2
	    val _ = convValue (G, T.Root(T.Var k1, T.Nil), P2, F)
	in
	    convSub(G, s1, s2, G')
	end
      | convSub(G, T.Dot(T.Prg P1, s1), T.Dot(T.Idx k2, s2), I.Decl(G', T.PDec(_, F))) =
	let
	    val _ = isValue P1
	    val _ = convValue (G, P1, T.Root(T.Var k2, T.Nil), F)
	in
	    convSub(G, s1, s2, G')
	end
      
    and convValue (G, P1, P2, F) = ()
    and checkFor (Psi, (T.True, _)) = ()
      | checkFor (Psi, (T.All (D as T.PDec (_ ,F1), F2), t)) = 
          (checkFor (Psi, (F1, t)); checkFor (I.Decl (Psi, D), (F2, T.dot1 t)))
      | checkFor (Psi, (T.All (D' as T.UDec D, F), t)) =
	  (TypeCheck.checkDec (T.coerceCtx Psi, (D, T.coerceSub t));
	   checkFor (I.Decl (Psi, D'), (F, T.dot1 t)))
      | checkFor (Psi, (T.Ex  (D, F), t)) =
	  (TypeCheck.checkDec (T.coerceCtx Psi, (D, T.coerceSub t));
	   checkFor (I.Decl (Psi, T.UDec D), (F, T.dot1 t)))
      | checkFor (Psi, (T.And (F1, F2), t)) = 
	  (checkFor (Psi, (F1, t)); checkFor (Psi, (F2, t)))
      | checkFor (Psi, (T.FClo (F, t'), t)) =
	  checkFor (Psi, (F, T.comp (t', t)))


    and checkCtx (I.Null) = ()
      | checkCtx (I.Decl (Psi, T.UDec D)) = 
          (checkCtx (Psi); 
	   TypeCheck.checkDec (T.coerceCtx Psi, (D, I.id)))
      | checkCtx (I.Decl (Psi, T.PDec (_, F))) =
	  (checkCtx (Psi);
	   checkFor (Psi, (F, T.id)))


    (* checkSub (Psi, t, Psi') = () 
 
       Invariant
       If Psi |- t: Psi' then checkSub terminates with ()
       otherwise exception Error is raised 
    *)

    and checkSub (I.Null, T.Shift 0, I.Null) = ()
      | checkSub (I.Decl (G, D), T.Shift k, I.Null) = 
	if k > 0 
	then checkSub (G, T.Shift (k-1), I.Null)
	else raise Error "Sub is not well typed!"
      | checkSub (G, T.Shift k, G') = checkSub (G, T.Dot (T.Idx (k+1), T.Shift (k+1)), G')
      | checkSub (G, T.Dot (T.Idx k, s'), I.Decl (G', (T.UDec (I.Dec (_, A))))) =
	let 
	    val _ = checkSub (G, s', G')
	    val T.UDec (I.Dec (_, A')) = T.ctxDec (G, k)
	in
	    if Conv.conv ((A', I.id), (A, T.coerceSub(s'))) then ()
	    else raise Error "Sub isn't well typed!"
	end
      | checkSub (G, T.Dot (T.Idx k, s'), I.Decl (G', T.UDec (I.BDec(l, (_, s))))) = 
	let 
	    val _ = checkSub (G, s', G')
	    val T.UDec (I.BDec(l1, (_, s1))) = T.ctxDec (G, k)
	in
	    if (l<> l1) then raise Error "Sub isn't well typed!"
	    else
		if Conv.convSub (I.comp (s, T.coerceSub(s')), s1)
		then ()
		else raise Error "Sub isn't well typed!"
	end
      | checkSub (G, T.Dot (T.Idx k, s), I.Decl (G', T.PDec(_, F'))) = 
	let 
	    val _ = checkSub (G, s, G')
	    val T.PDec(_, F1) = T.ctxDec (G, k)
	in
	    convFor (G, (F1, T.id), (F', s))
	end
      | checkSub (G, T.Dot (T.Exp M, s), I.Decl(G', T.UDec (I.Dec (_, A)))) =
	let 
	    val _ = checkSub (G, s, G')
	in
	    TypeCheck.typeCheck (T.coerceCtx G, (M, I.EClo(A, T.coerceSub(s))))
	end
(*      | checkSub (G, T.Dot (T.Block (I.Bidx v), s), I.Decl(G', T.UDec (I.BDec(l2, (_, s2))))) = 
	(* Unexpected in LF level? -- Yu Liao *) (* What does v in I.Bidx v mean??? *)
	let 
 	    val _ = checkSub (G, s, G')
	    val T.UDec (I.BDec(l1, (_, s1))) = T.ctxDec (G, v)
	in
	    if (l1<> l2) then raise Error "Sub isn't well typed!"
	    else
		if Conv.convSub (I.comp (s2, T.coerceSub(s)), s1)
		then ()
		else raise Error "Sub isn't well typed!"
	end*)
      | checkSub (Psi, T.Dot (T.Prg P, t), I.Decl(Psi', T.PDec(_, F'))) =
	let 
	  val _ = chatter 4 (fn () => "$")
	  val _ = checkSub (Psi, t, Psi')
	  val _ = isValue P
	in
	    checkPrg (Psi, (P, (F', t)))
	end
      | checkSub (Psi, T.Dot (T.Block B, t), I.Decl(Psi', T.UDec (I.BDec(l2, (c, s2))))) =
	let 
	  val _ = chatter 4 (fn () => "$")
	  val _ = checkSub (Psi, t, Psi')
					(* Psi |- t : Psi' *)
					(* Psi' |- s2 : SOME variables of c *)
	  val (G, L) = I.constBlock c
					(* Psi |- s2 : G *)
	  val _ = TypeCheck.typeCheckSub (T.coerceCtx Psi', s2, G)
	in
	    checkBlock (Psi, (B, (c, I.comp (s2, T.coerceSub t))))
	end
      | checkSub (Psi, T.Dot _, I.Null) = raise Error "Sub is not well typed"


    and checkBlock (Psi, (I.Bidx v, (c2, s2))) = 
 	let 
	  val T.UDec (I.BDec(l1, (c1, s1))) = T.ctxDec (Psi, v)
	in
	  if (c1 <> c2) then raise Error "Sub isn't well typed!"
	  else if Conv.convSub (s2, s1)  then ()
	       else raise Error "Sub isn't well typed!"
	end
      | checkBlock (Psi, (I.Inst UL, (c2, s2))) = 
	let
	  val (G, L) = I.constBlock c2
					(* Psi |- s2 : G *)
	  val _ = TypeCheck.typeCheckSub (T.coerceCtx Psi, s2, G)
	in
	  checkInst (Psi, UL, (1, L, s2))
	end

   (* Invariant:

      If   Psi |- s2 : Psi'    Psi' |-  Bn ... Bm
      and  Psi |- s : [cn :An ... cm:Am]
      and  Ai == Bi n<= i<=m
      then checkInst returns () otherwise an exception is raised.
   *)
   and checkInst (Psi, nil, (_, nil, _)) = ()
     | checkInst (Psi, U :: UL, (n, D :: L, s2)) = 
       let
	 val G = T.coerceCtx Psi
	 val I.Dec (_ ,V) = I.decSub (D, s2)
	 val _ = TypeCheck.typeCheck (G, (U, V))
       in
	 checkInst (Psi, UL, (n+1, L, I.dot1 s2))
       end

	

    and isValue (T.Lam _) = ()
      | isValue (T.PairExp (M, P)) = isValue P
      | isValue (T.PairBlock _ ) = ()
      | isValue (T.PairPrg (P1, P2)) = (isValue P1; isValue P2)
      | isValue T.Unit = ()
      | isValue (T.Root ((T.Const lemma), T.Nil)) = (* could lemma be a VALUE? -- Yu Liao *)
	( case (T.lemmaLookup lemma) of 
	      T.ForDec _ => raise Error "Lemma isn't a value"
	    | T.ValDec(_,P,_) => isValue P )

      | isValue (T.Root ((T.Var k), T.Nil)) = ()
      | isValue (T.Rec _) = ()

      (* ABP 1/23/03 *)
      | isValue (T.EVar _) = raise Error "It is an EVar"

      | isValue _ = raise Error "P isn't Value!"


    fun check (Psi, (P, F)) = checkPrg (Psi, (P, (F, T.id)))



  in
  val checkPrg = fn (Psi, (P, F)) => checkPrg (Psi, (P, (F, T.id)))
  val checkSub = checkSub
  val checkFor = fn (Psi, F) => checkFor (Psi, (F, T.id))
  val checkCtx = checkCtx
  end
end	      
