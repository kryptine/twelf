(* Type checking for Tomega *)
(* Author: Carsten Schuermann *)
(* Modified: Yu Liao *)

functor TomegaTypeCheck
  (structure IntSyn' : INTSYN
   structure Tomega' : TOMEGA
     sharing Tomega'.IntSyn = IntSyn'
   structure Abstract : ABSTRACT
     sharing Abstract.IntSyn = IntSyn'
   structure TypeCheck : TYPECHECK
     sharing TypeCheck.IntSyn = IntSyn'
   structure Conv : CONV
     sharing Conv.IntSyn = IntSyn'
   structure Normalize : NORMALIZE
     sharing Normalize.IntSyn = IntSyn'
     sharing Normalize.Tomega = Tomega'
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn'
   structure Print : PRINT
     sharing Print.IntSyn = IntSyn'
   structure TomegaPrint : TOMEGAPRINT
     sharing TomegaPrint.IntSyn = IntSyn'
     sharing TomegaPrint.Tomega = Tomega'
   structure Subordinate : SUBORDINATE
     sharing Subordinate.IntSyn = IntSyn'
   structure Weaken : WEAKEN
     sharing Weaken.IntSyn = IntSyn') : TOMEGATYPECHECK= 
struct
  structure IntSyn = IntSyn'
  structure Tomega = Tomega'

  exception Error of string 
  
  local 
    structure I = IntSyn'
    structure T = Tomega


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
    and inferSpine (G, (T.Nil, s), (F2, s2)) = (F2, s2)
      | inferSpine (G, (T.AppExp (M, S), s), (T.All (T.UDec(I.Dec(_, A2)), F2), s2)) =
	let 
	    val _ = TypeCheck.typeCheck (T.coerceCtx(G), (I.EClo(M, T.coerceSub(s)), I.EClo(A2, T.coerceSub(s2))))
	in 
	    inferSpine(G, (S, s), (F2, T.Dot(T.Exp(M), s2)))
	end
      | inferSpine (G, (T.AppBlock (I.Bidx v, S), s), (T.All (T.UDec (I.BDec (_, (l2, s2'))), F2), s2)) =
	let 
	    val T.UDec (I.BDec(_, (l, s')))= T.ctxDec(G, v)
	    val (G', _) = I.conDecBlock (I.sgnLookup l)
	    val _ = if (l<>l2) then raise Error("Type mismatch") else ()
	    val _ = convSub (G, T.comp(T.embedSub s', s), T.comp(T.embedSub s2', s2), T.revCoerceCtx(G')) 
	in 
	    inferSpine (G, (S, s), (F2, T.Dot(T.Block(I.Bidx v), s2)))
	end
      | inferSpine (G, (T.AppPrg (P, S), s), (T.All (T.PDec (_, F2'), F2), s2)) =
	let 
	    val _ = checkProg(G, ((P, s), (F2', s2)))
	in 
	    inferSpine (G, (S, s), (F2, s2))
	end
      | inferSpine (G, (T.SClo(S, s'), s), Fs) = inferSpine(G, (S, T.comp(s', s)), Fs)
      | inferSpine (G, _, _) = raise Error "applied, but not of function type."
	

    (* checkProg (Psi, (P, t1), F) = ()
     
       Invariant:
       If   Psi  |- t1 : Psi1 
       and  Psi1 |- P : F'
       and  Psi  |- F for     (F in normal form)
       then checkProg returns () iff F'[t1] == F[id]
    *)
    and checkProg (Psi, ((T.Root (H, S), t), (F2, t2))) =
	let
	  val H' = normalizeHead  (H, t)
	  val F = inferCon (Psi, H')
	  val (F1, t1) = inferSpine (Psi, (S, t), (F, T.id))
	  val _ = convFor (Psi, Normalize.normalizeFor (F1, t1), Normalize.normalizeFor (F2, t2))
	in 
	  ()
	end
      | checkProg (Psi, ((T.Lam (D as T.PDec (x, F1), P), t1), (T.All (T.PDec (x', F1'), F2), t2))) = 
	let 
	  val _ = chatter 4 (fn () => "[lam[p]")
	    val _ = isFor (Psi, T.FClo(F1, t1))
	    val _ = isFor (Psi, F1')
	    val _ = convFor (Psi, Normalize.normalizeFor (F1, t1), Normalize.normalizeFor (F1', t2)) 
	  val _ = chatter 4 (fn () => "]")
	in 
	    checkProg (I.Decl (Psi, T.decSub(D, t1)), ((P, T.dot1 t1), (F2, T.dot1 t2)))
	end

      | checkProg (Psi, ((T.Lam (T.UDec D, P), t1), (T.All (T.UDec D', F), t2))) =
	let 
	  val _ = chatter 4 (fn () => "[lam[u]")
	  val _ = Conv.convDec ((D, T.coerceSub t1), (D', T.coerceSub t2))
	  val _ = chatter 4 (fn () => "]")
	in  
	    checkProg(I.Decl(Psi , T.UDec D'), ((P, T.dot1 t1), (F, T.dot1 t2)))
	end
(*		   
      | checkProg(G, ((T.Lam (T.UDec (I.BDec(name, (l, s'))), P), s), (T.All(T.UDec (I.BDec(_, (l2, s2'))), F2), s2))) =
	let
	    val _ = if (l <> l2) then raise Error("Type mismatch") else ()         
	    val (G', _) = I.conDecBlock (I.sgnLookup l)
	    val _ = convSub (G, T.comp(T.embedSub s', s), T.comp(T.embedSub s2', s2), T.revCoerceCtx(G')) 
	in 
	    checkProg(I.Decl(G, T.UDec (I.BDec(name, (l, I.comp(s', T.coerceSub s))))), ((P, T.dot1 s), (F2, T.dot1 s2)))
	end
      | checkProg(G, ((T.Lam(T.UDec(D as I.Dec(x, A)), P), s), (T.All(T.UDec(I.Dec(x2, A2)), F2), s2))) =
	let 
	  val _ = chatter 4 (fn () => "[lam[u]")
	    val _ = TypeCheck.checkDec(T.coerceCtx(G), (D, T.coerceSub(s)))
	    val _ = Conv.conv((A, T.coerceSub(s)), (A2, T.coerceSub(s2)))
	  val _ = chatter 4 (fn () => "]")
	in  
	    checkProg(I.Decl(G, T.UDec(I.decSub(D, T.coerceSub(s)))), ((P, T.dot1 s), (F2, T.dot1 s2)))
	end *)
      | checkProg (G, ((T.PairExp (M, P), s), (T.Ex(I.Dec(x, A), F2), s2))) =
	let 
	    val _ = TypeCheck.typeCheck(T.coerceCtx(G), (I.EClo(M, T.coerceSub(s)), I.EClo(A, T.coerceSub(s2))))
	in 
	    checkProg(G, ((P, s), (F2, T.Dot(T.Exp(I.EClo(M, T.coerceSub(s))), s2))))
	end
      | checkProg(G, ((T.PairBlock(I.Bidx v, P), s), (T.Ex(I.BDec(_, (l2, s2')), F2), s2))) =
	let
	    val T.UDec (I.BDec(_, (l, s'))) = T.ctxDec(G, v)
	    val (G', _) = I.conDecBlock (I.sgnLookup l)
	    val _ = if (l<>l2) then raise Error("Type mismatch") else ()
	    val _ = convSub (G, T.comp(T.embedSub s', s), T.comp(T.embedSub(s2'), s2), T.revCoerceCtx(G'))  
	in 
	    checkProg(G, ((P, s), (F2, T.Dot(T.Block(I.blockSub(I.Bidx v, T.coerceSub(s))), s2)))) (* -- Yu Liao: Why Block Closure isn't used any more? *)
	end
      | checkProg(G, ((T.PairPrg (P1, P2), s), (T.And( F1, F2), s'))) =
	( checkProg(G, ((P1, s), (F1, s'))); checkProg(G, ((P2, s), (F2, s'))) )
      | checkProg (_, ((T.Unit, _), (T.True, _))) = ()
(*      | checkProg (G, ((T.Redex (P, T.Nil), s), Fs)) = checkProg (G, ((P, s), Fs)) *)
(*      | checkProg (G, ((T.Redex (P, T.AppExp(M, S)), s), (F2, s2))) =  -- Yu Liao *)
      | checkProg (G, ((T.Case (T.Cases nil), s), (F2, s2))) = ()
      | checkProg (G, ((T.Case (T.Cases ((G', s', P) :: tailCases)), s), (F2, s2))) =
	let 
	  val _ = chatter 4 (fn () => "[case")
	  val _ = isSub(G', T.comp(s, s'), G)
	  val _ = checkProg (G', ((P, s), (F2, T.comp(s2, s'))))
	  val _ = chatter 4 (fn () => "]\n")
	in 
	    checkProg (G, ((T.Case (T.Cases tailCases), s), (F2, s2)))
	end 
      | checkProg (G, ((T.Rec (FDec as T.PDec (x, F), P), s), (F2, s2))) =
	let 
	  val _ = chatter 4 (fn () => "[rec")
	  val _ = convFor(G, Normalize.normalizeFor (F, s), Normalize.normalizeFor (F2, s2))
	  val _ = chatter 4 (fn () => "]\n")
	in 
	    checkProg(I.Decl(G, FDec), ((P, T.dot1(s)), (F2, s2)))
	end
      | checkProg (G, ((T.PClo(P1,s1), s11), (F2, s2))) = checkProg (G, ((P1, T.comp(s1, s11)), (F2, s2)))
      | checkProg (G, ((T.Let(F1Dec as T.PDec(_, F1), P1, P2), s1), (F2, s2))) = 
	let 
	    val _ = checkProg (G, ((P1, s1), (F1, s1)))
	in
	    checkProg(I.Decl(G, F1Dec), ((P2, T.dot1(s1)), (F2, s2)))
	end

    and  inferLemma lemma = 
	( case (T.lemmaLookup lemma) of 
	     T.ForDec (_, F) => F |
	     T.ValDec (_,_,F) => F)

	    
    and convFor(_, T.True, T.True) = ()
      | convFor(Psi, T.All (D as T.UDec( I.Dec (_, A1)), F1), 
		     T.All (     T.UDec( I.Dec (_, A2)), F2)) =
	let
	  val G = T.coerceCtx (Psi)
	  val _ = Conv.conv((A1, I.id), (A2, I.id))
	  val _ = TypeCheck.typeCheck(G, (A1, I.Uni I.Type))
	  val _ = TypeCheck.typeCheck(G, (A2, I.Uni I.Type))
	in
	  convFor (I.Decl(Psi, D), F1, F2)
	end
      | convFor(G, T.All (D as T.UDec (I.BDec(_, (l1, s1))), F1), 
		   T.All(T.UDec (I.BDec(_, (l2, s2))), F2)) =
	let 
	    val _ = if l1 <> l2 then raise Error "Formula not equilavent" else ()
	    val (G', _) = I.conDecBlock (I.sgnLookup l1)
	    val _ = convSub (G, T.embedSub s1, T.embedSub s2, T.revCoerceCtx(G'))  
	in
	    convFor (I.Decl (G, D), F1, F2)
	end
      | convFor(Psi, T.Ex (D as I.Dec (_, A1), F1), 
		     T.Ex (     I.Dec (_, A2), F2)) =
	let
	  val G = T.coerceCtx (Psi)
	  val _ = Conv.conv ((A1, I.id), (A2, I.id))
	  val _ = TypeCheck.typeCheck(G, (A1, I.Uni I.Type))
	  val _ = TypeCheck.typeCheck(G, (A2, I.Uni I.Type))
	in
	    convFor (I.Decl(Psi, T.UDec D), F1, F2)
	end
      | convFor(G, T.Ex(D as I.BDec(name, (l1, s1)), F1), T.Ex(I.BDec(_, (l2, s2)), F2)) =
	let 
	    val _ = if l1 <> l2 then raise Error "Formula not equilavent" else ()
	    val (G', _) = I.conDecBlock (I.sgnLookup l1)
	    val _ = convSub (G, T.revCoerceSub(s1), T.revCoerceSub(s2), T.revCoerceCtx(G'))
	in
	    convFor(I.Decl(G, T.UDec (I.BDec (name, (l1, s1)))), F1, F2)
	end
      | convFor(Psi, T.And(F1, F1'), T.And(F2, F2')) =
	let
	  val _ = convFor(Psi, F1, F2)
	  val _ = convFor(Psi, F1', F2') 
	in 
	  ()
	end
      | convFor(G, T.All(D as T.PDec(_, F1), F1'), T.All(T.PDec(_, F2), F2')) =
	(convFor(G, F1, F2); convFor(I.Decl (G, D), F1', F2')) 
      | convFor _ = raise Error "Typecheck error"

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
    and isFor (G, F)= ()


    (* isSub (Psi, t, Psi') = () 
 
       Invariant
       If Psi |- t: Psi' then isSub terminates with ()
       otherwise exception Error is raised 
    *)

    and isSub (I.Null, T.Shift 0, I.Null) = ()
      | isSub (I.Decl (G, D), T.Shift k, I.Null) = 
	if k >0 
	then isSub (G, T.Shift (k-1), I.Null)
	else raise Error "Sub is not well typed!"
      | isSub (G, T.Shift k, G') = isSub (G, T.Dot (T.Idx (k+1), T.Shift (k+1)), G')
      | isSub (G, T.Dot (T.Idx k, s'), I.Decl (G', (T.UDec (I.Dec (_, A))))) =
	let 
	    val _ = isSub (G, s', G')
	    val T.UDec (I.Dec (_, A')) = T.ctxDec (G, k)
	in
	    if Conv.conv ((A', I.id), (A, T.coerceSub(s'))) then ()
	    else raise Error "Sub isn't well typed!"
	end
      | isSub (G, T.Dot (T.Idx k, s'), I.Decl (G', T.UDec (I.BDec(l, (_, s))))) = 
	let 
	    val _ = isSub (G, s', G')
	    val T.UDec (I.BDec(l1, (_, s1))) = T.ctxDec (G, k)
	in
	    if (l<> l1) then raise Error "Sub isn't well typed!"
	    else
		if Conv.convSub (I.comp (s, T.coerceSub(s')), s1)
		then ()
		else raise Error "Sub isn't well typed!"
	end
      | isSub (G, T.Dot (T.Idx k, s), I.Decl (G', T.PDec(_, F'))) = 
	let 
	    val _ = isSub (G, s, G')
	    val T.PDec(_, F1) = T.ctxDec (G, k)
	in
	    convFor (G, Normalize.normalizeFor (F1, T.id), Normalize.normalizeFor (F', s))
	end
      | isSub (G, T.Dot (T.Exp M, s), I.Decl(G', T.UDec (I.Dec (_, A)))) =
	let 
	    val _ = isSub (G, s, G')
	in
	    TypeCheck.typeCheck (T.coerceCtx G, (M, I.EClo(A, T.coerceSub(s))))
	end
      | isSub (G, T.Dot (T.Block (I.Bidx v), s), I.Decl(G', T.UDec (I.BDec(l2, (_, s2))))) = (* Unexpected in LF level? -- Yu Liao *) (* What does v in I.Bidx v mean??? *)
	let 
	    val _ = isSub (G, s, G')
	    val T.UDec (I.BDec(l1, (_, s1))) = T.ctxDec (G, v)
	in
	    if (l1<> l2) then raise Error "Sub isn't well typed!"
	    else
		if Conv.convSub (I.comp (s2, T.coerceSub(s)), s1)
		then ()
		else raise Error "Sub isn't well typed!"
	end
      | isSub (Psi, T.Dot (T.Prg P, t), I.Decl(Psi', T.PDec(_, F'))) =
	let 
	  val _ = isSub (Psi, t, Psi')
	  val _ = isValue P
	in
	    checkProg (Psi, ((P, T.id), (F', t)))
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
      | isValue _ = raise Error "P isn't Value!"


    fun check (P, F) = checkProg (I.Null, ((P, T.id), (F, T.id)))

  in
  val check = check
  val isFor = isFor
  end
end	      
