(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)

functor Converter 
  (structure Global : GLOBAL
   structure IntSyn' : INTSYN
   structure Tomega' : TOMEGA
     sharing Tomega'.IntSyn = IntSyn'
   structure Abstract : ABSTRACT
     sharing Abstract.IntSyn = IntSyn'
   structure ModeSyn : MODESYN
     sharing ModeSyn.IntSyn = IntSyn'
   structure Names : NAMES
     sharing Names.IntSyn = IntSyn'
   structure Unify : UNIFY
     sharing Unify.IntSyn = IntSyn'
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn'
   structure WorldSyn : WORLDSYN
     sharing WorldSyn.IntSyn = IntSyn'
     sharing WorldSyn.Tomega = Tomega'
   structure Worldify : WORLDIFY
     sharing Worldify.IntSyn = IntSyn'
     sharing Worldify.Tomega = Tomega'
   structure Subordinate : SUBORDINATE
     sharing Subordinate.IntSyn = IntSyn'
   structure TypeCheck : TYPECHECK
     sharing TypeCheck.IntSyn = IntSyn')
     : CONVERTER = 
struct
  structure IntSyn = IntSyn'
  structure Tomega = Tomega'

  exception Error of string 

  local
    structure T = Tomega
    structure I = IntSyn 
    structure M = ModeSyn
    structure S = Subordinate    
    structure A = Abstract

    (* strengthenExp (U, s) = U' 
     
       Invariant:
       If   G |- s : G'
       and  G |- U : V
       then G' |- U' = U[s^-1] : V [s^-1] 
    *)
    fun strengthenExp (U, s) = Whnf.normalize (Whnf.cloInv (U, s), I.id)

    fun strengthenSub (s, t) = Whnf.compInv (s, t)

    (* strengthenDec (x:V, s) = x:V'
     
       Invariant:
       If   G |- s : G'
       and  G |- V : L
       then G' |- V' = V[s^-1] : L
    *)
    fun strengthenDec (I.Dec (name, V), s) = I.Dec (name, strengthenExp (V, s))
      | strengthenDec (I.BDec (name, (L, t)), s) = 
          I.BDec (name, (L, strengthenSub (t, s)))

    (* strengthenCtx (G, s) = (G', s')
     
       If   G0 |- G ctx
       and  G0 |- s : G1 
       then G1 |- G' = G[s^-1] ctx
       and  G0 |- s' : G1, G'  
    *)
    fun strengthenCtx (I.Null, s) = (I.Null, s)
      | strengthenCtx (I.Decl (G, D), s) = 
        let 
	  val (G', s') = strengthenCtx (G, s)
	in
	  (I.Decl (G', strengthenDec (D, s')), I.dot1 s')
	end


    (* strengthenFor (F, s) = F'
     
       If   Psi0 |- F for
       and  Psi0 |- s :: Psi1 
       then Psi1 |- F' = F[s^-1] ctx
    *)
    fun strengthenFor (T.True, s) = T.True
      | strengthenFor (T.And (F1, F2), s) = 
          T.And (strengthenFor (F1, s), strengthenFor (F2, s))
      | strengthenFor (T.All (T.UDec D, F), s) =
	  T.All (T.UDec (strengthenDec (D, s)), strengthenFor (F, I.dot1 s))
      | strengthenFor (T.Ex (D, F), s) =
	  T.Ex (strengthenDec (D, s), strengthenFor (F, I.dot1 s))


    fun strengthenSpine (I.Nil, t) = I.Nil
      | strengthenSpine (I.App (U, S), t) = I.App (strengthenExp (U, t), strengthenSpine (S, t))



    (* strengthenPsi (Psi, s) = (Psi', s')
     
       If   Psi0 |- Psi ctx
       and  Psi0 |- s :: Psi1 
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' :: Psi1, Psi'  
    *)
    fun strengthenPsi (I.Null, s) = (I.Null, s)
      | strengthenPsi (I.Decl (Psi, T.UDec D), s) = 
        let 
	  val (Psi', s') = strengthenPsi (Psi, s)
	in
	  (I.Decl (Psi', T.UDec (strengthenDec (D, s'))), I.dot1 s')
	end
      | strengthenPsi (I.Decl (Psi, T.PDec (name, F)), s) = 
        let 
	  val (Psi', s') = strengthenPsi (Psi, s)
	in
	  (I.Decl (Psi', T.PDec (name, strengthenFor (F, s'))), I.dot1 s')
	end


    (* strengthenPsi' (Psi, s) = (Psi', s')
     
       If   Psi0 |- Psi ctx
       and  Psi0 |- s : Psi1 
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'  weakening substitution
    *)
    fun strengthenPsi' (nil, s) = (nil, s)
      | strengthenPsi' (T.UDec D :: Psi, s) = 
        let 
	  val D' = strengthenDec (D, s) 
	  val s' = I.dot1 s
	  val (Psi'', s'') = strengthenPsi' (Psi, s')
	in
	  (T.UDec D' :: Psi'', s'')
	end
(*      | strengthenPsi' (F.Block (F.CtxBlock (l, G)) :: Psi, s) =
	let 
	  val (G', s') = strengthenCtx (G, s)
	  val (Psi'', s'') = strengthenPsi' (Psi, s')
	in 
	  (F.Block (F.CtxBlock (l, G')) :: Psi'', s'')
	end
*)

    (* ctxSub (G, s) = (G', s')
     
       Invariant:
       if   Psi |- G ctx
       and  Psi' |- s : Psi
       then Psi' |- G' ctx
       and  Psi', G' |- s' : G
       and  G' = G [s],  declarationwise defined
    *)
    fun ctxSub (I.Null, s) = (I.Null, s)
      | ctxSub (I.Decl (G, D), s) =
        let
	  val (G', s') = ctxSub (G, s)
	in
	  (I.Decl (G', I.decSub (D, s')), I.dot1 s)
	end


    fun convertOneFor cid =
      let
	val V  = case I.sgnLookup cid 
	           of I.ConDec (name, _, _, _, V, I.Kind) => V
	            | _ => raise Error "Type Constant declaration expected"
	val mS = case M.modeLookup cid
	           of NONE => raise Error "Mode declaration expected"
	            | SOME mS => mS

	(* convertFor' (V, mS, w1, w2, n) = (F', F'')

	   Invariant:
	   If   G |- V = {{G'}} type :kind 
	   and  G |- w1 : G+
	   and  G+, G'+, G- |- w2 : G
	   and  G+, G'+, G- |- ^n : G+
	   and  mS is a spine for G'
	   then F'  is a formula excepting a another formula as argument s.t.
	        If G+, G'+ |- F formula,
		then . |- F' F formula 
           and  G+, G'+ |- F'' formula
	*)
	fun convertFor' (I.Pi ((D, _), V), M.Mapp (M.Marg (M.Plus, _), mS), w1, w2, n) =
            let
	      val (F', F'') = convertFor' (V, mS, I.dot1 w1, I.Dot (I.Idx n, w2), n-1)
	    in
	      (fn F => T.All (T.UDec (strengthenDec (D, w1)), F' F), F'')
	    end
	  | convertFor' (I.Pi ((D, _), V), M.Mapp (M.Marg (M.Minus, _), mS), w1, w2, n) =
            let
	      val (F', F'') = convertFor' (V, mS, I.comp (w1, I.shift), I.dot1 w2, n+1)
	    in
	      (F', T.Ex (I.decSub (D, w2), F''))
	    end
	  | convertFor' (I.Uni I.Type, M.Mnil, _, _, _) = 
              (fn F => F, T.True)
	  | convertFor' _ = raise Error "type family must be +/- moded"

	(* shiftPlus (mS) = s'
	 
	 Invariant:
	 s' = ^(# of +'s in mS)
	 *)
	    
	fun shiftPlus mS = 
	  let
	    fun shiftPlus' (M.Mnil, n) = n
	      | shiftPlus' (M.Mapp (M.Marg (M.Plus, _), mS'), n) =
	          shiftPlus' (mS', n+1)
	      | shiftPlus' (M.Mapp (M.Marg (M.Minus, _), mS'), n) =
		  shiftPlus' (mS', n)
	  in
	    shiftPlus' (mS, 0)
	  end
	
	val n = shiftPlus mS
	val (F, F') = convertFor' (V, mS, I.id, I.Shift n, n)
      in 
	F F'
      end


    (* createIHCtx (Psi, L) = (Psi', P', F')

       Invariant:
       If   L is a list of type families
       and  Psi is a context
       then Psi' extends Psi' by declarations in L
       and  F' is the conjunction of the formuals 
	    that corresponds to each type family in L
       and  Psi' |- P' in F'
     *)
    fun createIHCtx (Psi, nil) = raise Error "Empty theorem"
      | createIHCtx (Psi, [a]) = 
        let 
	  val F = convertOneFor a
	in
	  (I.Decl (I.Null, T.PDec (NONE, F)),  T.Root (T.Var 1, T.Nil), F)
	end
      | createIHCtx (Psi, a :: L) = 
	let
	  val F = convertOneFor a
	  val (Psi', P', F') = createIHCtx (I.Decl (Psi,  T.PDec (NONE, F)), L)
	in
	  (Psi', T.PairPrg (T.Root (T.Var (1+length L), T.Nil), P'), T.And (F, F'))
	end


    fun convertFor L = 
      let 
	val (Psi', P', F') = createIHCtx (I.Null, L)
      in
	F'
      end

    (* occursInExpN (k, U) = B, 

       Invariant:
       If    U in nf 
       then  B iff k occurs in U
    *)
    fun occursInExpN (k, I.Uni _) = false
      | occursInExpN (k, I.Pi (DP, V)) = occursInDecP (k, DP) orelse occursInExpN (k+1, V)
      | occursInExpN (k, I.Root (H, S)) = occursInHead (k, H) orelse occursInSpine (k, S)
      | occursInExpN (k, I.Lam (D, V)) = occursInDec (k, D) orelse occursInExpN (k+1, V)
      | occursInExpN (k, I.FgnExp (cs, ops)) = occursInExpN (k, Whnf.normalize (#toInternal(ops) (), I.id))
    (* no case for Redex, EVar, EClo *)


    and occursInHead (k, I.BVar (k')) = (k = k')
      | occursInHead (k, I.Const _) = false
      | occursInHead (k, I.Def _) = false
      | occursInHead (k, I.FgnConst _) = false
      (* no case for FVar *)

    and occursInSpine (_, I.Nil) = false
      | occursInSpine (k, I.App (U, S)) = occursInExpN (k, U) orelse occursInSpine (k, S)
      (* no case for SClo *)

    and occursInDec (k, I.Dec (_, V)) = occursInExpN (k, V)
    and occursInDecP (k, (D, _)) = occursInDec (k, D)

    and occursInExp (k, U) = occursInExpN (k, Whnf.normalize (U, I.id))

    (* dot1inv w = w'

       Invariant:
       If   G, A |- w : G', A
       then G |- w' : G'
       and  w = 1.w' o ^
    *) 
    fun dot1inv (w) = strengthenSub (I.comp (I.shift, w), I.shift)

    (* shiftinv (w) = w'
     
       Invariant:
       If   G, A |- w : G'
       and  1 does not occur in w
       then w  = w' o ^
    *)
    fun shiftinv (w) = strengthenSub (w, I.shift)

    fun peel w = 
      if (I.bvarSub (1, w) = I.Idx 1) then dot1inv w else shiftinv w

    fun peeln (0, w) = w
      | peeln (n, w) = peeln (n-1, peel w)
    


    (* domain (G2, w) = n'
     
       Invariant: 
       If   G2 |- w: G1   and w weakening substitution
       then n' = |G1|
    *)
    fun domain (G, I.Dot (I.Idx _, s)) = domain (G, s) + 1
      | domain (I.Null, I.Shift 0) = 0
      | domain (G as I.Decl _, I.Shift 0) = domain (G, I.Dot (I.Idx 1, I.Shift 1)) 
      | domain (I.Decl (G, _), I.Shift n) = domain (G, I.Shift (n-1))


    (* strengthen (Psi, (a, S), w, m) = (Psi', w')       
     
       This function traverses the spine, and finds 
       all variables in a position input/output position
       (hence strenghten might not be a good name for it, because it is to general.)

       Invariant:
       If   |- Psi ctx
       and  |- Psi1 ctx      where Psi1 is a subcontext of Psi
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} > type
       and  Psi |- w : Psi1 
       and  m mode
       then |- Psi' ctx
       and  Psi |- w' : Psi'
       where Psi' extends Psi1 (but is a subset of Psi?)
    *)

    fun strengthen (Psi, (a, S), w, m) =
      let 
	val mS = case M.modeLookup a
	           of NONE => raise Error "Mode declaration expected"
		    | SOME mS => mS

	fun args (I.Nil, M.Mnil) = nil
	  | args (I.App (U, S'), M.Mapp (M.Marg (m', _), mS)) =
	      let 
		val L = args (S', mS)
	      in
		(case M.modeEqual (m, m') 
		   of true => U :: L
		    | false => L)
	      end
 		   

	fun strengthenArgs (nil, s) =  nil
	  | strengthenArgs (U :: L, s) = 
	      strengthenExp (U, s) :: strengthenArgs (L, s)

	fun occursInArgs (n, nil) = false
	  | occursInArgs (n, U :: L) = 
	    (occursInExp (n, U) orelse occursInArgs (n, L))
	  
	fun occursInPsi (n, (nil, L)) = 
	      occursInArgs (n, L)
	  | occursInPsi (n, (T.UDec (I.Dec (_, V)) :: Psi1, L)) = 
              occursInExp (n, V) orelse occursInPsi (n+1, (Psi1, L))
(*	  | occursInPsi (n, (F.Block (F.CtxBlock (l, G)) :: Psi1, L)) =
	      occursInG (n, G, fn n' => occursInPsi (n', (Psi1, L)))
*)	  
	and occursInG (n, I.Null, k) = k n
	  | occursInG (n, I.Decl (G, I.Dec (_, V)), k) =
	      occursInG (n, G, fn n' => occursInExp (n', V) orelse k (n'+ 1))

	fun occursBlock (G, (Psi2, L)) =
	  let 
	    fun occursBlock (I.Null, n) = false
	      | occursBlock (I.Decl (G, D), n) = 
	          occursInPsi (n, (Psi2, L)) orelse occursBlock (G, n+1)
	  in
	    occursBlock (G, 1)
	  end

	(* testBlock (G, (bw, w1)) = (bw', w')

	   Invariant:
	   If   |- G ctx
	   and  |- G1 ctx
	   and  |- G2 ctx
	   and  G1 |- w1 : G2, G
	   and  bw is a boolean value
	   then there ex. a G1'
	   s.t. |- G1' ctx
	   and  G1' |- w' : G2
	   and  bw' = bw or (G1 =/= G1')
	 *)
	fun inBlock (I.Null, (bw, w1)) = (bw, w1)
	  | inBlock (I.Decl (G, D), (bw, w1)) = 
	    if I.bvarSub (1, w1) = I.Idx 1 then
	      inBlock (G, (true, dot1inv w1))
	    else inBlock (G, (bw, strengthenSub (w1, I.shift)))
	  
	  


	fun blockSub (I.Null, w) = (I.Null, w) 
	  | blockSub (I.Decl (G, I.Dec (name, V)), w) =
	    let 
	      val (G', w') = blockSub (G, w)
	      val V' = strengthenExp (V, w')
	    in 
	      (I.Decl (G', I.Dec (name, V')), I.dot1 w')
	    end
	    
        (* strengthen' (Psi1, Psi2, S, w1) =  (Psi', w')
	 
	   Invariant: 
	   If   |- Psi1 ctx
	   and  Psi1 |- Psi2 ctx      (Psi2 is a list to maintain order)
	   and  |- Psi3 ctx
	   and  Psi1 |- w1 : Psi3     where w1 is a weakening substitution
	   and  Psi1, Psi2 |- S : V1 > V2
	   then |- Psi' ctx
	   and  Psi1 |- w' : Psi'     where w' is a weakening substitution
           where Psi3 < Psi' < Psi1   (Psi' contains all variables of Psi3
	                               and all variables occuring in m
				       position in S)
	*)
      	fun strengthen' (I.Null, Psi2, L, w1 (* =  I.id *)) = (I.Null, I.id)    
	  | strengthen' (I.Decl (Psi1, LD as T.UDec (I.Dec (name, V))), Psi2, L, w1) =
	    let 
	      val (bw, w1') = if (I.bvarSub (1, w1) = I.Idx 1) then (true, dot1inv w1)
			      else (false, strengthenSub (w1, I.shift))
	    in
	      if bw orelse occursInPsi (1, (Psi2, L)) then
		let 
		  val (Psi1', w') = strengthen' (Psi1, LD :: Psi2, L, w1')
		  val V' = strengthenExp (V, w')
		in
		  (I.Decl (Psi1', T.UDec (I.Dec (name, V'))), I.dot1 w')
		end	    
	      else
		let 
		  val w2 = I.shift
		  val (Psi2', w2') = strengthenPsi' (Psi2, w2)
		  val L' = strengthenArgs (L, w2')
		  val (Psi1'', w') = strengthen' (Psi1, Psi2', L', w1')
		in
		  (Psi1'', I.comp (w', I.shift))
		end
	    end
	  | strengthen' (I.Decl (Psi1, LD as T.PDec (name, F)), Psi2, L, w1) =
	    let 
	      val (bw, w1') = if (I.bvarSub (1, w1) = I.Idx 1) then (true, dot1inv w1)
			      else (false, strengthenSub (w1, I.shift))
	      val (Psi1', w') = strengthen' (Psi1, LD :: Psi2, L, w1')
	      val F' = strengthenFor (F, w')
	    in
	      (I.Decl (Psi1', T.PDec (name, F')), I.dot1 w')
	    end	    
	  

(*	  | strengthen' (I.Decl (Psi1, LD as F.Block (F.CtxBlock (name, G))), Psi2, L, w1) =
	    let 
	      val (bw, w1') = inBlock (G, (false, w1))
	    in
	      if bw orelse occursBlock (G, (Psi2, L)) 
		then 
		  let 
		    val (Psi1', w') = strengthen' (Psi1, LD :: Psi2, L, w1')
                    val (G'', w'') = blockSub (G, w')  
		  in
		    (I.Decl (Psi1', F.Block (F.CtxBlock (name, G''))), w'')
		  end
	      else 
		let
		  val w2 = I.Shift (I.ctxLength G)
		  val (Psi2', w2') = strengthenPsi' (Psi2, w2)
		  val L' = strengthenArgs (L, w2')
		in
		  strengthen' (Psi1, Psi2', L', w1')
		end
	    end
*)

      in
	strengthen' (Psi, nil, args (S, mS), w)
      end


    fun recursion L =
        let
	  val (Psi, P, F) = createIHCtx (I.Null, L)
	  val t = T.Dot (T.Prg P, T.Shift (I.ctxLength Psi))

	  fun name [a] = I.conDecName (I.sgnLookup a)
	    | name (a :: L) = I.conDecName (I.sgnLookup a) ^ "/" ^ (name L)
	in
	  (Psi, fn p => T.Rec (T.PDec (SOME (name L), F), 
			       T.Case (T.Cases [(Psi, t, p)])))
	end


    fun lookupIH (Psi, L, a) = 
        let
	  fun lookupIH' (b::L, a, k)= 
	      if a = b then k
	      else lookupIH' (L, a, k-1)
	in
	  lookupIH' (L, a, I.ctxLength Psi)
	end


    (* createSub (Psi, L) = t'
     
       Invariant:
       If  |- Psi = Psi0, Psi1 ctx
       and Psi0 contains all declarations for invariants in L
       and |Psi0| = n
       and |L| = k
       and n = k + m - 1
       then Psi |- t' = m, m+1 ... n. ^n :  Psi0
    *)
    fun createIHSub (Psi, L) =
         T.Shift (I.ctxLength Psi - List.length L)

    (* abstract a = P'

       Invariant: 
       If   a is a type family
       and  Sigma (a) = {x1:A1}..{xn:An} type
       then for all P s.t.    
	    +x1:A1, .., +xn:An; . |- P in [[-x1:A1]] .. [[-xn:An]] true
	    . ;. |- (P' P) in [[+x1:A1]] .. [[+xn:An]] [[-x1:A1]] .. [[-xn:An]] true
    *)
    fun abstract (a) = 

      let 
	val mS = case M.modeLookup a
	           of NONE => raise Error "Mode declaration expected"
		    | SOME mS => mS
	val V = case I.sgnLookup a 
	           of I.ConDec (name, _, _, _, V, I.Kind) => V
	            | _ => raise Error "Type Constant declaration expected"


	(* abstract' ((V, mS), w) = P'

	   Invariant:
	   If  Sigma (a) = {x1:A1} .. {xn:An} type
	   and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
	   and  Gamma= x1:A1, .. x(j-1):A(j-1) 
           and  Gamma |- w : Gamma+ 
	   then P' is a Lam abstraction
	*)
	fun abstract' ((_, M.Mnil), w) = (fn p => p)
	  | abstract' ((I.Pi ((D, _), V2), M.Mapp (M.Marg (M.Plus, _), mS)), w) =
	    let 
	      val D' = strengthenDec (D, w)
	      val P = abstract' ((V2, mS), I.dot1 w)
	    in
	      fn p => T.Lam (T.UDec D', P p)
	    end
	  | abstract' ((I.Pi (_, V2), M.Mapp (M.Marg (M.Minus, _), mS)), w) =
	      abstract' ((V2, mS), I.comp (w, I.shift))
      in
	abstract' ((V, mS), I.id)
      end

    (* transformInit (Psi, (a, S), w1) = (w', s')
     
       Invariant:
       If   |- Psi ctx
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w1 : Psi+
       then |- Gamma+ ctx
       and  Gamma+ = +x(k1):A(k1), ... +x(km):A(km) 
       and  Psi+ |- s' : Gamma+
       and  x1:A1 .. xn:An |- w: Gamma+    (w weakening substitution)
    *)
    fun transformInit (Psi, L, (a, S), w1) = 
      let
	val mS = case M.modeLookup a
	           of NONE => raise Error "Mode declaration expected"
		    | SOME mS => mS
	val V = case I.sgnLookup a 
	           of I.ConDec (name, _, _, _, V, I.Kind) => V
	            | _ => raise Error "Type Constant declaration expected"

	(* transformInit' ((S, mS), V, (w, s)) = (w', s')
 
  	   Invariant: 
	   If   Psi |- S : V > type
	   and  x1:A1...x(j-1):A(j-1) |- V = mj{xj:Aj} .. mn{xn:An} type : kind
	   and  x1:A1...x(j-1):A(j-1) |- w : +x1:A1... +x(j-1):A(j-1)
	   and  Psi |- w1 : Psi+
	   and  Psi+ |- s : +x1:A1... +x(j-1):A(j-1)
           then x1:A1...xn:An |- w' : +x1:A1... +xn:An
	   and  Psi+ |- s' : +x1:A1 .. +xn:An
	*)
	 
	fun transformInit' ((I.Nil, M.Mnil), I.Uni I.Type, (w, s)) = (w, s) 
	  | transformInit' ((I.App (U, S), M.Mapp (M.Marg (M.Minus, _), mS)), 
		 	    I.Pi (_, V2), (w, s)) =
  	    let 
	      val w' = I.comp (w, I.shift)
	      val s' = s
	    in
	      transformInit' ((S, mS), V2, (w', s'))
	    end
	  | transformInit' ((I.App (U, S), M.Mapp (M.Marg (M.Plus, _), mS)),
			    I.Pi ((I.Dec (name, V1), _), V2), (w, s)) =
	    let 
	      val V1' = strengthenExp (V1, w)
	      val w' = I.dot1 w
	      val U' = strengthenExp (U, w1)
	      val s' = T.dotEta (T.Exp U', s)
	    in
	      transformInit' ((S, mS), V2, (w', s'))
	    end
      in
	transformInit' ((S, mS), V, (I.id, createIHSub (Psi, L)))
      end
    
    (* transformConc ((a, S), w) = P

       Invariant:
       If   Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w : PsiAll
       then P is proof term consisting of all - objects of S,
	    defined in PsiAll
    *)
    fun transformConc ((a, S), w) = 
      let
	val mS = case M.modeLookup a
	           of NONE => raise Error "Mode declaration expected"
		    | SOME mS => mS

	fun transformConc' (I.Nil, M.Mnil) =
	      T.Unit
	  | transformConc' (I.App (U, S'), M.Mapp (M.Marg (M.Plus, _), mS')) =
	      transformConc' (S', mS')
	  | transformConc' (I.App (U, S'), M.Mapp (M.Marg (M.Minus, _), mS')) =
	      T.PairExp (strengthenExp (U, w), transformConc' (S', mS'))
      in
	transformConc' (S, mS)
      end
	

    (* transformApp (Psi0, (a, S), w) = (P', F')

       Invariant:
       Psi0 |- w : Psi
       a is the type family that is being converted
       Psi  |- S  : V >> V'
       Psi  |- P' : F'
    *)
    fun transformApp ((Psi, I.Null), (a, S), w) = 
        let
	  val mS = case M.modeLookup a
	             of NONE => raise Error "Mode declaration expected"
		      | SOME mS => mS
	  val V = case I.sgnLookup a 
	            of I.ConDec (name, _, _, _, V, I.Kind) => V
	             | _ => raise Error "Type Constant declaration expected"
	
	  fun transformApp' (I.Nil, M.Mnil) = T.Nil 
	    | transformApp' (I.App (U, S), (M.Mapp (M.Marg (M.Plus, _), mS))) =
	        T.AppExp (strengthenExp (U, w), transformApp' (S, mS))
	    | transformApp' (I.App (_, S), (M.Mapp (M.Marg (M.Minus, _), mS))) =
		transformApp' (S, mS)

	in 
	  (T.Root (T.Var ~1  (* Compute correctly *), transformApp' (S, mS)))
	end
      | transformApp ((Psi, I.Decl(Psi', D)), (a, S), w) =
          T.Lam (T.UDec D, transformApp ((Psi, Psi'), (a, S), peel w))





    (* raiseProg (G, (P, F)) = (P', F')) 
 
       Invariant:
       If   Psi, G |- P in F
       and  Psi |- G : blockctx
       then Psi |- P' in F'
       and  P = raise (G, P')   (using subordination)
       and  F = raise (G, F')   (using subordination)
    *)
    fun raisePrg (G, (T.Unit, T.True)) = (T.Unit, T.True)
      | raisePrg (G, (T.PairPrg (P1, P2), (T.And (F1, F2)))) =
        let 
	  val (P1', F1') = raisePrg (G, (P1, F1))
	  val (P2', F2') = raisePrg (G, (P2, F2))
	in
	  (T.PairPrg (P1', P2'), (T.And (F1', F2')))
	end
      | raisePrg (G, (T.PairExp (U, P), T.Ex (I.Dec (x, V), F))) =
	let 
 	  val w = S.weaken (G, I.targetFam V)       (* G  |- w  : G'    *)
	  val iw = Whnf.invert w 	          (* G' |- iw : G     *)
	  val G' = Whnf.strengthen (iw, G)
	  val V' = A.raiseType (G', V)
	  val U' = A.raiseTerm (G', U)
	  val (P', F') = raisePrg (G, (P, F))
	in
	  (T.PairExp (U', P'), T.Ex (I.Dec (x, V'), F'))
	end
      | raisePrg (G, (_, T.All _)) = raise Domain
    
    (* deblockify G = G'
     
       Invariant:
       If   |- G is a block ctx
       then |- G == G' 
       and  |- G' is an LF context
    *)
    fun deblockify (I.Null) = I.Null
      | deblockify (I.Decl (G, I.BDec (x, (c, s)))) = 
        let
	  val G' = deblockify G
          val (_, L) = I.constBlock c
	in 
	  append (G', (L, s))
	end
    and append (G', (nil, s)) = G'
      | append (G', (D :: L, s)) = 
          append (I.Decl (G', I.decSub (D, s)), (L, I.dot1 s))



    (* traverse (Ts, c) = L'

       Invariant:
       If   Ts is a list of type families
       and  c is a type family which entries are currently traversed
       then L' is a list of cases
    *)
    fun traverse (Psi0, L, c, Sig, wmap) =
      let 
	(* traverseNeg (Psi0, V, L) = ([w', d', PQ'], L')    [] means optional
	   
	   Invariant:
	   If   Psi0 |- V : type
	   and  V[v^-1] does not contain Skolem constants
	   and  c'' is the name of the object constant currently considered
	   and  L is a list of cases
	   then L' list of cases and L' extends L
	   and  Psi |- w' : Psi'   (Psi' is the context of all variables considered so far)
	   and  d' is the length of Delta
	   and  PQ'  is a pair, generating the proof term
	*)
	fun traverseNeg (Psi, I.Pi ((D as I.Dec (_, V1), I.Maybe), V2)) =
	    (case traverseNeg (I.Decl (Psi, T.UDec D), V2)
	       of (SOME (w', PQ')) => SOME (peel w', PQ'))
	  | traverseNeg (Psi, I.Pi ((D as I.Dec (_, V1), I.No), V2)) =
	    (case traverseNeg (Psi, V2) 
	       of (SOME (w', PQ')) => traversePos ((Psi, I.Null), V1, SOME (peel w', PQ')))
	  | traverseNeg (Psi, I.Root (I.Const a, S)) = 
	    let 
	      val (Psi', w') = strengthen (Psi, (a, S), I.Shift (I.ctxLength Psi), M.Plus)
	      val (w'', s'') = transformInit (Psi', L, (a, S), w')
	    in
	      (SOME (w', (fn P => (Psi', s'', P), fn wf => transformConc ((a, S), wf))))
	    end
	  
        and traversePos ((Psi, G), I.Pi ((D as I.BDec (x, (c, s)), _), V), SOME (w1, (P, Q))) =
  	    let 
	      val c' = wmap c
	    in
	      traversePos ((Psi, I.Decl (G, I.BDec (x, (c', s)))), 
			   V, SOME (I.dot1 w1, (P, Q)))
	    end
          | traversePos ((Psi, G), V as I.Root (I.Const a, S), SOME (w1, (P, Q))) =
	    let 	   
	      val (Psi'', _) = strengthenPsi (Psi, w1)
	      val k = lookupIH (Psi'', L, a) 
	      val T.PDec(_, F) = I.ctxLookup (Psi'', k)
	      val P' = transformApp ((Psi, G), (a, S), w1)
	      val (Psi', w2) = strengthen (Psi, (a, S), w1, M.Minus)
	      val (P'', F'') = raisePrg (deblockify G, (transformConc ((a, S), w2), F))
	      val w3 = peeln (I.ctxLength G, w2)
	      val t = T.Dot (T.Prg P'', T.id)
	    in     
	      (SOME (w3, 
		     (fn p => P (T.Let (T.PDec (NONE, F''), T.New P'', 
					T.Case (T.Cases [(Psi', t, p)]))), Q)))
	    end

	fun traverseSig' nil = nil
          | traverseSig' (I.ConDec (name, _, _, _, V, I.Type) :: Sig) = 
  	    (case traverseNeg (Psi0, Whnf.normalize (V, I.Shift (I.ctxLength Psi0)))
	       of (SOME (wf, (P', Q'))) =>  (P' (Q' wf)) :: traverseSig' Sig)
      in
	traverseSig' Sig
      end




    fun convertWorlds (a, T.Worlds cids) = 
          (fn (cids', wmap) => (T.Worlds cids', wmap)) (convertWorlds' (a, cids))
    and convertWorlds' (a, nil) = (nil, fn c => raise Error "World not found")
      | convertWorlds' (a, cid :: cids) = 
        let 
	  val I.BlockDec (s, m, G, L) = I.sgnLookup cid
	  (* Design decision: Let's keep all of G *)
	  val L' = convertList (a, (L, I.id))
	  val (cids', wmap) = convertWorlds' (a, cids)
	  val cid' = I.sgnAdd (I.BlockDec (s, m, G, L'))
	in
	  (cid' :: cids', fn c => if c = cid then cid' else wmap c)
	end
    and convertList (a, (nil, s)) = nil
      | convertList (a, (I.Dec (x, V) :: L, w)) = 
        if I.targetFam V = a then 
	  I.Dec (x, strengthenExp (V, w)) :: convertList (a, (L, I.dot1 w))
	else 
	  (* here we need to generate a case *)
	  convertList (a, (L, I.comp (w, I.shift)))
        
        
    (* convertPrg L = P'

       Invariant:
       If   L is a list of type families
       then P' is a conjunction of all programs resulting from converting
	    the relational encoding of the function expressed by each type 
	    family in L into functional form 
    *)

    fun convertPrg (L) = 
      let
	val (Psi0, R) = recursion L

	fun convertOnePrg a =
	  let 
	    val (name, V) = case I.sgnLookup a 
	              of I.ConDec (name, _, _, _, V, I.Kind) => (name, V)
		       | _ => raise Error "Type Constant declaration expected"
	    val mS = case M.modeLookup a
	               of NONE => raise Error "Mode declaration expected"
		        | SOME mS => mS
	    val Sig = Worldify.worldify a
	    val W = WorldSyn.lookup a
	    val (W', wmap) = convertWorlds (a, W)
	    val P = abstract a
	    val C = traverse (Psi0, L, a, Sig, wmap)
	  in
	    P (T.Case (T.Cases C))
	  end

	fun convertPrg' nil = raise Error "Cannot convert Empty program"
	  | convertPrg' [a] = convertOnePrg a
	  | convertPrg' (a :: L') = T.PairPrg (convertOnePrg a, convertPrg' L')


      in
	R (convertPrg' L)
      end
	  
  in 
    val convertFor = convertFor
    val convertPrg = convertPrg
    val traverse = traverse
  end
end (* functor FunSyn *)
