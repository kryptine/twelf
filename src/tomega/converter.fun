(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)

functor Converter 
  (structure Global : GLOBAL
   structure IntSyn' : INTSYN
   structure Tomega' : TOMEGA
     sharing Tomega'.IntSyn = IntSyn'
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
       and  G0 |- s G1 
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
(*      | strengthenPsi (I.Decl (Psi, F.Block (F.CtxBlock (l, G))), s) =
	let 
	  val (Psi', s') = strengthenPsi (Psi, s)
	  val (G'', s'') = strengthenCtx (G, s')
	in
	  (I.Decl (Psi', F.Block (F.CtxBlock (l, G''))), s'')
	end
 *)
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


    (* convertFor L = F'

       Invariant:
       If   L is a list of type families
       then F' is the conjunction of the logical interpretation of each
	    type family
     *)
    fun convertFor nil = raise Error "Empty theorem"
      | convertFor [a] = convertOneFor a
      | convertFor (a :: L) = T.And (convertOneFor a, convertFor L)



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


    (* strenghten (Psi, (a, S), w, m) = (Psi', w')       
     
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
	val F = convertFor L
	  
	fun name [a] = I.conDecName (I.sgnLookup a)
	  | name (a :: L) = I.conDecName (I.sgnLookup a) ^ "/" ^ (name L)
      in
	fn p => T.Rec (T.PDec (SOME (name L), F), p)
      end
	


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
    fun transformInit (Psi, (a, S), w1) = 
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
	      val w' =  I.dot1 w
	      val U' = strengthenExp (U, w1)
	      val s' = Whnf.dotEta (I.Exp (U'), s)
	    in
	      transformInit' ((S, mS), V2, (w', s'))
	    end
      in
	transformInit' ((S, mS), V, (I.id, I.Shift (I.ctxLength Psi)))
      end
    
 
    fun transformDec (Ts, (Psi, G0), d, (a, S), w1, w2, t0) = raise Error "not yet implemented"

(*
    (* transformDec (c'', (Psi+-, G0), d, (a, S), w1, w2, t) = (d', w', s', t', Ds)
     
       Invariant:
       If   |- Psi ctx
       and  Psi |- G0 ctx
       and  d = |Delta|
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi, G0 |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi, G0 |- w1 : Psi+, G0[w1^-1]
       and  Psi |- w2 : Psi+-
       and  Psi+- |- t0 : Psi+
       then |- Gamma+ ctx
       and  Gamma+ = +x(k1):A(k1), ... +x(km):A(km) 
       and  Psi |- s' : Gamma+
       and  x1:A1 .. xn:An |- w': Gamma+    (w weakening substitution)
       and  Psi+- |- t' : Psi+, -x(k1):{G0} A(k1), ... -x(km):{G0} A(km)
       and  d' = |Delta'|
    *)

    fun transformDec (Ts, (Psi, G0), d, (a, S), w1, w2, t0) = 
      let
	val mS = case M.modeLookup a
	           of NONE => raise Error "Mode declaration expected"
		    | SOME mS => mS
	val V = case I.sgnLookup a 
	           of I.ConDec (name, _, _, _, V, I.Kind) => V
	            | _ => raise Error "Type Constant declaration expected"


	(* raiseExp (G, U, a) = U'  
	 
	   Invariant: 
	   If   |- Psi ctx         (for some given Psi)
	   and  Psi |- G ctx
           and  Psi, G |- U : V    (for some V)
	   then Psi, G |- [[G]] U : {{G}} V     (wrt subordination)
	*)
	fun raiseExp (G, U, a) =
	  let

	    (* raiseExp G = (w', k)
	       
	       Invariant:
	       If   |-  Psi ctx
	       and  Psi |- G ctx
	       and  Psi |- G' ctx   which ARE subordinate to a
	       then Psi, G |- w : Psi, G'
	       and  k is a continuation calculuting the right exprssion:
		    for all U, s.t. Psi, G |- U : V 
		    Psi |- [[G']] U : {{G'}} V
	    *)
	    fun raiseExp' I.Null = (I.id, fn x => x)  
	      | raiseExp' (I.Decl (G, D as I.Dec (_, V))) =
	        let
		  val (w, k) = raiseExp' G
		in
		  if Subordinate.belowEq (I.targetFam V, a) then 
		    (I.dot1 w, fn x => k (I.Lam (strengthenDec (D, w), x)))
		  else 
		    (I.comp (w, I.shift), k)
		end
	      
	    val (w, k) = raiseExp' G 
	  in 
	    k (strengthenExp (U, w))
	  end
	

	(* raiseType (G, U, a) = U'  
	 
	   Invariant: 
	   If   |- Psi ctx         (for some given Psi)
	   and  Psi |- G ctx
           and  Psi, G |- U : V    (for some V)
	   then Psi, G |- [[G]] U : {{G}} V     (wrt subordination)
	   and  Psi, G, x:{{G}} V |- x G : V
	*)

	fun raiseType (G, U, a) =
	  let
	    (* raiseType (G, n) = (w', k, S')
	     
	      Invariant:
              If   |-  Psi ctx
              and  Psi |- G, Gv ctx
	      and  Psi |- G' ctx   which ARE subordinate to a
	      and  n = |Gv| + 1
              then Psi, G |- w : Psi, G'
	      and  k is a continuation calculating the right exprssion:
	           for all U, s.t. Psi, G |- U : V 
	           Psi |- [[G']] U : {{G'}} V
	      and  k' is a continuation calculating the corresponding spine:
		   for all S, s.t. Psi, G, G0,|- ... refine
	    *)
	    fun raiseType' (I.Null, n) = (I.id, fn x => x, fn S => S)
	      | raiseType' (I.Decl (G, D as I.Dec (_, V)), n) =
		let
		  val (w, k, k') = raiseType' (G, n+1)
		in
		  if Subordinate.belowEq (I.targetFam V, a) then 
		    (I.dot1 w, fn x => k (I.Pi ((strengthenDec (D, w), I.Maybe), x)), 
		               fn S => I.App (I.Root (I.BVar n, I.Nil), S))
		  else 
		    (I.comp (w, I.shift), k, k')
		end
	      
	    val (w, k, k') = raiseType' (G, 2)
	  in 
	    (k (strengthenExp (U, w)), I.Root (I.BVar 1, k' I.Nil))
	  end


	(* exchangeSub (G0) = s'

	   Invariant:
	   For some Psi, some G, some V:
	   Psi, V, G0 |- s' : Psi, G0, V
	*)
	fun exchangeSub (G0) = 
	  let 
	    val g0 = I.ctxLength G0 
	    fun exchangeSub' (0, s) = s 
	      | exchangeSub' (k, s) = exchangeSub' (k-1, I.Dot (I.Idx (k), s))
	  in
	    I.Dot (I.Idx (g0 + 1), exchangeSub' (g0, I.Shift (g0 + 1)))
	  end


	(* transformDec' (d, (S, mS), V, (z1, z2), (w, t)) = (d', w', t', (Ds+, Ds-))
 
  	   Invariant: 
	   If   Psi, G0 |- S : V > type
	   and  S doesn't contain Skolem constants
	   and  d = |Delta|
	   and  x1:A1...x(j-1):A(j-1) |- V = mj{xj:Aj} .. mn{xn:An} type : kind
	   and  x1:A1...x(j-1):A(j-1) |- w : +x1:A1... +x(j-1):A(j-1)
	   and  Psi, G0 |- w1 : Psi+, G0[w1^-1]
           and  Psi |- w2 : Psi+-
	   and  Psi+- |- t : Psi+, -x1:{{G0}} A1... -xj:{{G0}} Aj    
           and  Psi+, -x1:{{G0}} A1...-x(j-1):{{G0}} A(j-1) |- z1: Psi+
	   and  Psi+, -x1:{{G0}} A1...-x(j-1):{{G0}} A(j-1), G0 |- z2: x1:A1...x(j-1):A(j-1)
           then x1:A1...xn:An |- w' : +x1:A1... +xn:An
	   and  Psi+- |- s' : +x1:A1 .. +xn:An
           and  Psi+- |- t' : Psi+, -x1:{{G0}} A1... -xn:{{G0}} An   
	   and  d' = |Delta'|
	*)
       	fun transformDec' (d, (I.Nil, M.Mnil), I.Uni I.Type, (z1, z2), (w, t)) = 
	      (w, t, (d, fn (k, Ds) => Ds k, fn _ => T.Empty))
	  | transformDec' (d, (I.App (U, S), M.Mapp (M.Marg (M.Minus, _), mS)), 
			  I.Pi ((I.Dec (_, V1), DP), V2), (z1, z2), (w, t)) =
	      let 
		val g = I.ctxLength G0
		val w1' = peeln (g, w1)
		val (G1, _) = strengthenCtx (G0, w1')
		val (G2, _) = ctxSub (G1, z1)
                val (V1'', Ur) = raiseType (G2, I.EClo (V1, z2), I.targetFam V1)
                val w' = (case DP 
			    of I.Maybe => I.dot1 w
			    |  I.No => I.comp (w, I.shift))

		val U0 = raiseExp (G0, U, I.targetFam V1'')
		val U' = strengthenExp (U0, w2)
	       	val t' = Whnf.dotEta (I.Exp (U'), t)
		val z1' = I.comp (z1, I.shift)
		val xc  = exchangeSub G0
		val z2n = I.comp (z2, I.comp (I.shift, xc))
		val Ur' = I.EClo (Ur, xc)
		val z2' = Whnf.dotEta (I.Exp (Ur'), z2n)
		val (w'', t'', (d', Dplus, Dminus)) = 
		  transformDec' (d+1, (S, mS), V2, (z1', z2'), (w', t'))
	      in
		(w'', t'', (d', Dplus, fn k => T.Split (k, Dminus 1)))
	      end
	  | transformDec' (d, (I.App (U, S), M.Mapp (M.Marg (M.Plus, _), mS)),
			  I.Pi ((I.Dec (name, V1), _), V2), (z1, z2), (w, t)) =
	    let 
	      val V1' = strengthenExp (V1, w)
	      val w' =  I.dot1 w
	      val U' = strengthenExp (U, w1)
	      val t' = t
	      val z1' = T.dot1n (G0, z1)
	      val z2' = I.Dot (I.Exp (I.EClo (U', z1')), z2)
	      val (w'', t'', (d', Dplus, Dminus)) = 
		transformDec' (d+1, (S, mS), V2, (z1, z2'), (w', t'))
	    in
	      (w'', t'', (d', fn (k, Ds) => T.App ((k, U'), Dplus (1, Ds)), Dminus))
	    end

	  val (w'', t'', (d', Dplus, Dminus)) = 
	    transformDec' (d, (S, mS), V, (I.id, I.Shift (domain (Psi, t0) + I.ctxLength G0)), 
			   (I.id, t0))


	  (* head Ts (w, t, (d, Dplus, Dminus)) = (d', w', t', P')

	     Invariant:
	     If   a not in Ts  then d'= d+1,  P' makes a lemma call
	     If   Ts = [a]     then d'= d     P' used directly the ih.
	     If   Ts = a1 .. ai ... and ai = a  
	     then d' = d+i   and P' select ih, and then decomposes is, using
	          (i-1) Rights and 1 Left
          *)
	  fun varHead Ts (w'', t'', (d', Dplus, Dminus)) =
	    let 
	      fun head' ([a'], d1, k1) = (d1, k1)
		| head' (a'::Ts', d1, k1) =
		  if a = a' then 
		    (d1+1, fn xx => T.Left (xx, (k1 1)))
		  else 
		    let 
		      val (d2, k2) = head' (Ts', d1+1, k1)
		    in
		      (d2, fn xx => T.Right (xx, (k2 1)))
		    end

		val (d2, k2) = head' (Ts, d', fn xx => Dplus (xx, Dminus))
	      in
		(d2, w'', t'', k2 d)
	      end
	    

(*
	  fun lemmaHead (w'', t'', (d', Dplus, Dminus)) = 
	    let 
	      val name = I.conDecName (I.sgnLookup a)
	      val l = (case NONE (* (FunNames.nameLookup name) --cs *)
			 of NONE => raise Error ("Lemma " ^ name ^ " not defined")
		       | SOME lemma => lemma)
	    in
	      (d'+1, w'', t'', F.Lemma (l, Dplus (1, Dminus)))
	    end
*)	        
      in
	if List.exists (fn x => x = a) Ts 
	  then varHead Ts (w'', t'', (d', Dplus, Dminus))
	else (* lemmaHead (w'', t'', (d', Dplus, Dminus)) *) 
	  raise Error "Lemmas temporarily disabled --cs"
      end


*)
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
	
		     

    (* traverse (Ts, c) = L'

       Invariant:
       If   Ts is a list of type families
       and  c is a type family which entries are currently traversed
       then L' is a list of cases
    *)
    fun traverse (Ts, c, Sig, wmap) =
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
	       of (SOME (w', d', PQ')) => (SOME (peel w', d', PQ'))
  	        | (NONE) => (NONE))

	  | traverseNeg (Psi, I.Pi ((D as I.Dec (_, V1), I.No), V2)) =
	    (case traverseNeg (Psi, V2) 
	       of (SOME (w', d', PQ')) => traversePos (Psi, (V1, I.id), 
						       SOME (w', d', PQ'))
	        | (NONE) => traversePos (Psi, (V1, I.id), NONE))
	       
	  | traverseNeg (Psi, I.Root (I.Const a, S)) = 
	    let 
	      val (Psi', w') = strengthen (Psi, (a, S), I.Shift (I.ctxLength Psi), M.Plus)
		(* Psi  |- w' : Psi' *)
		(* Psi' is a subcontext of Psi', which contains all those
		   variables that occur in a M.Plus position *)	 
	      val (w'', s'') = transformInit (Psi', (a, S), w')
		(* Let Sigma (a) = PI{PsiDef} type *)
		(* Psi+ is a subset of PsiDef, of all the parameters that occur in a 
		   plus position *)
		(* Psi+ |- w' : PsiDef *)
		(* Psi' |-  s'' : Psi+ *)  
		(* s'' is the substitution in a case *)
		(* Psi' is the context in a case *) 
	    in
	      (SOME (w', 1, (fn p => (Psi', s'', p), fn wf => transformConc ((a, S), wf))))
	    end
	  
        and traversePos (Psi, (I.Pi ((D as I.BDec (x, (c, s)), _), V), v), SOME (w1, d, (P, Q))) =
  	    let 
	      val c' = wmap c
	      val _ = traversePos (I.Decl (Psi, T.UDec (strengthenDec (D, v))), (V, I.dot1 v), SOME (w1, d, (P, Q)))
	    in
	      NONE
	    end
          | traversePos (Psi, (V as I.Root _, v), SOME (w1, d, (P, Q))) =
	    let 
	      val I.Root (I.Const a', S) = Whnf.normalize (strengthenExp (V, v), I.id)
	      val (Psi', w2) = strengthen (Psi, (a', S), w1, M.Minus)
	      val w3 = strengthenSub (w1, w2)
	      val (d4, w4, t4, Ds) = transformDec (Ts, (Psi', I.Null), d, (a', S), w1, w2, w3) 
	    in     
	      (SOME (w2, d4, (fn p => P ( (* T.Let (Ds,  *)
						T.Case (T.Cases [(Psi', t4, p)])), Q)))
	    end

	(* traversePos (c, Psi, (V, v), [w', d', PQ'], L) =  ([w'', d'', PQ''], L'') 
	   
	   Invariant:
	   If   Psi, G |- V : type
	   and  Psi, G |- v : Psi'       (s.t.  Psi' |- V[v^-1] : type exists)
	   and V[v^-1] does not contain Skolem constants 
	   [ and Psi', G |- w' : Psi''
	     and |Delta'| = d'    for a Delta'
	     and PQ' can generate the proof term so far in Delta'; Psi''
	   ]
	   and  c is the name of the constant currently considered
	   and  L is a list of cases
	   then L'' list of cases and L'' extends L
	   and  Psi |- w'' : Psi2
	   and  |Delta''| = d''  for a Delta'
	   and  PQ'' can genreate the proof term so far in Delta''; Psi2
	*)
(*	and traversePos (c'', Psi, (I.Pi ((D as I.Dec (_, V1), I.Maybe), V2), v), 
			 SOME (w, d, PQ), L) = 
	    (case traversePos (c'', I.Decl (Psi,  T.UDec (strengthenDec (D, v))), 
			       (V2, I.dot1 v), 
			       SOME (I.dot1 w, d, PQ), L)
	       of (SOME (w', d', PQ'), L') => (SOME  (w', d', PQ'), L'))
	  | traversePos (c'', Psi, G, (I.Pi ((D as I.Dec (_, V1), I.No), V2), v), SOME (w, d, PQ), L) =
	    (case traversePos (c'', Psi, G, (V2, I.comp (v, I.shift)), SOME (w, d, PQ), L)
	       of (SOME (w', d', PQ'), L') => 
		 (case traverseNeg (c'', I.Decl (Psi, F.Block (F.CtxBlock (NONE, G))), 
				    (V1, v), L')
		    of (SOME (w'', d'', (P'', Q'')), L'') => (SOME (w', d', PQ'), (P'' (Q'' w'')) :: L'')
	             | (NONE, L'') => (SOME (w', d', PQ'), L'')))

	  | traversePos (c'', Psi, (V, v), SOME (w1, d, (P, Q)), L) = 
	    let (* Lemma calls (no context block) *)
	      val I.Root (I.Const a', S) = Whnf.normalize (strengthenExp (V, v), I.id)
	      val (Psi', w2) = strengthen (Psi, (a', S), w1, M.Minus)

	      val _ = if !Global.doubleCheck 
			then TypeCheck.typeCheck (T.coerceCtx Psi', (I.Uni I.Type, I.Uni I.Kind))
		      else ()    (* provide typeCheckCtx from typecheck *)
	      val w3 = strengthenSub (w1, w2)
		
	      (* val (d4, w4, t4, Ds) = transformDec (Ts, (Psi', I.Null), d, (a', S), w1, w2, w3) *)
	      val D = transformDec (Psi', (a', S))
	    in     
	      (SOME (w2, d4, (fn p => P (T.Let (Ds, 
				       T.Case (T.Cases [(Psi', t4, p)]))), Q)), L)
	    end


	  | traversePos (c'', Psi, G, (V, v), SOME (w1, d, (P, Q)), L) = 
	    let (* Lemma calls (under a context block) *)
	      val I.Root (I.Const a', S) = strengthenExp (V, v)
	      val (dummy as I.Decl (Psi', F.Block (F.CtxBlock (name, G2))), w2) = 
		    strengthen (I.Decl (Psi, F.Block (F.CtxBlock (NONE, G))),
					    (a', S), w1, M.Minus)
	      val _ = if !Global.doubleCheck 
			then TypeCheck.typeCheck (F.makectx dummy, (I.Uni I.Type, I.Uni I.Kind))
		      else ()   (* provide typeCheckCtx from typecheck *)
	      val g = I.ctxLength G
	      val w1' = peeln (g, w1)
	      val w2' = peeln (g, w2)  (* change w1 to w1' and w2 to w2' below *)
	      val (G1, _) = strengthenCtx (G, w1')
	      val w3 = strengthenSub (w1', w2')
	      val (d4, w4, t4, Ds) = transformDec (Ts, (Psi', G), d, (a', S), w1, w2', w3)
	    in
	      (SOME (w2', d4, (fn p => P (F.Let (F.New (F.CtxBlock (NONE, G1), Ds), 
				       T.Case (T.Cases [(Psi', t4, p)]))), Q)), L)
	    end
*)
(* cannot occur in our setting

	  | traversePos (c'', Psi, (I.Pi ((D as I.Dec (_, V1), I.Maybe), V2), v), NONE, L) =
	      traversePos (c'',  I.Decl (Psi, T.UDec (strengthenDec (D, v))), 
			       (V2, I.dot1 v), 
			       NONE, L)

*)
(*	  | traversePos (c'', Psi, G, (I.Pi ((D as I.Dec (_, V1), I.No), V2), v), NONE, L) =
	    (case traversePos (c'', Psi, G, (V2, I.comp (v, I.shift)), NONE, L)
	       of (NONE, L') => 
		 (case traverseNeg (c'', I.Decl (Psi, F.Block (F.CtxBlock (NONE, G))), 
				    (V1, v), L')
		    of (SOME (w'', d'', (P'', Q'')), L'') => (NONE, (P'' (Q'' w'')) :: L'')
	             | (NONE, L'') => (NONE, L'')))
*)
(* cannot occur in our design now, can it?

	  | traversePos (c'', Psi, (V, v), NONE, L) =
	    (NONE, L) *)

	fun traverseSig' nil = nil
          | traverseSig' (I.ConDec (name, _, _, _, V, I.Type) :: Sig) = 
  	    (case traverseNeg (I.Null, V)
	       of (SOME (wf, d', (P', Q'))) =>  (P' (Q' wf)) :: traverseSig' Sig)
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
        
        

		


    (* convertPrg Ts = P'

       Invariant:
       If   Ts is a list of type families
       then P' is a conjunction of all programs resulting from converting
	    the relational encoding of the function expressed by each type 
	    family in Ts into functional form 
    *)

    fun convertPrg Ts = 
      let

	fun convertOnePrg a =
	  let 
	    val V = case I.sgnLookup a 
	              of I.ConDec (name, _, _, _, V, I.Kind) => V
		       | _ => raise Error "Type Constant declaration expected"
	    val mS = case M.modeLookup a
	               of NONE => raise Error "Mode declaration expected"
		        | SOME mS => mS
	    val Sig = Worldify.worldify a
	    val W = WorldSyn.lookup a
	    val (W', wmap) = convertWorlds (a, W)
	    val P = abstract a
	    val C = traverse (Ts, a, Sig, wmap)
	  in
	    P (T.Case (T.Cases (nil (* C -cs *))))
	  end

	fun convertPrg' nil = raise Error "Cannot convert Empty program"
	  | convertPrg' [a] = convertOnePrg a
	  | convertPrg' (a :: Ts') = T.PairPrg (convertOnePrg a, convertPrg' Ts')

	val R = recursion Ts
      in
	R (convertPrg' Ts)
      end
	  
	  

  in 
    val convertFor = convertFor
    val convertPrg = convertPrg
    val traverse = traverse
  end
end (* functor FunSyn *)
