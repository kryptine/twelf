(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Brigitte Pientka *)
(* The implemented abstraction is used in tabling
   it includes linearization and strengthening *)
functor AbstractTabled (structure IntSyn' : INTSYN
			structure Whnf    : WHNF
			sharing Whnf.IntSyn = IntSyn'
			structure Subordinate : SUBORDINATE
			sharing Subordinate.IntSyn = IntSyn'
			structure Conv    : CONV
			sharing Conv.IntSyn = IntSyn'
			structure TableParam : TABLEPARAM
			  sharing TableParam.IntSyn = IntSyn'
			structure Unify   : UNIFY
			sharing Unify.IntSyn = IntSyn'
			structure Print : PRINT
			sharing Print.IntSyn = IntSyn'
		      )
  : ABSTRACTTABLED =
struct

  structure IntSyn = IntSyn' 
  structure TableParam = TableParam 
    
  exception Error of string

  (* Strenghening during abstraction *)
  (* val strengthen = ref false;*)

 
  local
    structure I = IntSyn
      
    datatype ExistVars =
      EV of I.Exp			

    datatype Duplicates = AV of (I.Exp * int) | FGN of int 

    (*
       We write {{K}} for the context of K, where EVars have
       been translated to declarations and their occurrences to BVars.
       For each occurrence of EVar, we generate a distinct BVar together with
       a residual constraint. This enforces that the final abstraction of U is 
       linear.
       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars in U are collected in K.
       In particular, . ||- U means U contains no EVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)

    fun compose'(IntSyn.Null, G) = G
      | compose'(IntSyn.Decl(G', D), G) = IntSyn.Decl(compose'(G', G), D)

    fun isId (I.Shift(n)) = (n = 0)
      | isId (s as I.Dot(I.Idx n, s')) = isId' (s, 0)
      | isId (s as I.Dot(I.Undef, s')) = isId' (s, 0)
      | isId (I.Dot(I.Exp _ , s)) = false 
      
    and isId' (I.Shift(n), k) = (n = k)
      | isId' (I.Dot(I.Idx(i), s), k) = 
      let
	val k' = k+1
      in 
	(i = k') andalso isId' (s, k')
      end 
      | isId' (I.Dot(I.Undef, s), k) = isId' (s, k+1)

    fun equalCtx (I.Null, s, I.Null, s') = true
      | equalCtx (I.Decl(G, D), s, I.Decl(G', D'), s') = 
      Conv.convDec((D, s), (D', s')) andalso (equalCtx (G, I.dot1 s, G', I.dot1 s'))
      | equalCtx (I.Decl(G, D), s, I.Null, s') = false
      | equalCtx (I.Null, s, I.Decl(G', D'), s') = false

    (* eqEVar X Y = B
     where B iff X and Y represent same variable
     *)	      
    fun eqEVarW (I.EVar (r1, _, _, _)) (EV (I.EVar (r2, _, _, _))) = (r1 = r2)
      | eqEVarW _ _ = false 

    fun eqEVar X1 (EV X2) = 
      (*      Sun Dec  1 14:04:17 2002 -bp  may raise exception 
       if strengthening is applied,i.e. the substitution is not always id! *)
      (* does the substitution matter here? -- 
         I guess no. Wed Jan 22 13:24:35 2003 -bp *)
      (* s = I.Shift(0) if no strengthening is applied, otherwise it may be 
         different *)
      let val (X1', s) = Whnf.whnf (X1, I.id)
        val (X2', s) = Whnf.whnf (X2, I.id)
      in 
	eqEVarW X1' (EV X2')
      end 
      
    (* eqAVar X Y = B
     where B iff X and Y represent same variable
     *)
    fun eqAVar (I.EVar (r1, _, _, _)) (AV (I.EVar (r2, _, _, _), d)) = (r1 = r2)
      | eqAVar _ _ = false 

      
    (* exists P K = B
     where B iff K = K1, Y, K2  s.t. P Y  holds
     *)
    fun exists P K =
        let fun exists' (I.Null) = false
	      | exists' (I.Decl(K',Y)) = P(Y) orelse exists' (K')
	in
	  exists' K
	end
 
    (* member P K = B option *)
    fun member P K =
        let fun exists' (I.Null) = NONE
	      | exists' (I.Decl(K',(i, Y))) = if P(Y) then SOME(i) else exists' (K')
	in
	  exists' K
	end

    fun or (I.Maybe, _) = I.Maybe
      | or (_, I.Maybe) = I.Maybe
      | or (I.Meta, _) = I.Meta
      | or (_, I.Meta) = I.Meta
      | or (I.No, I.No) = I.No

   
    (* occursInExp (k, U) = DP, 

       Invariant:
       If    U in nf 
       then  DP = No      iff k does not occur in U
	     DP = Maybe   iff k occurs in U some place not as an argument to a Skonst
	     DP = Meta    iff k occurs in U and only as arguments to Skonsts
    *)
    fun occursInExp (k, I.Uni _) = I.No
      | occursInExp (k, I.Pi (DP, V)) = or (occursInDecP (k, DP), occursInExp (k+1, V))
      | occursInExp (k, I.Root (H, S)) = occursInHead (k, H, occursInSpine (k, S))
      | occursInExp (k, I.Lam (D, V)) = or (occursInDec (k, D), occursInExp (k+1, V))
      | occursInExp (k, I.FgnExp (cs, ops)) = occursInExp (k, Whnf.normalize (#toInternal(ops) (), I.id))
      (* no case for Redex, EVar, EClo *)

    and occursInHead (k, I.BVar (k'), DP) = 
        if (k = k') then I.Maybe
	else DP
      | occursInHead (k, I.Const _, DP) = DP
      | occursInHead (k, I.Def _, DP) = DP
      | occursInHead (k, I.FgnConst _, DP) = DP
      | occursInHead (k, I.Skonst _, I.No) = I.No
      | occursInHead (k, I.Skonst _, I.Meta) = I.Meta
      | occursInHead (k, I.Skonst _, I.Maybe) = I.Meta
      (* no case for FVar *)

    and occursInSpine (_, I.Nil) = I.No
      | occursInSpine (k, I.App (U, S)) = or (occursInExp (k, U), occursInSpine (k, S))
      (* no case for SClo *)

    and occursInDec (k, I.Dec (_, V)) = occursInExp (k, V)
    and occursInDecP (k, (D, _)) = occursInDec (k, D)

    (* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise 
    *)
    (* optimize to have fewer traversals? -cs *)
    (* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *)
    fun piDepend (DPV as ((D, I.No), V)) = I.Pi DPV
      | piDepend (DPV as ((D, I.Meta), V)) = I.Pi DPV
      | piDepend ((D, I.Maybe), V) = 
	  I.Pi ((D, occursInExp (1, V)), V)
	
    (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
    fun raiseType (I.Null, V) = V
      | raiseType (I.Decl (G, D), V) = raiseType (G, I.Pi ((D, I.Maybe), V))

    (* collectExpW ((Gs, ss), G, Gl, (U, s), K, DupVars, flag) = (K', DupVars')

       Invariant: 
       If    G, Gl |- s : G1     G1 |- U : V      (U,s) in whnf
                Gs |- ss : G  (Gs is the strengthened context and ss is the strengthening substitution)

       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
	     where K' contains all EVars in (U,s) 
       and  DupVars' = DupVars, DupVars'' 
            where DupVars' contains all duplicates in (U,s)

      if flag = true 
        then duplicates of EVars are collected in DupVars
        otherwise no duplicates are collected

      note : 1) we only need to collect duplicate occurrences of EVars 
                if we need to linearize the term the EVars occur in.

             2) we do not linearize fgnExp 
    *)
    (* Possible optimization: Calculate also the normal form of the term *)
    fun collectExpW (Gss, G, Gl, (I.Uni L, s), K, DupVars, flag, d) = (K, DupVars)
      | collectExpW (Gss, G, Gl, (I.Pi ((D, _), V), s), K, DupVars, flag, d) =
        let
	  val (K', DupVars') = collectDec (Gss, G, (D, s), K, DupVars, flag, d)
	in 
	  (* should we apply I.dot1(ss) ? Tue Oct 15 21:55:16 2002 -bp *)
          collectExp (Gss, G, I.Decl (Gl, I.decSub (D, s)), (V, I.dot1 s), K', DupVars', flag, d+1)
	end 
      | collectExpW (Gss, G, Gl, (I.Root (_ , S), s), K, DupVars, flag, d) =
	  collectSpine (Gss, G, Gl, (S, s), K, DupVars, flag, d)
      | collectExpW (Gss, G, Gl, (I.Lam (D, U), s), K, DupVars, flag, d) =
	  let
	    val (K', DupVars') = collectDec (Gss, G, (D, s), K, DupVars, false, d)
	  in 
	    collectExp (Gss, G, I.Decl (Gl, I.decSub (D, s)), (U, I.dot1 s), K', DupVars', flag, d+1)
	  end 
      | collectExpW (Gss, G, Gl, (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) =
	  collectEVar (Gss, G, Gl, (X, s), K, DupVars, flag, d)
	      
      | collectExpW (Gss, G, Gl, (I.FgnExp (cs, ops), s), K, DupVars, flag, d) = 
          collectExp (Gss, G, Gl, (#toInternal(ops) (), s), K, I.Decl(DupVars, FGN(I.ctxLength G)), false, d)
	  
    (* No other cases can occur due to whnf invariant *)

    (* collectExp (Gss, G, Gl, (U, s), K) = K' 
       
       same as collectExpW  but  (U,s) need not to be in whnf 
    *) 
    and collectExp (Gss, G, Gl, Us, K, DupVars, flag, d) = 
        collectExpW (Gss, G, Gl, Whnf.whnf Us, K, DupVars, flag, d)

    (* collectSpine (Gss, G, Gl, (S, s), K, DupVars, flag) = (K', DupVars')

       Invariant: 
       If    G, Gl |- s : G1     G1 |- S : V > P
                Gs |- ss : G
       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in (S, s)
       and DupVars'' contains all duplicates in (S, s)
     *)
    and collectSpine (Gss, G, Gl, (I.Nil, _), K, DupVars, flag, d) = (K, DupVars)
      | collectSpine (Gss, G, Gl, (I.SClo(S, s'), s), K, DupVars, flag, d) = 
          collectSpine (Gss, G, Gl, (S, I.comp (s', s)), K, DupVars, flag, d)
      | collectSpine (Gss, G, Gl, (I.App (U, S), s), K, DupVars, flag, d) =
	  let
	    val (K', DupVars') = collectExp (Gss, G, Gl, (U, s), K, DupVars, flag, d)
	  in 
	    collectSpine (Gss, G, Gl, (S, s), K', DupVars', flag, d)
	  end 


    and collectEVarFapStr (Gss, G, Gl, ((X', V'), w), (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) = 
        if exists (eqEVar X) K  
	  then (* we have seen X before *)
	    (if flag 
	       then 
		 collectSub(Gss, G, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d) 
	     (* since X has occurred before, we do not traverse its type V' *)
	     else                     
	       collectSub(Gss, G, Gl, s, K, DupVars, flag, d))
	else 
	  let
(*	    val V' = raiseType (GX, V) (* inefficient! *)*)
	    val (K', DupVars') = collectExp ((I.Null, I.id), I.Null, I.Null, (V', I.id), K, DupVars, false, d)
	  in
	    collectSub(Gss, G, Gl, I.comp(w, s), I.Decl (K', EV(X')), DupVars', flag, d)
	  end

    and collectEVarNFapStr (Gss, G, Gl, ((X', V'), w), (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) = 
        if exists (eqEVar X) K  
	  then 
	    (* we have seen X before, i.e. it was already strengthened *)
	    (if flag 
	       then 
		 collectSub(Gss, G, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d) 
	     else 
	       collectSub(Gss, G, Gl, s, K, DupVars, flag, d))
	else 
	  let
	     (*	    val V' = raiseType (GX, V) (* inefficient! *)*)
	     val (K', DupVars') = collectExp ((I.Null, I.id), I.Null, I.Null, (V', I.id), K, DupVars, false, d)
	   in	     
	     if flag 
	       then 
		 collectSub(Gss, G, Gl, I.comp(w, s), I.Decl(K', EV(X')), I.Decl(DupVars', AV(X', d)), flag, d) 
	     else 
	       collectSub(Gss, G, Gl, I.comp(w, s), I.Decl(K', EV(X')), DupVars', flag, d)
	   end 

    and collectEVarStr (Gss as (Gs, ss), G, Gl, (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) = 
      let
	val w = Subordinate.weaken (GX, I.targetFam V)
	val iw = Whnf.invert w 
	val GX' = Whnf.strengthen (iw, GX)
	val X' as I.EVar (r', _, _, _) = I.newEVar (GX', I.EClo (V, iw)) (* ? *)
	val _ = Unify.instantiateEVar (r, I.EClo (X', w), nil) 
	val V' = raiseType (GX', I.EClo (V, iw))	
      in 
	if isId (I.comp(w, I.comp(ss, s))) (* equalCtx (Gs, I.id, GX', s) *) 
	  then (* fully applied *)
	    collectEVarFapStr (Gss, G, Gl, ((X', V'), w), (X, s), K, DupVars, flag, d)
	else 
	  (* not fully applied *)
	  collectEVarNFapStr (Gss, G, Gl, ((X', V'), w), (X, s), K, DupVars, flag, d)
      end 

    (* X is fully applied pattern *)
    and collectEVarFap (Gss, G, Gl, (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) = 
        if exists (eqEVar X) K
	  then 
	    (* we have seen X before *)
	     (if flag 
	       then
		 ((* print "collect fap EVar, duplicate flag = true\n";*)
		 collectSub(Gss, G, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d) )
	        (* since X has occurred before, we do not traverse its type V' *)
	     else 
		((* print "collect fap EVar, duplicate flag = false\n";*)
	       collectSub(Gss, G, Gl, s, K, DupVars, flag, d)))
	else 
	  let
	    (* val _ = checkEmpty !cnstrs *)
	    val V' = raiseType (GX, V) (* inefficient! *)
	    val (K', DupVars') = collectExp ((I.Null, I.id), I.Null, I.Null, (V', I.id), K, DupVars, false, d)
(*	    val _ = print "collect fap EVar (seen for the first time) \n"*)
	  in
	    collectSub(Gss, G, Gl, s, I.Decl (K', EV(X)), DupVars', flag, d)
	  end

    and collectEVarNFap (Gss, G, Gl, (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) = 
        if exists (eqEVar X) K 
	  then 
	    (if flag 
	       then 
		 ((* print "collect nfap EVar (duplicate) flag = true\n";*)
		 collectSub(Gss, G, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)) 
	     else  
	       ((* print "collect nfap EVar (duplicate) flag = false\n"; *)
	       collectSub(Gss, G, Gl, s, K, DupVars, flag, d))) 
	else 
	  let
	    val V' = raiseType (GX, V) (* inefficient! *)
	    val (K', DupVars') = collectExp ((I.Null, I.id), I.Null, I.Null, (V', I.id), K, DupVars, false, d)
(*	    val _ = print "collect nfap EVar (seen for the first time)\n"; *)
	  in 
	    if flag 
	      then 
		collectSub(Gss, G, Gl, s, I.Decl(K', EV(X)), I.Decl(DupVars, AV(X, d)), flag, d) 
	    else 
	      collectSub(Gss, G, Gl, s, I.Decl(K', EV(X)), DupVars, flag, d)
	  end

    and collectEVar (Gss, G, Gl, (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) =
      if (!TableParam.strengthen) then 
	collectEVarStr (Gss, G, Gl, (X, s), K, DupVars, flag, d) 
      else 
        if isId(s) (* equalCtx (compose'(Gl, G), s, GX, s)  *)
	  then (* X is fully applied *)
	    collectEVarFap (Gss, G, Gl, (X, s), K, DupVars, flag, d)
	else 
	  (* X is not fully applied *)
	  collectEVarNFap (Gss, G, Gl, (X, s), K, DupVars, flag, d)
	  
    (* collectDec (Gss, G, (x:V, s), K, DupVars, flag) = (K', DupVars')

       Invariant: 
       If    G |- s : G1     G1 |- V : L
            Gs |- ss : G
       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in (V, s)
       and DupVars'' contains all duplicates in (S, s)
    *)
    and collectDec (Gss, G,(I.Dec (_, V), s), K, DupVars, flag, d) =
          collectExp (Gss, G, I.Null, (V, s), K, DupVars, flag, d)
	  

    (* collectSub (G, s, K, DupVars, flag) = (K', DupVars)

       Invariant: 
       If    G |- s : G1    
       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in s
       and DupVars'' contains all duplicates in s
    *)

    and collectSub (Gss, G, Gl, I.Shift _, K, DupVars, flag, d) = (K, DupVars)
      | collectSub (Gss, G, Gl, I.Dot (I.Idx _, s), K, DupVars, flag, d) = collectSub (Gss, G, Gl, s, K, DupVars, flag, d)
      | collectSub (Gss, G, Gl, I.Dot (I.Exp (X as I.EVar (ref (SOME U), _, _, _)), s), K, DupVars, flag, d) =      
        let
	  val U' = Whnf.normalize (U, I.id) (* inefficient? *)
	  val (K', DupVars') = collectExp (Gss, G, Gl, (U', I.id), K, DupVars, flag, d)
	in 
	  collectSub (Gss, G, Gl, s, K', DupVars', flag, d)
	end 

      | collectSub (Gss, G, Gl, I.Dot (I.Exp (U as I.AVar (ref (SOME U'))), s), K, DupVars, flag, d) =      
        let
	  val (K', DupVars') = collectExp (Gss, G, Gl, (U', I.id), K, DupVars, flag, d)
	in 
	  collectSub (Gss, G, Gl, s, K', DupVars', flag, d)
	end 

      | collectSub (Gss, G, Gl, I.Dot (I.Exp (I.EClo(U', s')), s), K, DupVars, flag, d) =      
        let
	  val U = Whnf.normalize (U',s') (* inefficient? *)
	  val (K', DupVars') = collectExp (Gss, G, Gl, (U, I.id), K, DupVars, flag, d)
	in 
	  collectSub (Gss, G, Gl, s, K', DupVars', flag, d)
	end 

      | collectSub (Gss, G, Gl, I.Dot (I.Exp (U), s), K, DupVars, flag, d) =      
        let
	  val (K', DupVars') = collectExp (Gss, G, Gl, (U, I.id), K, DupVars, flag, d)
	in 
	  collectSub (Gss, G, Gl, s, K', DupVars', flag, d)
	end 

    (* collectCtx (Gss, G0, G, K, DupVars, flag) = (K', DupVars)
       Invariant:
       If G0 |- G ctx,
       then G0' = G0,G 
       and K' = K, K'' where K'' contains all EVars in G
       and DupVars' = DupVars, DupVars'' where DupVars'' contains all duplicates in G
    *)
    fun collectCtx (Gss, G0, I.Null, K, DupVars, flag, d) = (G0, K, DupVars)
      | collectCtx (Gss, G0, I.Decl (G, D), K, DupVars, flag, d) =
        let
	  val (G0', K', DupVars') = collectCtx (Gss, G0, G, K, DupVars, flag, d)
	  val (K'', DupVars'') = collectDec (Gss, G0, (D, I.id), K', DupVars', flag, d)
	in
	  (I.Decl (G0, D), K'', DupVars'')
	end

      

    (* abstractExpW (epos, apos, Vars, G, total, depth, (U, s), eqn) = (epos', apos', Vars', U', eqn')
      (abstraction and linearization of existential variables in (U,s))

       U' = {{U[s]}}_(K, Dup)

       Invariant:
       If     G |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   |Gl| = l
       and   |G| = depth
       and   Dup, K  ||- U and Dup, K ||- V

       and Vars'  = Vars, Vars'' 
           where Vars' contains pairs (i, EV X) of all EVars (EV X) together with 
           their corresponding bvar-index i in (U,s)

       and   K ~ Vars' (we can obtain K from Vars' by dropping the first component of 
             each pair (i, EV X) in Vars' )
       
       and epos = (total(K) + l) - #replaced expressions in U    (generate no additional constraints)
       and apos = (total(Dup) + l) - #replaced expressions in U  (generate additional constraints (avars))

       and {{Dup}} {{K}} {{G}}, G |- U' : V'
       and eqn' = eqn, eqn'' where eqn'' are residual equations relating between elements 
           in {{K}} and {{Dup}}

       and . ||- U' and . ||- V'
       and   U' is in nf 

       flag indicates whether we use linearization or not.

    *)
    fun abstractExpW (flag, Gs, posEA, Vars, G, total, depth, (U as I.Uni (L), s), eqn) = 
        (posEA, Vars, U, eqn)
      | abstractExpW (flag, Gs, posEA, Vars, G, total, depth, (I.Pi ((D, P), V), s), eqn) =
        let
	  val (posEA', Vars', D, eqn1) = abstractDec (flag, Gs, posEA, Vars, G, total, depth, (D, s), eqn)
	  val (posEA'', Vars'', V', eqn2) = abstractExp (flag, Gs, posEA', Vars', G, total + 1, depth + 1, (V, I.dot1 s), eqn1)
	in 
          (posEA'', Vars'', piDepend ((D, P), V'),eqn2)
	end 
      | abstractExpW (flag, Gs, posEA, Vars, G, total, depth, (I.Root (H, S) ,s), eqn) =
	let
	  val (posEA', Vars', S, eqn') = abstractSpine (flag, Gs, posEA, Vars, G, total, depth, (S, s), eqn)
	in 
	  (posEA', Vars', I.Root (H, S), eqn')
	end
      | abstractExpW (flag, Gs, posEA, Vars, G as (G', Gl), total, depth, (I.Lam (D, U), s), eqn) =
	let
	  val (posEA', Vars', D', eqn1) = abstractDec (false, Gs, posEA, Vars, G, total, depth, (D, s), eqn)
	  val (posEA'', Vars'', U', eqn2) = abstractExp (flag, Gs, posEA', Vars', (G', I.Decl(Gl, D')), total + 1, depth + 1, (U, I.dot1 s), eqn1)
	in 
          (posEA'', Vars'', I.Lam (D',U' ), eqn2)
	end
      | abstractExpW (flag, Gs as (Gss, ss), posEA as (epos, apos), Vars, G, total, depth, (X as I.EVar (_, GX, VX, _), s), eqn) =	  
	(* X is possibly strengthened ! *)
	if  isId(I.comp(ss, s))  (* equalCtx (Gs, I.id, GX, I.id)*)
	   then  (* X is fully applied *)
	     ((* print " \t abstract over X -- X fully applied\n";*)
	     abstractEVarFap (flag, Gs, posEA, Vars, G, total, depth, (X, s), eqn))
	 else 
	   (* s =/= id, i.e. X is not fully applied *)	
	   ((* print " \t abstract over X -- X not fully applied\n";*)
	  abstractEVarNFap (flag, Gs, posEA, Vars, G, total, depth, (X, s), eqn))
		  
(*      | abstractExpW (posEA, Vars, Gl, total, depth, (X as I.FgnExp (cs, ops), s), eqn) =  *)
(*	let
	  val (X, _) = #map(ops) (fn U => abstractExp (posEA, Vars, Gl, total, depth, (U, s), eqn))
	in 	  abstractFgn (posEA, Vars, Gl, total, depth, X, eqn)
	end  
*)


    (* abstractExp (posEA, Vars, Gl, total, depth, (U, s)) = U'
     
       same as abstractExpW, but (U,s) need not to be in whnf 
    *)
    and abstractExp (flag, Gs, posEA, Vars, G, total, depth, Us, eqn) = 
        abstractExpW (flag, Gs, posEA, Vars, G, total, depth, Whnf.whnf Us, eqn)

    and abstractEVarFap (flag, Gs, posEA as (epos, apos), Vars, G as (G', Gl), total, depth, (X, s), eqn) = 
        (case (member (eqEVar X) Vars) of
	   SOME(i) =>  (* we have seen X before *)	    
	     (if flag then 		    
	       let
		 val _ = print "abstract over fap X (duplicate) flag = true\n";
		 val _ = print ("BV = " ^ Int.toString(apos + total) ^ "\n")
		 val _ = print ("UNIFY : BV " ^ Int.toString(i + depth)) 
		 val _ = print ("= BV " ^ Int.toString(apos + depth) ^ "\n")
		 val BV = I.BVar(apos + total) 
		 val BV' = I.BVar(i + depth)    
		 val BV1 = I.BVar(apos + depth) 		   
		 val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos - 1), Vars, G, total, depth, s, I.Nil, eqn)
	       in 
		 (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil), eqn1))
	       end 	 
	     else 
	       let
(*		 val _ = print "abstract over fap X (duplicate) flag = false\n";
		 val _ = print ("i = " ^ Int.toString(i) ^ "\n")
		 val _ = print ("BV = " ^ Int.toString(i + total) ^ "\n")*)
		 val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars, G, total, depth, s, I.Nil, eqn)
	       in 
		 (posEA', Vars', I.Root(I.BVar(i + total), S), eqn1)
	       end) 
	 | NONE => 
	       let
(*		 val _ = print "abstract over fap X (seen for first time) \n";
		 val _ = print ("epos " ^ Int.toString (epos) ^ "\n")
		 val _ = print ("total " ^ Int.toString (total) ^ "\n")
		 val _ = print ("BV = " ^ Int.toString(epos + total) ^ "\n")*)
		 val BV = I.BVar(epos + total) 
		 val pos = (epos - 1, apos)
		 val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, pos, I.Decl(Vars, (epos, EV X)), G, total, depth, s, I.Nil, eqn)
	       in 
		 (posEA', Vars', I.Root(BV, S), eqn1)
	       end)

    and abstractEVarNFap (flag, Gs, posEA as (epos, apos), Vars, G as (G', Gl), total, depth, (X, s), eqn) = 
        (case (member (eqEVar X) Vars) of
	   SOME(i) =>  (* we have seen X before *)	    
	     if flag 
	       then 
		 let
(*		 val _ = print "abstract over nfap X (duplicate) flag = true\n";
		 val _ = print ("BV = " ^ Int.toString(apos + total) ^ "\n")
		 val _ = print ("UNIFY : BV " ^ Int.toString(i + depth) ^ " = ")
		 val _ = print ("BV " ^ Int.toString(apos + depth) ^ "\n") *)
		 val BV = I.BVar(apos + total) 
		 val BV' = I.BVar(i + depth)   
		 val BV1 = I.BVar(apos + depth)
		     
		 val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos - 1), Vars, G, total, depth, s, I.Nil, eqn)
		 in 
		   (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil ), eqn1))
		 end 	  
	     else 
	       let
(*		 val _ = print ("abstract over nfap X (duplicate) flag = false\n")
		 val _ = print ("i = " ^ Int.toString i ^ "\n")
		 val _ = print ("total = " ^ Int.toString total ^ "\n")
		 val _ = print ("BV = " ^ Int.toString(i + total) ^ "\n")*)
		 val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars, G, total, depth, s, I.Nil, eqn)

	       in 
		 (posEA', Vars', I.Root(I.BVar(i + total), S), eqn1)
	       end 
	 | NONE => 
	   (if flag 
	      then 		  
		let
(*		  val _ = print "abstract over nfap X (see for first time) (flag = true)\n";
		  val _ = print ("BV = " ^ Int.toString(apos + total) ^ "\n")
		  val _ = print ("BV " ^ Int.toString(epos + depth))
		  val _ = print ("= BV " ^ Int.toString(apos + depth) ^ "\n")*)
		  val BV = I.BVar(apos + total)
		  val BV' = I.BVar(epos + depth)  
		  val BV1 = I.BVar(apos + depth)  
		  val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos - 1, apos - 1),  I.Decl(Vars, (epos, EV X)), G, total, depth, s, I.Nil, eqn) 
		in 
		  (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil), eqn1))
		end
	    else 
	      let
(*		val _ = print "abstract over nfap X (see for first time) (flag = false)\n";
		 val _ = print ("BV = " ^ Int.toString(epos + total) ^ "\n")*)
		val BV = I.BVar(apos + total)
		val BV' = I.BVar(epos + total + depth)  
		val BV1 = I.BVar(apos + total + depth)  
		val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos - 1, apos),  I.Decl(Vars, (epos, EV X)), G, total, depth, s, I.Nil, eqn) 
	      in 
		(posEA', Vars', I.Root(I.BVar(epos+total), S), eqn1)
	      end
		 ))	   
		
    (* abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, s, S, eqn) = (posEA', Vars', S', eqn')

       (implicit raising)
       (for posEA, Vars, eqn explanation see above)

       let K* = K, Dup

       S' = {{s}}_K* @@ S

       Invariant:
       If    G, G |- s : G1   
       and  |G| = depth
       and   {{Dup}} {{K}} ||- s
       then {{Dup}} {{K}}, G, G |- S' : {G1}.W > W   (for some W)
       and  . ||- S' 
    *)
    and abstractSub (flag, Gs, posEA, Vars, G, total, depth, I.Shift (k), S, eqn) = 
	if (k + depth) < (depth + total)
	  then abstractSub (flag, Gs, posEA, Vars, G, total, depth, I.Dot (I.Idx (k+1), I.Shift (k+1)), S, eqn)
	else (* k = depth *) (posEA, Vars, S, eqn)
      | abstractSub (flag, Gs, posEA, Vars, G, total, depth, I.Dot (I.Idx (k), s), S, eqn) =
	  abstractSub (flag, Gs, posEA, Vars, G, total, depth, s, I.App (I.Root (I.BVar (k), I.Nil), S), eqn)
      | abstractSub (flag, Gs, posEA, Vars, G, total, depth, I.Dot (I.Exp (U), s), S, eqn) =
	  let
	    val (posEA', Vars', U', eqn') = abstractExp (flag, Gs, posEA, Vars, G, total, depth, (U, I.id), eqn)
	  in 
	    abstractSub (flag, Gs, posEA', Vars', G, total, depth, s, I.App (U', S), eqn')
	  end 
 

    (* abstractSpine (flag, Gs, posEA, Vars, G, total, depth, (S, s), eqn) = (posEA', Vars', S', eqn')
       where S' = {{S[s]}}_K*   and K* = K, Dup

       Invariant:
       If   Gl, G |- s : G1     G1 |- S : V > P 
       and  K* ||- S
       and  |G| = depth

       then {{K*}}, G, G |- S' : V' > P'
       and  . ||- S'
    *)
    and abstractSpine (flag, Gs, posEA, Vars, G, total, depth, (I.Nil, _), eqn)  = 
        (posEA, Vars, I.Nil, eqn)
      | abstractSpine (flag, Gs, posEA, Vars, G, total, depth, (I.SClo (S, s'), s), eqn) = 
	  abstractSpine (flag, Gs, posEA, Vars, G, total, depth, (S, I.comp (s', s)), eqn)
      | abstractSpine (flag, Gs, posEA, Vars, G, total, depth, (I.App (U, S), s), eqn) =
	  let
	    val (posEA', Vars', U', eqn') = abstractExp (flag, Gs, posEA, Vars, G, total, depth, (U ,s), eqn)
	    val (posEA'', Vars'', S', eqn'') = abstractSpine (flag, Gs, posEA', Vars', G, total, depth, (S, s), eqn')
	  in 
	    (posEA'', Vars'', I.App (U', S'), eqn'')
	  end 


    (* abstractSub' (flag, Gs, epos, K, G, total, depth, s) = s'      (implicit raising) 

        Invariant:  
        If   G |- s : G1    
       and  |G| = depth 
       and  K ||- s 
       and {{K}}, G |- {{s}}_K : G1
       then Gs, G |- s' : G1    where  s' == {{s}}_K

	 *) 
       
    and abstractSub' (flag, Gs, evartotal, posEA, Vars, G, total, d, I.Shift (k), eqn) =  
        if k < d
	  then 
	    (posEA, Vars, I.Dot(I.Idx(k+1), I.Shift (k+1)), eqn) 
	else 
	  (posEA, Vars, I.Shift(k + evartotal), eqn)
      | abstractSub' (flag, Gs, evartotal, posEA, Vars, G, total, d, I.Dot (I.Idx (k), s), eqn) =
	  let
	    val (posEA', Vars', s', eqn') = abstractSub' (flag, Gs, evartotal, posEA, Vars, G, total, d, s, eqn)
	  in 
	    (posEA', Vars', I.Dot(I.Idx(k),s'), eqn')
	  end 
      | abstractSub' (flag, Gs, evartotal, posEA, Vars, G, total, d, I.Dot (I.Exp (U), s), eqn) =
	  let
	    val (posEA', Vars', s', eqn') = abstractSub' (flag, Gs, evartotal, posEA, Vars, G, total, d, s, eqn) 
	    val (posEA'', Vars'', U', eqn'') = abstractExp (false, Gs, posEA', Vars', (G, I.Null), total, d, (U, I.id), eqn') 	

	  in 
	    (posEA'', Vars'', I.Dot(I.Exp(U'), s'), eqn'')
	  end 



    (* abstractDec (flag, Gs, posEA, Vars, G, total, depth, (x:V, s)) = (posEA', Vars', x:V', eqn')
       where V = {{V[s]}}_K*

       Invariant:
       If   G |- s : G1     G1 |- V : L
       and  K* ||- V
       and  |G| = depth

       then {{K*}}, G |- V' : L
       and  . ||- V'
    *)
    and abstractDec (flag, Gs, posEA, Vars, G, total, depth, (I.Dec (x, V), s), eqn) =
      let
	val (posEA', Vars', V', eqn') = abstractExp (flag, Gs, posEA, Vars, G, total, depth, (V, s), eqn)
      in 
	(posEA', Vars', I.Dec (x, V'), eqn')
      end 


    (* abstractCtx (flag, Gs, posEA, Vars, total, depth, G, eqn) = (posEA', Vars', G', total, depth', eqn')
       where G' = {{G}}_K

       Invariants:
       If Glocal |- G ctx
       and K ||- G
       and |Glocal| = depth
       then {{K}}, Glocal |- G' ctx
       and . ||- G'
       and |Glocal,G| = depth'
       and |G| = total 
       and epos = current epos
       and apos = current apos
    *)
    fun abstractCtx (flag, Gs, posEA, Vars, total, depth, I.Null, eqn) = 
          (posEA, Vars, I.Null, eqn)
      | abstractCtx (flag, Gs, posEA, Vars, total, depth, I.Decl (G, D), eqn) =
        let
	  val (posEA', Vars', G', eqn') = abstractCtx (flag, Gs, posEA, Vars, total - 1, depth, G, eqn)
	  val (posEA'', Vars'', D', eqn'') = abstractDec (flag, Gs, posEA', Vars', (G, I.Null), total , depth, (D, I.id), eqn') (* ? *)
	in
	  (posEA'', Vars'', I.Decl (G', D'), eqn'')
	end


    (* --- here Mon Sep  9 11:02:26 2002 -bp *)
    (* createEVarCtx (G, K, s, eqn) = (posEA', G', s', eqn')

       where U[s] = [[K]] U

       Invariant: 
       If   {{K}} |- U : V 
       and  . ||- U
       and  . ||- V

       then U[s] = [[K]] U
       and  . |- U[s] : {{K}} V
       and  . ||- U[s]
    *)
    (* epos = apos = 0 ? *)
    fun createEVarCtx (Gs, epos, G, I.Null, s, total, eqn) = (epos, G, s, eqn)
      | createEVarCtx (Gs, epos, G, I.Decl (K', (_, EV (E as I.EVar (_, GX, VX, _)))),s, total, eqn) =
        let
	  val V' = raiseType (GX, VX)
          val (epos', G',s', eqn') = createEVarCtx (Gs, epos, G, K', s, total - 1, eqn)
	    (* note: apos and depth is irrelevant since we never create any residual eq. !*)
	  val ((epos', _), _, V'', eqn'') = abstractExp (false, Gs, (epos', 0),  K', (G, I.Null), (total - 1), 0, (V', I.id), eqn')
	  val G'' = I.Decl (G', I.decSub (I.Dec (NONE, V''), s))
	in
	  (epos', G'', I.dot1 s', eqn'')
	end       

    (* collapes into createEVar..if it is AV then create ADec if EVar then Dec
       no need to have two ctx one for AVars and one for EVars *)
    fun createDupCtx (G, Vars, I.Null, k) = G
      | createDupCtx (G, Vars, I.Decl (K', AV (E as I.EVar (ref NONE, GX, VX, _), d)), k) =
        let
          val G' = createDupCtx (G, Vars, K', k+1)
	in
	  I.Decl (G', I.ADec (SOME("AVar "^Int.toString k ^ "--" ^ Int.toString d), d)) 
	end       
      | createDupCtx (G, Vars, I.Decl (K', AV (E as I.EVar (_, GX, VX, _), d)), k) = 
	let
	  val _ = print "createDupCtx : AV (EVar...) is instantiated!\n"
          val G' = createDupCtx (G, Vars, K', k+1)
	in
	  I.Decl (G', I.ADec (SOME("AVar "^Int.toString k ^ "--" ^ Int.toString d), d)) 
	end       
	
      (* add case for foreign expressions *)

    (* lowerEVar' (G, V[s]) = (X', U), see lowerEVar *)
    fun lowerEVar' (X, G, (I.Pi ((D',_), V'), s')) =
        let
	  val D'' = I.decSub (D', s')
	  val (X', U) = lowerEVar' (X, I.Decl (G, D''), Whnf.whnf (V', I.dot1 s'))
	in
	  (X', I.Lam (D'', U))
	end
      | lowerEVar' (X, G, Vs') =
        let
	  val X' = X
	in
	  (X', X')
	end
    (* lowerEVar1 (X, V[s]), V[s] in whnf, see lowerEVar *)
    and (* lowerEVar1 (X, I.EVar (r, G, _, _), (V as I.Pi _, s)) = *)
      lowerEVar1 (X, I.EVar (r, G, _, _), (V as I.Pi _, s)) =
        let 
	  val (X', U) = lowerEVar' (X, G, (V,s))
	in
	  I.EVar(ref (SOME(U)), I.Null, V, ref nil)
	end
      | lowerEVar1 (_, X, _) = X

    (* lowerEVar (X) = X'

       Invariant:
       If   G |- X : {{G'}} P
            X not subject to any constraints
       then G, G' |- X' : P

       Effect: X is instantiated to [[G']] X' if G' is empty
               otherwise X = X' and no effect occurs.
    *)
    and 
      lowerEVar (E, X as I.EVar (r, G, V, ref nil)) = lowerEVar1 (E, X, Whnf.whnf (V, I.id))
      | lowerEVar (E, I.EVar _) =
        (* It is not clear if this case can happen *)
        (* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
        raise Error "abstraction : LowerEVars: Typing ambiguous -- constraint of functional type cannot be simplified"


    fun abstractKSubEVar (I.Null, s) = s
      | abstractKSubEVar (I.Decl (K', (_, EV (E as I.EVar (I as (ref NONE), GX, VX, cnstr)))),s) =
        let
	  val V' = raiseType (GX, VX) (* redundant ? *)
	  val s' = abstractKSubEVar (K', s)
	  val X = lowerEVar1 (E, I.EVar(I, I.Null, V', cnstr), Whnf.whnf(V', I.id))  
	in
	  I.Dot(I.Exp(X), s')      
	end

    fun abstractKSubAVars (I.Null, s) = s
(*       | abstractKSubAVars (I.Decl (Vars', (AV (E as I.EVar (I (* as (ref NONE)*), GX, VX, cnstr), d))), s) =*)
(* is this sound??? Wed Jan 22 14:04:03 2003 -bp *)
      | abstractKSubAVars (I.Decl (Vars', (AV (E as I.EVar (I, GX, VX, cnstr), d))), s) =
        let
	  val s' = abstractKSubAVars (Vars', s)
	  val X' as I.AVar(r) = I.newAVar () 
	in
	  I.Dot(I.Exp(I.EClo(X', I.Shift(~d))), s')    
	end

(*      | abstractKSubAVars (I.Decl (Vars', (AV (E as I.EVar (I, GX, VX, cnstr), d))), s) =
	let
	  val _ = 	print "abstractKSubAVars: AVar is instantiated!\n"
	in
	  raise Error "abstractKSubAVars: AVar is instantiated!\n"
	end *)
  in

  (* abstractEVarCtx (G, p, s) = (G', D', U', s')

     if G |- p[s]
        and s contains free variables X_n .... X_1
     then 
        
       D', G' |- U'  
       where D' is the abstraction over 
       the free vars X_n .... X_1
 
       and s' is a substitution the free variables
            X_n .... X_1, s.t. 

       G' |- s' : D', G'        

       G' |- U'[s']  is equivalent to G |- p[s]

       Note: G' and U' are possibly strengthened
   *)

    val abstractEVarCtx = 
      (fn (G, p, s) => 
       let
	 val (Gs, ss, d) =  if (!TableParam.strengthen) then 
	                  let
			    val w' = Subordinate.weaken (G, I.targetFam p)
			    val iw = Whnf.invert w' 
			    val G' = Whnf.strengthen (iw, G)
			    val d' = I.ctxLength (G')
			  in		
			    (G', iw, d')
			  end
			 else 
			   (G, I.id, I.ctxLength(G))
	 (* Kdp contains all EVars in G, G0' = G  *)	
	 (* DupVars contains all duplicate EVars and Fgn in G,  G0' = G 
	    in general expressions which need to be replaced to obtain a 
	    linear assignable expression *)	
	 val (G0', Kdp, DupVars) = collectCtx ((Gs, ss), I.Null, G, I.Null, I.Null, true, 0)
	 val _ = print "Collect Ctx done\n";
	 val _ = print ("|DupVars| = " ^ Int.toString (I.ctxLength(DupVars)) ^ "\n")
	 (* K contains all EVars in (p,s) and G *)
	 (* DupVars' contains all duplicate EVars in (p,s) and G *)
	 val (K, DupVars') = collectExp((Gs, ss), G, I.Null, (p, s), Kdp, DupVars, true, d)
(*	 val _ = print "Abstract ctx\n";*)
	 val epos = I.ctxLength(K)
	 val apos = I.ctxLength(DupVars')
(*	 val _ = print ("epos " ^ Int.toString (epos) ^ "\n")
	 val _ = print ("apos " ^ Int.toString (apos+epos) ^ "\n")*)
	 val (posEA', Vars', G', eqn) = abstractCtx (true, (Gs,ss), (epos, apos+epos), I.Null, d - 1, d, G, TableParam.Trivial) 
(*	 val _ = print "abstractCtx done\n"*)
	 val (epos', apos') = posEA'
(*	 val _ = print ("epos' " ^ Int.toString (epos') ^ "\n")
	 val _ = print ("apos' " ^ Int.toString (apos') ^ "\n")
	 val _ = print "abstractExp \n"*)

	 val (posEA'', Vars'', U', eqn') = abstractExp (true, (Gs, ss), posEA', Vars',  (G, I.Null), d, d, (p,s), eqn)
(*	 val _ = print "abstractExp done\n"*)
	 (* Vars'' contains all EVars occuring in G and p[s] once *)
         (* by invariant epos'' = apos'' = 0 *)
	 val (epos'', apos'') = posEA''
(*	 val _ = print ("epos'' " ^ Int.toString (epos'') ^ "\n")
	 val _ = print ("apos'' " ^ Int.toString (apos'') ^ "\n")
	 val _ = print ("d " ^ Int.toString (d) ^ "\n")*)

	 val DAVars = createDupCtx (I.Null, Vars'', DupVars', 0)  
(*	 val _ = print "createEVarCtx\n"
	 val _ = print ("total = " ^ Int.toString (epos+apos-1) ^ "\n")*)
	 val ( _, DEVars,I.Shift(0), eqn2) = createEVarCtx ((Gs, ss), epos'', I.Null, Vars'', I.id, 0 (* epos + apos - 1 *), eqn')
(*	 val _ = print "abstractKSubAVars\n"*)
	 (* abstract over the assignable variables *)
	 val s' = abstractKSubAVars (DupVars', I.id)
(*	 val _ = print "abstractKSubEVars\n"*)
	 val s'' = abstractKSubEVar (Vars'', s')
(*	 val _ = print "DONE\n"*)
       in 		
	 if (!TableParam.strengthen) then 
	   let
	     val w' = Subordinate.weaken (G', I.targetFam U')
	     val iw = Whnf.invert w' 
	     val G'' = Whnf.strengthen (iw, G')
	   in		
	     (G'', DAVars, DEVars, U', eqn2, s'')
	   end
	 else 
	   (G', DAVars, DEVars, U', eqn2, s'')
       end)


  (* abstractAnswSub s = (Delta, s')
    
   if G |- s : Delta', G 
      s may contain free variables
    
   then 
  
    Delta, G |- s' : Delta', G
    where Delta contains all the 
    free variables from s

    D, G |- U 
       G |- s : D, G
       G[s] |- U[s]
    Dk, G |- s : D', G

   *)
    val abstractAnswSub = 
      (fn (G, s) => 
       let
(*	 val _ = print "abstractAnswSub\n"*)
	 val total = I.ctxLength (G)
	 val (K, DupVars) = collectSub((I.Null, I.id), I.Null, I.Null, s, I.Null, I.Null, false, 0)
	 val epos = I.ctxLength K
	 val apos = I.ctxLength DupVars	   
	 val evartotal = epos + apos
(*	 val _ = print ("epos " ^ Int.toString epos ^ "\n")
	 val _ = print ("apos " ^ Int.toString apos ^ "\n")*)
         (* total = length(G), depth = |Glocal|*)
	 val ((epos' (*0 *), _ (* 0 *)), Vars, s', eqn) = abstractSub' (false, (I.Null, I.id), evartotal, (epos, apos+epos), I.Null, G, 0 (* total *), 0(* total*), s, TableParam.Trivial)
(*	 val _ = print ("epos' " ^ Int.toString epos' ^ "\n")*)
(*	 val DAVars = createDupCtx (I.Null, Vars, DupVars, 0)  (* will have no avars! *)*)
	 val ( _, DEVars,_, _ (* trivial *)) = createEVarCtx ((I.Null, I.id), epos', I.Null, Vars, I.id, (* 0 *) (epos + apos -1), eqn)  
       in 
	 (DEVars, s')
       end)

    val raiseType = (fn (G, U) => 
		       raiseType (G, U)
			   )

  end
end;  (* functor AbstractTabled *)



