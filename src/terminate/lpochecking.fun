(* about lexicographic path orders *)
(* Based on Brigitte Pientka's code for reasoning *)
(* about structural orders *)
(* Modified by: Jeffrey Sarnat *)
 
functor LPOChecking  (structure Global : GLOBAL
		      (*! structure IntSyn' : INTSYN !*)
		      structure Whnf : WHNF
		      (*! sharing Whnf.IntSyn = IntSyn' !*)
	              structure Conv : CONV
		      (*! sharing Conv.IntSyn = IntSyn' !*)
	              structure Unify : UNIFY
		      (*! sharing Unify.IntSyn = IntSyn' !*)
	              structure Names : NAMES
		      (*! sharing Names.IntSyn = IntSyn' !*)
	              structure Index : INDEX
		      (*! sharing Index.IntSyn = IntSyn' !*)
	              structure Subordinate : SUBORDINATE
		      (*! sharing Subordinate.IntSyn = IntSyn' !*)
     		      structure Formatter : FORMATTER
	              structure Print : PRINT
		      (*! sharing Print.IntSyn = IntSyn' !*)
		      sharing Print.Formatter = Formatter
		      structure Order : ORDER
		      (*! sharing Order.IntSyn = IntSyn' !*)
		      (*! structure Paths  : PATHS !*)
		      structure Origins : ORIGINS
		      (*! sharing Origins.Paths = Paths !*)
		      (*! sharing Origins.IntSyn = IntSyn' !*)
		      (*! structure CSManager : CS_MANAGER !*)
		      (*! sharing CSManager.IntSyn = IntSyn' !*)
		      structure Lpo : LPO)
  :  CHECKING =
struct
  (*! structure IntSyn = IntSyn' !*)
structure Order = Order
(*! structure Paths = Paths !*)
		  
datatype Quantifier =        (* Quantifier to mark parameters *)
	 All                        (* Q ::= All                     *)
       | Exist                      (*     | Exist                   *)
       | And of Paths.occ	    (*     | And                     *)
		

(* If Q marks all parameters in a context G we write   G : Q               *)

datatype 'a Predicate = 
	 Less of 'a * 'a
       | Leq of 'a * 'a 
       | Eq of 'a * 'a 
       | Pi of IntSyn.Dec * 'a Predicate        

   (* Abbreviation *)
type order = (IntSyn.eclo * IntSyn.eclo) Order.Order  

(* reduction order assumptions (unordered) *)
type rctx = order Predicate list
	    
(* mixed prefix order contex *)
type qctx = Quantifier IntSyn.Ctx

exception Error of string
exception Unimp of string
		       
local
  structure I = IntSyn
  structure P = Paths
  structure N = Names
  structure F = Formatter
  structure R = Order
  structure L = Lpo		

  (* Reasoning about order relations *)
  (*
   OUTDATED
   Typing context        G  
   mixed prefix context  Q  := . | All | Existental

    Orders                0  := U[s1] : V[s2]
                               | Lex O1 ... On | Simul O1 ... On 
                                (lex, simul not supported for now)
    Order Relation        P  := O < O' | O <= O' | O = O' | Pi x:V. O

    Atomic Order Relation P' := U[s1] : V[s2] <  U'[s1'] : V'[s2'] | 
                                U[s1] : V[s2] <= U'[s1'] : V'[s2'] | 
			        U[s1] : V[s2] =  U'[s1'] : V'[s2'] 
   
    Order Relation Ctx    D  := . | R , D
    Atomic Order Rel. Ctx D' := . | R',  D'

    Invariant:

    sometimes we write G |- P as an abbreviation 
    
    if P = (O < O')    then G |- O and G |- O'
    if P = (O <= O')    then G |- O and G |- O'
    if P = (O = O')    then G |- O and G |- O'

    if O = Lex O1 .. On  then G |- O1 and ....G |- On
    if O = Simul O1 .. On  then G |- O1 and ....G |- On

    if O = U[s1] : V[s2] 
      then     G : Q
           and G |- s1 : G1, G1 |- U : V1
           and G |- s2 : G2   G2 |- V : L
           and G |- U[s1] : V[s2]  
     
  *)

   (*--------------------------------------------------------------------*)
   (* Printing atomic orders *)

  fun atomicPredToString (G, Less((Us, _), (Us', _))) = 
      Print.expToString(G, I.EClo(Us)) ^ " < " ^ 
      Print.expToString(G, I.EClo(Us'))
    | atomicPredToString (G, Leq((Us, _), (Us', _))) = 
      Print.expToString(G, I.EClo(Us)) ^ " <= " ^ 
      Print.expToString(G, I.EClo(Us'))
    | atomicPredToString (G, Eq((Us, _), (Us', _))) = 
      Print.expToString(G, I.EClo(Us)) ^ " = " ^ 
      Print.expToString(G, I.EClo(Us'))
      
  fun atomicRCtxToString (G, nil) = " "
    | atomicRCtxToString (G, O::nil) = atomicPredToString (G, O)
    | atomicRCtxToString (G, O::D') = 
      atomicRCtxToString (G, D') ^ ", " ^ atomicPredToString (G, O)
      
   (*--------------------------------------------------------------------*)
   (* shifting substitutions *)

   (* shiftO O f = O'

      if O is an order 
         then we shift the substitutions which are associated
	 with its terms by applying f to it
    *)

    fun shiftO (R.Arg ((U, us), (V, vs))) f = 
	    R.Arg ((U, (f us)), (V, (f vs)))
      | shiftO (R.Lex L) f = R.Lex (map (fn O => shiftO O f) L)
      | shiftO (R.Simul L) f = R.Simul (map (fn O => shiftO O f) L)

    fun shiftP (Less(O1, O2)) f = Less(shiftO O1 f, shiftO O2 f)
      | shiftP (Leq(O1, O2)) f = Leq(shiftO O1 f, shiftO O2 f)
      | shiftP (Eq(O1, O2)) f = Eq(shiftO O1 f, shiftO O2 f)
      | shiftP (Pi(D as I.Dec(X,V), P)) f = Pi(D, shiftP P f) 

    fun shiftRCtx Rl f = map (fn p => shiftP p f) Rl

    fun shiftArg (Less (((U1, s1), (V1, s1')), ((U2, s2), (V2, s2')))) f = 
          Less (((U1, (f s1)), (V1, (f s1'))), (((U2, (f s2)), (V2, (f s2')))))
      | shiftArg (Leq (((U1, s1), (V1, s1')), ((U2, s2), (V2, s2')))) f = 
          Leq (((U1, (f s1)), (V1, (f s1'))), (((U2, (f s2)), (V2, (f s2')))))
      | shiftArg (Eq (((U1, s1), (V1, s1')), ((U2, s2), (V2, s2')))) f = 
          Eq (((U1, (f s1)), (V1, (f s1'))), (((U2, (f s2)), (V2, (f s2')))))

    fun shiftACtx Rl f = map (fn p => shiftArg p f) Rl

   (*--------------------------------------------------------------------*)
   (* Printing *)

    fun fmtOrder (G, O) =
        let
	  fun fmtOrder' (R.Arg (Us as (U, s), Vs as (V, s'))) =
	        F.Hbox [F.String "(", Print.formatExp (G, I.EClo Us), F.String ")"]
	    | fmtOrder' (R.Lex L) =
		F.Hbox [F.String "{", F.HOVbox0 1 0 1 (fmtOrders L), F.String "}"]
	    | fmtOrder' (R.Simul L) =
		F.Hbox [F.String "[", F.HOVbox0 1 0 1 (fmtOrders L), F.String "]"]
	  
	  and fmtOrders [] = []
	    | fmtOrders (O :: []) = fmtOrder' O :: []
	    | fmtOrders (O :: L) = fmtOrder' O :: F.Break :: fmtOrders L
	in
	  fmtOrder' O
	end

    fun fmtComparison (G, O, comp, O') =
        F.HOVbox0 1 0 1 [fmtOrder (G, O), F.Break, F.String comp, F.Break, fmtOrder (G, O')]

    fun fmtPredicate' (G, Less(O, O')) = fmtComparison (G, O, "<", O')
      | fmtPredicate' (G, Leq(O, O'))  = fmtComparison (G, O, "<=", O')
      | fmtPredicate' (G, Eq(O, O'))  = fmtComparison (G, O, "=", O')
      | fmtPredicate' (G, Pi(D, P))  =  (* F.String "Pi predicate"  *)
          F.Hbox [F.String "Pi ", fmtPredicate' (I.Decl (G, D), P)]   

    fun fmtPredicate (G, P) = fmtPredicate' (Names.ctxName G, P) 

    fun fmtRGCtx' (G, nil) = ""
      | fmtRGCtx' (G, [P]) = 
	F.makestring_fmt(fmtPredicate' (G, P) )
      | fmtRGCtx' (G, (P :: Rl)) = 
	F.makestring_fmt(fmtPredicate' (G, P)) ^ " ," ^ fmtRGCtx' (G, Rl)
	
    fun fmtRGCtx (G, Rl) = fmtRGCtx' (Names.ctxName G, Rl) 

	
    (*--------------------------------------------------------------------*)

    fun isUniversal (All) = true
      | isUniversal (Exist) = false
      | isUniversal (Exist') = false

    fun isExistential (All) = false
      | isExistential (Exist) = true
      | isExistential (Exist') = true
    fun lookstuffup _ = false

    datatype headCase = LT | EQ | SUB | SUBORD | LOOKUP

    fun rootCompare (Q, (h, S1, s1),
		     Vs as (V as I.Root ((I.Const a), S2), s2),
		     (h', S1', s1'),
		      Vs' as (V' as I.Root ((I.Const a'), S2'), s2')) =
	let
	  val typesDecide = fn () => if (Subordinate.below (a,a')) then LT 
				     else SUB
	in
	
	  (case (h,h')
	    of (I.Const cid, I.Const cid') =>
	       (case (L.orderCompare (cid, cid'))
		 of (L.LT) => LT
		  | (L.EQ) => EQ
		  | (L.NLE) => SUB)
	     | (I.Const cid, I.BVar n') => 
	       if (isExistential (I.ctxLookup (Q, n'))) then SUBORD
	       else (typesDecide())
	     | (I.BVar n, I.Const cid') => 
	       (* if n is existential then n and c aren't comparable *)
	       if (isExistential (I.ctxLookup (Q, n))) then SUB 
	       else typesDecide()
	     | (I.BVar n, I.BVar n') => 
	       let
		 val hExist = isExistential (I.ctxLookup (Q, n))
		 val h'Exist = isExistential (I.ctxLookup (Q, n'))
	       in
		 if (h'Exist andalso hExist) then LOOKUP
		 else if h'Exist then SUBORD
		 else if (Subordinate.below (a, a')) then LT
		 else if (Conv.conv (Vs, Vs')) then EQ
		 else LOOKUP
	       end
		 )
	end

    fun proveLt ((G,Q), D, (Us as (I.Lam(_, U), s1), 
			    Vs as (I.Pi((Dec, _), V), s2)),
		 ((U', s1'), (V',s2'))) = 
	let
	  val G1 = I.Decl (G, N.decLUName (G, Dec))
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftACtx D (fn s => I.comp(s, I.shift))
	  val UsVs1 = ((U, I.dot1 s1), (V, I.dot1 s2))
	  val UsVs1' = ((U', I.comp (s1', I.shift)), 
			(V', I.comp (s2', I.shift)))
	in
	  proveLt ((G1,Q1), D, UsVs1, UsVs1')
	end 

      | proveLt ((G, Q), D, ((U as I.Root _, s1),
			    (V as I.Root _, s2)),
			   ((I.Lam (_, U'), s1'),
			    (I.Pi ((Dec', _), V'), s2'))) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, Dec'))
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftACtx D (fn s => I.comp(s, I.shift))
	  val UsVs1 = ((U, I.comp (s1, I.shift)), 
		       (V, I.comp (s2, I.shift)))
	  val UsVs1' =((U', I.dot1 s1'), (V, I.dot1 s2'))
	in
	  proveLt ((G1,Q1), D1, UsVs1, UsVs1')
	end

      (* currently ignores the possibility of definitions 
         at both type and term level *) 
      | proveLt (GQ as (G,Q), D, ((U as I.Root (h, S1), s1),
			    Vs as (V as I.Root ((I.Const a), S2), s2)),
		 ((U' as I.Root (h', S1'), s1'),
		  Vs' as (V' as I.Root ((I.Const a'), S2'), s2'))) =
	let
	  val ord = rootCompare (Q, (h, S1, s1), Vs,
				 (h', S1', s1'), Vs')
	in
	  (case ord
	    of LT => 
	      let
		val (I.Root (_, S1n), _) = Whnf.whnf (U, s1)
	      in
		proveLtAll (I.constType a) (GQ, D, S1n, U')
	      end
		)
	end

    and proveLtAll _ _ = false
    and proveLeSome _ = false
    and proveLex _ = false



		

    fun proveLtO (GQ, D, R.Arg UsVs, R.Arg UsVs') = proveLt (GQ, D, UsVs, UsVs')
      | proveLtO _ =
	raise Error "Lexicographic and Simultaneous orders not supported"

    fun proveEqO _ = false

    fun rightDecompose (GQ, D, Less (O,O')) = 
	proveLtO (GQ, D, O, O')
      | rightDecompose (GQ, D, Leq(O,O')) =
	proveLtO (GQ, D, O, O') orelse proveEqO(GQ, D, O, O')
      | rightDecompose (GQ, D, Eq(O,O')) =
	proveEqO (GQ, D, O, O')
      | rightDecompose (gq as (g,q), d, Pi (dec, p)) =
	let
	  val g1 = I.Decl (g, N.decLUName (g, dec))
	  val q1 = I.Decl (q, All)
	  val d1 = shiftACtx d (fn s => I.comp(s, I.shift))
	  val p1 = shiftP p I.dot1
	in
	  rightDecompose ((g1,q1), d1, p1)
	end

    (* leftDecompose (G, Q, D, D', P) = B

      if G : Q and  
         D --> P  where D might contain orders (Pi)

      then D' --> P 
           where all orders in D' are atomic

      D' accumulates all orders which are maximally unfolded,
      but do not contain any EVars

      maximally unfolded orders not containing EVars are:

      Less: R < R'
      Eq : R = R
      
      R := Root(n, S)  where n is existentially quantified in Q
      S := . | App(U, S) where U is in normal form
      
     *) 

    fun leftDecompose (GQ as (G, Q), nil, D', P) = rightDecompose (GQ, D', P)
     (* less *)
     | leftDecompose (GQ as (G, Q), 
		      (Less (R.Arg ((I.Lam (_, U), s1), 
				   (I.Pi ((Dec, _), V), s2)), 
				   R.Arg ((U', s1'), (V', s2')))
		       :: D), D', P) =
       let
	 val G1 = I.Decl (G, N.decLUName (G, I.decSub (Dec, s2)))
	 val Q1 =  I.Decl (Q, All)
	 val D1 = shiftRCtx D (fn s => I.comp(s, I.shift))
	 val D1' = shiftACtx D' (fn s => I.comp(s, I.shift))  
	 val UsVs1 = ((U, I.dot1 s1), (V, I.dot1 s2)) 
	 val UsVs1' = ((U', I.comp (s1', I.shift)), (V', I.comp (s2', I.shift)))
	 val P' = shiftP P (fn s => I.comp(s, I.shift))
       in
	 leftDecompose ((G1, Q1), D1, (Less (UsVs1, UsVs1')):: D1', P')
       end

    | leftDecompose (GQ as (G, Q), 
		      (Less (R.Arg (((U as I.Root _), s1), 
			     ((V as I.Root _), s2)),
			     R.Arg ((I.Lam (_, U'), s1'), 
				    (I.Pi ((Dec', _), V'), s2')))
		       :: D), D', P) =
       let
	 val G1 = I.Decl (G, N.decLUName (G, I.decSub (Dec', s2')))
	 val Q1 =  I.Decl (Q, All)
	 val D1 = shiftRCtx D (fn s => I.comp(s, I.shift))
	 val D1' = shiftACtx D' (fn s => I.comp(s, I.shift))  
	 val UsVs1 = ((U, I.comp (s1, I.shift)), (V, I.comp (s2, I.shift)))
	 val UsVs1' = ((U', I.dot1 s1'), (V', I.dot1 s2')) 
	 val P' = shiftP P (fn s => I.comp(s, I.shift))
       in
	 leftDecompose ((G1, Q1), D1, (Less (UsVs1, UsVs1')):: D1', P')
       end



     | leftDecompose (GQ, (Less(R.Lex O, R.Lex O') :: D), D', P) =
       raise Error 
	       ("Lexicographic orders not currently supported, " ^
		"try hacking them up with a pair instead")

     | leftDecompose (GQ, (Less(R.Simul O, R.Simul O') :: D), D', P) =
             raise Error 
	       ("Simultaneous orders not currently supported, " ^
		"try hacking them up with a pair instead")

     (* le *)
		   
     | leftDecompose (GQ, (Leq (O, O')) :: D, D', P) =
       leftDecompose (GQ, (Less (O, O')) :: D, D', P) andalso
       leftDecompose (GQ, (Eq (O, O')) :: D, D', P)
(*

     | leftDecompose (GQ, (Leq(R.Lex O, R.Lex O') :: D), D', P) =
      raise Error 
	       ("Lexicographic orders not currently supported, " ^
		"try hacking them up with a pair instead")

     | leftDecompose (GQ, (Leq(R.Simul O, R.Simul O') :: D), D', P) =
       raise Error 
	       ("Simultaneous orders not currently supported, " ^
		"try hacking them up with a pair instead")
*)
     (* eq *)		
     | leftDecompose (GQ, (Eq(R.Arg UsVs, R.Arg UsVs') :: D), D', P) =
       raise Unimp ""

     | leftDecompose (GQ, (Eq(R.Lex O, R.Lex O') :: D), D', P) =
      raise Error 
	       ("Lexicographic orders not currently supported, " ^
		"try hacking them up with a pair instead")


     | leftDecompose (GQ, (Eq(R.Simul O, R.Simul O') :: D), D', P) =
       raise Error 
	       ("Simultaneous orders not currently supported, " ^
		"try hacking them up with a pair instead")


     | leftDecompose (GQ as (G, Q), (Pi(Dec, O) :: D), D', P) = 
       raise Unimp ("Reasoning about Pi orderings not implemnted yet")
      


    fun deduce (G, Q, D, P) = true
  in
    val deduce = deduce 
    val shiftRCtx = shiftRCtx
    val shiftPred = shiftP
  end (* local *)
end; (* functor checking  *)
