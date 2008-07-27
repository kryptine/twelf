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

(* This algorithm isn't type directed, so it would work just as well with
   type order = IntSyn.eclo Order.Order,
   but I'm using the same interface as the old checker for simplicity sake *)

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
  structure W = Whnf
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

  fun subToString (I.Shift n) = "^" ^ (Int.toString n)
    | subToString (I.Dot (I.Idx n, s)) = (Int.toString n) ^ "." ^ (subToString s)

  fun printSub s = print ((subToString s) ^ "\n")
      
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
      | shiftP (Pi(D as I.Dec(X,V), P)) f =  raise Unimp ""
	(* -js Sat Jul 26 16:34:04 2008 *)


    fun shiftRCtx Rl f = map (fn p => shiftP p f) Rl

    fun shiftArg (Less (((U1, s1), (V1, s1')), ((U2, s2), (V2, s2')))) f =
          Less (((U1, (f s1)), (V1, (f s1'))), (((U2, (f s2)), (V2, (f s2')))))
      | shiftArg (Leq (((U1, s1), (V1, s1')), ((U2, s2), (V2, s2')))) f =
          Leq (((U1, (f s1)), (V1, (f s1'))), (((U2, (f s2)), (V2, (f s2')))))
      | shiftArg (Eq (((U1, s1), (V1, s1')), ((U2, s2), (V2, s2')))) f =
          Eq (((U1, (f s1)), (V1, (f s1'))), (((U2, (f s2)), (V2, (f s2')))))


    fun shiftACtx Rl f = map (fn p => shiftArg p f) Rl



    (* my shifting *)


    fun shiftAP (Less((U, us), (U', us'))) f = Less ((U, f us), (U', f us'))
      | shiftAP (Leq((U, us), (U', us'))) f = Leq ((U, f us), (U', f us'))
      | shiftAP (Eq((U, us), (U', us'))) f = Eq ((U, f us), (U', f us'))
      | shiftAP (Pi(D, P)) f =
	Pi (I.decSub (D, f I.id), 
	    shiftAP P (f o I.dot1))

    fun shiftDCtx D f = map (fn p => shiftAP p f) D

    fun shiftOnce s = I.comp(s, I.shift)

    (*--------------------------------------------------------------------*)
(*    (\* Printing *\) *)

(*     fun fmtOrder (G, O) = *)
(*         let *)
(* 	  fun fmtOrder' (R.Arg (Us as (U, s), Vs as (V, s'))) = *)
(* 	        F.Hbox [F.String "(", Print.formatExp (G, I.EClo Us), F.String ")"] *)
(* 	    | fmtOrder' (R.Lex L) = *)
(* 		F.Hbox [F.String "{", F.HOVbox0 1 0 1 (fmtOrders L), F.String "}"] *)
(* 	    | fmtOrder' (R.Simul L) = *)
(* 		F.Hbox [F.String "[", F.HOVbox0 1 0 1 (fmtOrders L), F.String "]"] *)
	  
(* 	  and fmtOrders [] = [] *)
(* 	    | fmtOrders (O :: []) = fmtOrder' O :: [] *)
(* 	    | fmtOrders (O :: L) = fmtOrder' O :: F.Break :: fmtOrders L *)
(* 	in *)
(* 	  fmtOrder' O *)
(* 	end *)

(*     fun fmtComparison (G, O, comp, O') = *)
(*         F.HOVbox0 1 0 1 [fmtOrder (G, O), F.Break, F.String comp, F.Break, fmtOrder (G, O')] *)

(*     fun fmtPredicate' (G, Less(O, O')) = fmtComparison (G, O, "<", O') *)
(*       | fmtPredicate' (G, Leq(O, O'))  = fmtComparison (G, O, "<=", O') *)
(*       | fmtPredicate' (G, Eq(O, O'))  = fmtComparison (G, O, "=", O') *)
(*       | fmtPredicate' (G, Pi(D, P))  =  (\* F.String "Pi predicate"  *\) *)
(*           F.Hbox [F.String "Pi ", fmtPredicate' (I.Decl (G, D), P)]    *)

(*     fun fmtPredicate (G, P) = fmtPredicate' (Names.ctxName G, P)  *)

(*     fun fmtRGCtx' (G, nil) = "" *)
(*       | fmtRGCtx' (G, [P]) =  *)
(* 	F.makestring_fmt(fmtPredicate' (G, P) ) *)
(*       | fmtRGCtx' (G, (P :: Rl)) =  *)
(* 	F.makestring_fmt(fmtPredicate' (G, P)) ^ " ," ^ fmtRGCtx' (G, Rl) *)
	
(*     fun fmtRGCtx (G, Rl) = fmtRGCtx' (Names.ctxName G, Rl)  *)

	
(*     (\*--------------------------------------------------------------------*\) *)


    fun strSubord (a,b) = Subordinate.below(a,b) andalso (not (Subordinate.equiv(a,b)))


      
    fun dropTypes (Less (R.Arg (Us,Vs), R.Arg (Us', Vs'))) = Less (Us, Us')
      | dropTypes (Leq (R.Arg (Us,Vs), R.Arg (Us', Vs'))) = Leq (Us, Us')
      | dropTypes (Eq (R.Arg (Us,Vs), R.Arg (Us', Vs'))) = Eq (Us, Us')
      | dropTypes (Pi (D, P)) = Pi (D, dropTypes P)
      | dropTypes  _ = 
	raise Unimp "Lexicographic and simultaneous orders not supported by the LPO checker;\n hack them up with pairs instead"

    datatype headStatus = CONST of I.cid
			| AV of int
			| EV of int

    fun statToString (CONST n) = "CONST(" ^ (Int.toString n) ^ ")"
      | statToString (AV n) =  "AV(" ^ (Int.toString n) ^ ")"
      | statToString (EV n) =  "EV(" ^ (Int.toString n) ^ ")"

    fun decType (I.Dec (_, E)) = E
    
    fun hstatus(Q, I.BVar n, s) = 
	let
	  val n' = (case (I.bvarSub(n, s))
		     of (I.Idx n') => n'
		      | (I.Exp (I.Root (I.BVar n', I.Nil))) => n')
	in
	  (case (I.ctxLookup (Q, n'))
			       of All => AV n'
				| _ => EV n')
	end
      | hstatus (Q, I.Const cid, s) = CONST cid

    (* possible optimization: have hcompare return any 
       type info it calculates *)
    fun hcompare (G,Q) ((h, s), (h', s')) =
	let
	  val stath = hstatus (Q, h, s)
	  val stath' = hstatus (Q, h', s')
	  val _ = print ("hcompare: "^ (statToString stath) ^ ", " ^ (statToString stath') ^ "\n")
	  val cfam = I.constType
	  val vfam = decType o (fn n => I.ctxDec (G,n))
	  fun famComp (V, V') = 
	      let
		val a = I.targetFam V
		val a' = I.targetFam V'
	      in
		if strSubord(a,a') then L.LT(V,V') else L.NLE(V,V')
	      end
	  val order = 
	      (case (stath, stath')
		of (CONST cid, CONST cid')  => L.orderCompare (cid, cid')
		 | (CONST cid, AV n') => famComp (cfam cid, vfam n')
		 | (CONST cid, EV n') => L.NLE (cfam cid, vfam n')
		 | (AV n, CONST cid') => famComp (vfam n, cfam cid')
		 | (AV n, AV n') => 
		   let
		     val V = vfam n
		     val V' = vfam n'
		   in
		     if (Conv.conv ((V, I.id), (V', I.id))) then L.EQ(V,V')
		     else famComp(V, V')
		   end
		 | (AV n, EV n') => L.NLE (vfam n, vfam n')
		 | (EV n, CONST cid) => L.NLE (vfam n, cfam cid)
		 | (EV n, AV n') => L.NLE (vfam n, vfam n')
		 | (EV n, EV n') => L.NLE (vfam n, vfam n')
				    )
	in
	  (stath, order, stath')
	end



    fun proveAtomic _ = raise Unimp "proveAtomic"

    fun proveEq ((G,Q), D, (I.Lam(Dec, U), s), (U', s')) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec, s)))
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtx D shiftOnce
	  val Us1 = (U, I.dot1 s)
	  val Us1' = (U', shiftOnce s')
	in
	  proveEq ((G1, Q1), D1, Us1, Us1') 
	end

      | proveEq (GQ, D, Us as (I.Root (I.Def _, _), _), Us') =
	proveEq (GQ, D, (Whnf.expandDef Us), Us')

      | proveEq ((G,Q), D, (U as I.Root _, s), (I.Lam(Dec', U'), s')) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec', s')))
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtx D shiftOnce
	  val Us1 = (U, shiftOnce s)
	  val Us1' = (U', I.dot1 s')
	in
	  proveEq ((G1, Q1), D1, Us1, Us1') 
	end
      | proveEq (GQ, D, Us as (I.Root _, _), Us' as (I.Root (I.Def _, _), _)) =
	proveEq (GQ, D, Us, (Whnf.expandDef Us'))
	     
      | proveEq (GQ, D, (U as I.Root (h, S), s), Us' as (I.Root (h', S'), s')) =
	(case (hcompare GQ ((h,s), (h',s')))
	  of (_, L.EQ(V, _), _) => proveEqList (GQ, D, (S,s), (S',s'), V)
	   | (EV n, L.NLE(V, _), EV n') =>  
	     (n = n') andalso proveEqList (GQ, D, (S,s), (S',s'), V)
	   | _ => false
		  )

    and proveEqList (GQ, D, Ss, Ss', V) =
	let
	  val b = I.targetFam V
	  fun proveEqList' (I.Nil, _) (I.Nil, _) _ = true
	    | proveEqList' (I.App (U,S), s) (I.App (U',S'), s')
			   (I.Pi ((I.Dec (_, V), _), V'))
	      =
	      let
		val a = I.targetFam V
	      in
		if (L.isDropped(a,b)) then proveEqList' (S, s) (S',s') V'
		else proveEq (GQ, D, (U,s), (U', s')) 
		     andalso proveEqList' (S, s) (S',s') V'
	      end
	(* If SClo can happen then I need to add some cases *)
	in
	  proveEqList' Ss Ss' V
	end

    fun proveLt ((G,Q), D, (I.Lam(Dec, U), s), (U', s')) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec, s)))
	  (* val G1 = I.Decl (G, N.decLUName (G,Dec))*) 
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtx D shiftOnce
	  val Us1 = (U, I.dot1 s)
	  val Us1' = (U', shiftOnce s')
	in
	  proveLt ((G1, Q1), D1, Us1, Us1') 
	end
	  
      | proveLt (GQ, D, Us as (I.Root (I.Def _, _), _), Us') =
	proveLt (GQ, D, (Whnf.expandDef Us), Us')

      | proveLt ((G,Q), D, (U as I.Root _, s), (I.Lam(Dec', U'), s')) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec', s')))
	  (* val G1 = I.Decl (G, N.decLUName (G, Dec')) *)
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtx D shiftOnce
	  val Us1 = (U, shiftOnce s)
	  val Us1' = (U', I.dot1 s')
	in
	  proveLt ((G1, Q1), D1, Us1, Us1') 
	end

      | proveLt (GQ, D, Us as (I.Root _, _), Us' as (I.Root (I.Def _, _), _)) =
	proveLt (GQ, D, Us, (Whnf.expandDef Us'))

      | proveLt (GQ, D, Us as (I.Root (h, S), s), 
		 Us' as (I.Root (h', S'), s')) =
	(case (hcompare GQ ((h,s), (h',s')))
	  of (_, L.LT(V, V'), _) => proveLtA (GQ, D, (S,s), V, Us')
	   | (_, L.EQ(V, _), _) => proveLex (GQ, D, (S,s), (S',s'), V, Us')
	   | (_, L.NLE(_, V'), CONST cid) => proveLeS (GQ, D, Us, (S',s'), V')
	   | (_, L.NLE(_, V'), AV n) => proveLeS (GQ, D, Us, (S',s'), V')
	   | _ => proveAtomic ()
	   )

    and proveLtA (GQ, D, (S,s), VS, Us') =
	let
	  val b = I.targetFam VS

	  (* note: VS is only being used here as a simple type, so we don't
	   need to worry about applying substitutions to it *)
	  fun proveLtA' _ (I.Nil) _ = true
	    | proveLtA' s (I.App (U,S)) (I.Pi ((I.Dec (_, V), _), V')) =
	      let
		val a = I.targetFam V
	      in
		if (L.isDropped(a,b)) then proveLtA' s S V'
		else proveLt (GQ, D, (U,s), Us') andalso proveLtA' s S V'
	      end
	    | proveLtA' s' (I.SClo (S, s)) VS = 
	      let
		val _ = print ("LtA encountered an SClo; " ^
			"hopefully I composed the substitutions correctly\n")
	      in
		proveLtA' (I.comp (s',s)) S VS
	      end
	in
	  proveLtA' s S VS
	end

    and proveLex (GQ, D, Ss, Ss', VS, Us2) = 
	let
	  val b = I.targetFam VS
	  fun proveLex' (I.Nil, _) (I.Nil, _) _ = false
	    | proveLex' (I.App (U,S), s) (I.App (U',S'), s') 
			(I.Pi ((I.Dec (_, V), _), V')) =
	      let
		val a = I.targetFam V
	      in
		if (L.isDropped(a,b)) then proveLex' (S,s) (S',s') V'
		else (proveLt (GQ, D, (U,s), (U',s')) 
		      andalso proveLtA (GQ, D, (S,s), V', Us2))
		     orelse
		     (proveEq (GQ, D, (U,s), (U',s'))
		      andalso proveLex' (S,s) (S',s') V')
	      end
	in
	  proveLex' Ss Ss' VS
	end

		  

    and proveLeS (GQ, D, Us, Ss', VS') = 
	let
	  val b = I.targetFam VS'
	  fun proveLeS' (I.Nil, _) _ = false
	    | proveLeS' (I.App (U', S'), s') (I.Pi ((I.Dec (_, V), _), V')) =
	      let
		val a = I.targetFam V
	      in
		if (L.isDropped(a,b)) then proveLeS' (S', s') V'
		else proveLe(GQ, D, Us, (U',s')) orelse proveLeS' (S', s') V'
	      end
	in
	  proveLeS' Ss' VS'
	end

    and proveLe (GQ, D, O, O') =
	proveLt (GQ, D, O, O')  orelse proveEq(GQ, D, O, O')

    fun rightDecompose (GQ, D, Less (O,O')) = 
	proveLt (GQ, D, O, O')
      | rightDecompose (GQ, D, Leq(O,O')) =
	proveLe (GQ, D, O, O')
      | rightDecompose (GQ, D, Eq(O,O')) =
	proveEq (GQ, D, O, O') 

      | rightDecompose (GQ as (G,Q), D, Pi (Dec, P)) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, Dec)): IntSyn.dctx
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtx D shiftOnce
	  val P1 = shiftAP P I.dot1
	in
	  rightDecompose ((G1,Q1), D1, P1)
	end

    fun leftDecompose(GQ, nil, D', P) = rightDecompose (GQ, D', P)
      | leftDecompose _ = raise Unimp "leftDecompose"

    fun deduce (G:I.dctx, Q:qctx, D:rctx, P:order Predicate) = 
	leftDecompose ((G,Q), map dropTypes D, nil, dropTypes P) 
	handle (E as Unimp s) => (print (s ^ "\n"); raise E)
  in
    val deduce = deduce 
    val shiftRCtx = shiftRCtx
    val shiftPred = shiftP
  end (* local *)
end; (* functor checking  *)
