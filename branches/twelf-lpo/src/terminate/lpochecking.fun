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
	(* the previous definition for Pi was wrong -js *)
      | shiftP (Pi(D as I.Dec(X,V), P)) f = Pi (I.decSub(D, f I.id),
						shiftP P (f o I.dot1))



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

    fun ecloToString G Us = Print.expToString (G, (I.EClo Us));
	
(*     (\*--------------------------------------------------------------------*\) *)


    fun strSubord (a,b) = Subordinate.below(a,b) 
			  andalso (not (Subordinate.equiv(a,b)))


      
    fun dropTypes (Less (R.Arg (Us,Vs), R.Arg (Us', Vs'))) = Less (Us, Us')
      | dropTypes (Leq (R.Arg (Us,Vs), R.Arg (Us', Vs'))) = Leq (Us, Us')
      | dropTypes (Eq (R.Arg (Us,Vs), R.Arg (Us', Vs'))) = Eq (Us, Us')
      | dropTypes (Pi (D, P)) = Pi (D, dropTypes P)
      | dropTypes  _ = 
	raise Error "Lexicographic and simultaneous orders not supported by the LPO checker;\n hack them up with pairs instead"

    datatype headStatus = CONST of I.cid
			| AV of int
			| EV of int

    fun statToString (CONST n) = "CONST(" ^ (Int.toString n) ^ ")"
      | statToString (AV n) =  "AV(" ^ (Int.toString n) ^ ")"
      | statToString (EV n) =  "EV(" ^ (Int.toString n) ^ ")"

    fun decType (I.Dec (_, E)) = W.normalize (E, I.id)
    
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


    fun findContradiction _ = false (* I'm not sure if I need to impliment this*)

    (* 
     atomic left predicates:
     h R = h' R' where h or h' is an existentially quantified bvar
	      and h != h'
     h R < h R'  where h or h' is an existentially quantified bvar

     atomic right predicates:
     h R = h' R' where h or h' is an existentially quantified bvar
	      and h != h'
     h R < x R'  where x is a existentially quantified bvar

     *)

    (* invariant lookupEq (GQ, D, Us, Us')
     D contains only atomic predicates
     Us = Us' is an atomic predicate
     *)
    fun lookupEq (GQ as (G,Q), D, Us0, Us1) = 
	let
	  val name0 = Print.expToString (G, W.normalize Us0)
	  val name1 = Print.expToString (G, W.normalize Us1)
	  val _ = print ("LookupEq: " ^ name0 ^ " = " ^ name1 ^ "? ")
	  fun lookupEq' nil = false
	    | lookupEq' (Less _ :: D) = lookupEq' D
	    | lookupEq' (Eq (Us2, Us3) :: D) =
	      (* axiom rule *)
	      (Conv.conv (Us0, Us2) andalso Conv.conv(Us1, Us3))
	      orelse
	      (* axiom rule with refl *)
	      (Conv.conv (Us0, Us3) andalso Conv.conv(Us1, Us2))
	      (* transitivity rule with refl *)
	      orelse
	      (Conv.conv (Us0, Us2) andalso rightEq(GQ, D, Us1, Us3))
	      orelse
	      (Conv.conv (Us0, Us3) andalso rightEq(GQ, D, Us1, Us2))
	      orelse
	      (Conv.conv (Us1, Us2) andalso rightEq(GQ, D, Us0, Us3))
	      orelse
	      (Conv.conv (Us1, Us3) andalso rightEq(GQ, D, Us0, Us2))
	      orelse
	      lookupEq' D
	  val b = lookupEq' D
	  val _ = print ((Bool.toString b) ^ "\n")
	in
	  b
	end

	  

	  
    (* invariant lookupLt (GQ, D, Us, Us')
     D contains only atomic predicates
     Us < Us' is an atomic predicate
     think about nontermination!

     *)
    and lookupLt (GQ as (G,Q), D, Us0, Us1) =
	let
	  val name0 = ecloToString G Us0
	  val name1 = ecloToString G Us1
	  val _ = print ("LookupLt: " ^ name0 ^ " <? " ^ name1 ^ "\n")
	  fun lookupLt' nil = false
	    | lookupLt' (Less (Us2, Us3) :: D) = 
	      let
		val name2 = ecloToString G Us2
		val name3 = ecloToString G Us3
		val _ = print ("  the context has: " ^ name2 ^ " < " ^ name3 ^ "\n")
	      in
		(* axiom rule *)
		(* (Conv.conv (W.whnf Us0, W.whnf Us2) andalso Conv.conv (W.whnf Us1, W.whnf Us3)) *)
		(rightEq (GQ, D, Us0, Us2) andalso rightEq (GQ, D, Us1, Us3))
		orelse
		(* lt-trans and lt-eq2 *)
		((Conv.conv (Us1, Us3))
		 andalso 
		 (rightLt(GQ, D, Us0, Us2) orelse rightEq(GQ, D, Us0, Us2)))
		orelse
		lookupLt' D
	      end
	    | lookupLt'(Eq (Us2, Us3) :: D)  = 
	      (Conv.conv (Us1, Us2) andalso rightLt (GQ, D, Us0, Us1))
	      orelse
	      (Conv.conv (Us1, Us3) andalso rightLt (GQ, D, Us0, Us3))
	      orelse
	      lookupLt' D
	  val b = lookupLt' D
	  val _ = print ((Bool.toString b) ^ "\n")
	in
	  b
	end

    and rightEq ((G,Q), D, (I.Lam(Dec, U), s), (U', s')) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec, s)))
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtx D shiftOnce
	  val Us1 = (U, I.dot1 s)
	  val Us1' = (U', shiftOnce s')
	in
	  rightEq ((G1, Q1), D1, Us1, Us1') 
	end

      | rightEq (GQ, D, Us as (I.Root (I.Def _, _), _), Us') =
	rightEq (GQ, D, (Whnf.expandDef Us), Us')

      | rightEq ((G,Q), D, (U as I.Root _, s), (I.Lam(Dec', U'), s')) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec', s')))
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtx D shiftOnce
	  val Us1 = (U, shiftOnce s)
	  val Us1' = (U', I.dot1 s')
	in
	  rightEq ((G1, Q1), D1, Us1, Us1') 
	end
      | rightEq (GQ, D, Us as (I.Root _, _), Us' as (I.Root (I.Def _, _), _)) =
	rightEq (GQ, D, Us, (Whnf.expandDef Us'))
	     
      | rightEq (GQ, D, Us as (I.Root (h, S), s), 
		 Us' as (I.Root (h', S'), s')) =
	(case (hcompare GQ ((h,s), (h',s')))
	  of (_, L.EQ(V, _), _) => rightEqList (GQ, D, (S,s), (S',s'), V)
	   | (EV n, L.NLE(V, _), EV n') => 
	     (print ("comparing evars for equality: " ^ Int.toString n ^ " and " ^ Int.toString n' ^ "\n");
	      ((n = n') andalso rightEqList (GQ, D, (S,s), (S',s'), V))
	      orelse lookupEq (GQ, D, Us, Us')
			      )
	   | (_, _, EV _) => lookupEq (GQ, D, Us,Us')
	   | _ => findContradiction (GQ,D, Eq(Us,Us'))

		  )

    and rightEqList (GQ as (G,Q), D, Ss, Ss', VS) =
	let
	  val b = I.targetFam VS
	  fun rightEqList' (I.Nil, _) (I.Nil, _) _ = true
	    | rightEqList' (I.App (U,S), s) (I.App (U',S'), s')
			   (I.Pi ((I.Dec (_, V), _), V'))
	      =
	      let
		val a = I.targetFam V
	      in
		if (L.isDropped(a,b)) then rightEqList' (S, s) (S',s') V'
		else rightEq (GQ, D, (U,s), (U', s')) 
		     andalso rightEqList' (S, s) (S',s') V'
	      end
	    | rightEqList' (I.SClo _, _) _ _ = (print "SCLO!!!\n"; raise Unimp "")
	    | rightEqList' (U,_) (U',_) V = 
	      let
		val Uname = foldr (fn (f,s) => (Formatter.makestring_fmt f)^ " | " ^ s) "." (Print.formatSpine (G,U))
		val Uname' = foldr (fn (f,s) => (Formatter.makestring_fmt f)^ " | " ^ s) "." (Print.formatSpine (G,U'))

		val Vname = Print.expToString (G, V)
		val _ = (case V 
			  of (I.Pi ((Dec, _), V')) => 
			     print ("Dec is: " ^ (Print.decToString (G,Dec)) ^ "\n")
			   | (I.Root (I.Def n, _)) => print "aah... defined constants\n"
			   | (I.Redex _) => print "redex?\n"
			   | (I.EClo _) =>  print "eclos?n"
			   | _ =>  print "not a pi or a def or a redex or an eclo?\n")

	      in
		raise Unimp ("something is wrong : [" ^ Uname ^ " ; " ^ Uname' ^ "]: "^ Vname)
	      end
	in
	  rightEqList' Ss Ss' VS
	end

    and rightLt ((G,Q), D, (I.Lam(Dec, U), s), (U', s')) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec, s)))
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtx D shiftOnce
	  val Us1 = (U, I.dot1 s)
	  val Us1' = (U', shiftOnce s')
	in
	  rightLt ((G1, Q1), D1, Us1, Us1') 
	end
	  
      | rightLt (GQ, D, Us as (I.Root (I.Def _, _), _), Us') =
	rightLt (GQ, D, (Whnf.expandDef Us), Us')

      | rightLt ((G,Q), D, (U as I.Root _, s), (I.Lam(Dec', U'), s')) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec', s')))
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtx D shiftOnce
	  val Us1 = (U, shiftOnce s)
	  val Us1' = (U', I.dot1 s')
	in
	  rightLt ((G1, Q1), D1, Us1, Us1') 
	end

      | rightLt (GQ, D, Us as (I.Root _, _), Us' as (I.Root (I.Def _, _), _)) =
	rightLt (GQ, D, Us, (Whnf.expandDef Us'))

      | rightLt (GQ, D, Us as (I.Root (h, S), s), 
		 Us' as (I.Root (h', S'), s')) =
	(case (hcompare GQ ((h,s), (h',s')))
	  of (_, L.LT(V, V'), _) => rightLtA (GQ, D, (S,s), V, Us')
	   | (_, L.EQ(V, _), _) => rightLex (GQ, D, (S,s), (S',s'), V, Us')
				   orelse
				   rightLeS (GQ, D, Us, (S',s'), V)
	   | (EV _, L.NLE(_,V'), CONST _) => 
	     rightLeS (GQ, D, Us, (S',s'), V') orelse
	     lookupLt (GQ, D, Us, Us')
	   | (EV _, L.NLE(_,V'), AV _) => 
	     rightLeS (GQ, D, Us, (S',s'), V') orelse
	     lookupLt (GQ, D, Us, Us')
	   | (EV _, _, EV _) => lookupLt (GQ, D, Us, Us')
	   | (_, L.NLE(_, V'), _) => rightLeS (GQ, D, Us, (S',s'), V')
				     )

    and rightLtA (GQ, D, (S,s), VS, Us') =
	let
	  val b = I.targetFam VS

	  (* note: VS is only being used here as a simple type, so we don't
	   need to worry about applying substitutions to it *)
	  fun rightLtA' _ (I.Nil) _ = true
	    | rightLtA' s (I.App (U,S)) (I.Pi ((I.Dec (_, V), _), V')) =
	      let
		val a = I.targetFam V
	      in
		if (L.isDropped(a,b)) then rightLtA' s S V'
		else rightLt (GQ, D, (U,s), Us') andalso rightLtA' s S V'
	      end
	    | rightLtA' s' (I.SClo (S, s)) VS = 
	      let
		val _ = print ("LtA encountered an SClo; " ^
			"hopefully I composed the substitutions correctly\n")
	      in
		rightLtA' (I.comp (s',s)) S VS
	      end
	in
	  rightLtA' s S VS
	end

    and rightLex (GQ, D, Ss, Ss', VS, Us2) = 
	let
	  val b = I.targetFam VS
	  fun rightLex' (I.Nil, _) (I.Nil, _) _ = false
	    | rightLex' (I.App (U,S), s) (I.App (U',S'), s') 
			(I.Pi ((I.Dec (_, V), _), V')) =
	      let
		val a = I.targetFam V
	      in
		if (L.isDropped(a,b)) then rightLex' (S,s) (S',s') V'
		else (rightLt (GQ, D, (U,s), (U',s')) 
		      andalso rightLtA (GQ, D, (S,s), V', Us2))
		     orelse
		     (rightEq (GQ, D, (U,s), (U',s'))
		      andalso rightLex' (S,s) (S',s') V')
	      end
	in
	  rightLex' Ss Ss' VS
	end

		  

    and rightLeS (GQ, D, Us, Ss', VS') = 
	let
	  val b = I.targetFam VS'
	  fun rightLeS' (I.Nil, _) _ = false
	    | rightLeS' (I.App (U', S'), s') (I.Pi ((I.Dec (_, V), _), V')) =
	      let
		val a = I.targetFam V
	      in
		if (L.isDropped(a,b)) then rightLeS' (S', s') V'
		else rightLe(GQ, D, Us, (U',s')) orelse rightLeS' (S', s') V'
	      end
	in
	  rightLeS' Ss' VS'
	end

    and rightLe (GQ, D, O, O') =
	rightEq(GQ, D, O, O') orelse rightLt (GQ, D, O, O')  

    fun rightDecompose (GQ, D, Less (O,O')) = 
	rightLt (GQ, D, O, O')
      | rightDecompose (GQ, D, Leq(O,O')) =
	rightLe (GQ, D, O, O')
      | rightDecompose (GQ, D, Eq(O,O')) =
	rightEq (GQ, D, O, O') 

      | rightDecompose (GQ as (G,Q), D, Pi (Dec, P)) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, Dec)): IntSyn.dctx
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtx D shiftOnce
	  val P1 = shiftAP P I.dot1
	in
	  rightDecompose ((G1,Q1), D1, P1)
	end

    fun leftEq ((I.Lam(Dec, U), s),  (U',s')) ((G,Q), D, D', P) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec, s)))
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtx D shiftOnce
	  val D1' = shiftDCtx D' shiftOnce
	  val Us1 = (U, I.dot1 s)
	  val Us1' = (U', shiftOnce s')
	  val P' = shiftAP P shiftOnce
	in
	  leftEq (Us1, Us1') ((G1,Q1), D1, D1', P)
	end

      | leftEq ((Us as (I.Root (I.Def _, _), _)), Us') GQDP =
	leftEq (W.expandDef Us, Us') GQDP

      | leftEq ((U as I.Root _, s), (I.Lam(Dec', U'), s'))
	       ((G,Q), D, D', P) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec', s')))
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtx D shiftOnce
	  val D1' = shiftDCtx D' shiftOnce
	  val Us1 = (U, shiftOnce s)
	  val Us1' = (U', I.dot1 s')
	  val P' = shiftAP P shiftOnce
	in
	  leftEq (Us1, Us1') ((G1, Q1), D1, D1', P')
	end
	  

      | leftEq (Us as (I.Root _, s), Us' as (I.Root (I.Def _, _), _)) GQDP =
	leftEq (Us, W.expandDef Us') GQDP
 
      | leftEq (Us as (U as I.Root (h, S), s), 
		Us' as (U' as I.Root (h', S'), s')) 
	       (GQDP as (GQ as (G,Q), D, D', P)) =
	(case (hcompare GQ ((h,s), (h',s')))
	  of (_, L.EQ(V, _), _) => leftEqList GQDP ((S,s), (S',s'), V)
	   | (CONST _, _, CONST _) => true
	   | (CONST _, _, AV _) => true
	   | (AV _, _, CONST _) => true
	   | (AV _, _, AV _) => true
	   | _ => leftDecompose (GQ, D, Less(Us,Us')::D', P)
		  )

    and leftEqList (GQ, D, D', P) (Ss, Ss', VS) =
	let
	  val b = I.targetFam VS
	  fun leftEqList' (I.Nil, _) (I.Nil, _) (_) D =
	      leftDecompose (GQ, D, D', P)
	    | leftEqList' (I.App (U, S), s) (I.App (U', S'), s')
			  (I.Pi ((I.Dec (_, V), _), V')) D =
	      let
		val a = I.targetFam V
	      in
		if (L.isDropped(a,b)) then leftEqList' (S, s) (S', s') V' D
		else leftEqList' (S,s) (S',s') V' (Eq ((U,s), (U',s'))::D)
	      end
	in
	  leftEqList' Ss Ss' VS D
	end



    and leftLt ((I.Lam(Dec, U), s),  (U',s')) ((G,Q), D, D', P) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec, s)))
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtx D shiftOnce
	  val D1' = shiftDCtx D' shiftOnce
	  val Us1 = (U, I.dot1 s)
	  val Us1' = (U', shiftOnce s')
	  val P' = shiftAP P shiftOnce
	in
	  leftLt (Us1, Us1') ((G1,Q1), D1, D1', P)
	end

      | leftLt ((Us as (I.Root (I.Def _, _), _)), Us') GQDP =
	leftLt (W.expandDef Us, Us') GQDP

      | leftLt ((U as I.Root _, s), (I.Lam(Dec', U'), s'))
	       ((G,Q), D, D', P) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec', s')))
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtx D shiftOnce
	  val D1' = shiftDCtx D' shiftOnce
	  val Us1 = (U, shiftOnce s)
	  val Us1' = (U', I.dot1 s')
	  val P' = shiftAP P shiftOnce
	in
	  leftLt (Us1, Us1') ((G1, Q1), D1, D1', P')
	end
	  
      | leftLt (Us as (I.Root _, s), Us' as (I.Root (I.Def _, _), _)) GQDP =
	leftLt (Us, W.expandDef Us') GQDP
 


      | leftLt (Us as (U as I.Root (h, S), s), 
		Us' as (U' as I.Root (h', S'), s')) 
	       (GQDP as (GQ as (G,Q), D, D', P)) =
	(case (hcompare GQ ((h,s), (h',s')))
	  of (_, L.LT(V, V'), _) => leftLtA GQDP ((S,s), V, Us')
	   | (_, L.EQ(V, _), _) => leftLex GQDP ((S,s), (S',s'), V, Us')
				   andalso
				   leftLeS GQDP (Us, (S',s'), V)
	   | (EV _, _, _) => 
	     let 
	       val name1 = ecloToString G (U,s)
	       val name2 = ecloToString G (U',s')
	       val _ = print ("putting " ^ name1 ^ " < " ^ name2 ^ " into the context\n")
	     in 
	       leftDecompose (GQ, D, Less(Us, Us')::D', P)
	     end
	   | (_, _, EV _) => (print "into the context it goes2\n"; leftDecompose (GQ, D, Less(Us, Us')::D', P))
	   | (_, L.NLE(_,V'), _) => leftLeS GQDP (Us, (S',s'), V')

(*

	   | (stat1, L.NLE(_,V), stat2) =>
	     (case (stat1) 
	       of (EV _) => leftDecompose (GQ, D, Less((U,s), (U',s'))::D', P)
		| _ =>
	   | (CONST _, L.NLE(_, V'), CONST _) => 
	     leftLeS GQDP (Us, (S',s'), V')
	   | (CONST _, L.NLE(_, V'), AV _) => 
	     leftLeS GQDP (Us, (S',s'), V')
	   | (AV _, L.NLE(_, V'), AV _) => 
	     leftLeS GQDP (Us, (S',s'), V')
	   | _ => leftDecompose (GQ, D, Less((U,s), (U',s'))::D', P)
*)
		  )


    and leftLtA (GQ, D, D', P) (Ss, VS, Us') =
	let
	  val b = I.targetFam VS
	  fun leftLtA' (I.Nil, _) _ D =
	      leftDecompose (GQ, D, D', P)
	    | leftLtA' (I.App (U, S), s) (I.Pi ((I.Dec (_, V), _), V')) D = 
	      let
		val a = I.targetFam V
	      in
		if (L.isDropped(a,b)) then leftLtA' (S,s) V' D
		else leftLtA' (S,s) V' (Less ((U,s), Us') ::D)
	      end
	in
	  leftLtA' Ss VS D
	end


    and leftLex (GQ, D, D', P) (Ss, Ss', VS, Us2) =
	let
	  val b = I.targetFam VS
	  fun leftLex' (I.Nil, _) (I.Nil, _) _ D =
	      leftDecompose (GQ, D, D', P)
	    | leftLex' (I.App (U,S), s) (I.App (U',S'), s') 
		       (I.Pi ((I.Dec (_, V), _), V')) D =
	      let
		val a = I.targetFam V
	      in
		if (L.isDropped(a,b)) then leftLex' (S,s) (S',s') V' D
		else (leftLtA (GQ, Less((U,s), (U',s'))::D, D', P) 
			      ((S,s), V', Us2))
		     andalso
		     (leftLex' (S,s) (S',s') V' (Eq((U,s),(U',s'))::D))
	      end
	in
	  leftLex' Ss Ss' VS D
	end



    and leftLeS (GQ, D, D', P) (Us, Ss', VS') = 
	let
	  val b = I.targetFam VS'
	  fun leftLeS' (I.Nil, _) _ D = true
	    | leftLeS' (I.App(U', S'), s') (I.Pi ((I.Dec (_, V), _), V')) D = 
	      let
		val a = I.targetFam V
	      in
		if (L.isDropped(a,b)) then leftLeS' (S',s') V' D
		else leftDecompose (GQ, Leq (Us, (U',s'))::D, D', P)
		     andalso
		     leftLeS' (S',s') V' D
	      end
		  
	in
	  leftLeS' Ss' VS' D
	end

    and leftLe (O,O') GQDP =
	(leftEq (O,O') GQDP) andalso (leftLt (O,O') GQDP)


    and leftDecompose(GQ, nil, D', P) = rightDecompose (GQ, D', P)
      | leftDecompose (GQ as (G,Q), Less(O,O')::D, D', P) = 
	leftLt (O,O') (GQ, D, D', P)
      | leftDecompose (GQ as (G,Q), Leq(O,O')::D, D', P) = 
	leftLe (O,O') (GQ, D, D', P)
      | leftDecompose (GQ as (G,Q), Eq(O,O')::D, D', P) = 
	leftEq (O,O') (GQ, D, D', P)
      | leftDecompose (GQ as (G,Q), Pi(Dec, P') :: D, D', P) = 
	let
	  val G1 = I.Decl (G, N.decLUName (G, Dec))
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtx D shiftOnce
	  val D1' = shiftDCtx D' shiftOnce
	  val P1' = shiftAP P I.dot1
	  val P1 = shiftAP P shiftOnce
	in
	  leftDecompose ((G1, Q1), P1'::D1, D1', P1)
	end



    fun deduce (G:I.dctx, Q:qctx, D:rctx, P:order Predicate) = 
	leftDecompose ((G,Q), map dropTypes D, nil, dropTypes P) 
	handle (E as Unimp s) => (print (s ^ "\n"); raise E)
  in
    val deduce = fn x => let val b = deduce x val _ =  (print "deduced: "; print (Bool.toString b); print "\n-----------------------------------\n\n") in b end
    val shiftRCtx = shiftRCtx
    val shiftPred = shiftP
  end (* local *)
end; (* functor checking  *)
