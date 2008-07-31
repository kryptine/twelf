(* about lexicographic path orders *)
(* Author: Jeffrey Sarnat *)
(* based on the code for the subterm ordering by Brigitte Pientka *)

 
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

datatype headStatus =        (* denotes the type of a head and some info *)
	 CONST of IntSyn.cid      (* constants *) 
       | AV of int                (* All quantified BVar *)
       | EV of int                (* Exist/And quantified BVar *)


(* possible optimization:
   take apart lambdas for Less, Leq and Eq all in one function then do 
   reasoning on atomic terms from there. This would cut down on backtracking.
 *)		

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
  structure W = Whnf
   (*--------------------------------------------------------------------*)
   (* Printing atomic orders *)

  fun predToString (G, Less (Us, Us')) =
      Print.expToString(G, I.EClo(Us)) ^ " < " ^ 
      Print.expToString(G, I.EClo(Us'))
    | predToString (G, Leq(Us,Us')) =
      Print.expToString(G, I.EClo(Us)) ^ " <= " ^ 
      Print.expToString(G, I.EClo(Us'))
    | predToString (G, Eq(Us,Us')) =
      Print.expToString(G, I.EClo(Us)) ^ " = " ^ 
      Print.expToString(G, I.EClo(Us'))
    | predToString (G, Pi (Dec, P)) = 
      "Pi " ^
      (Print.decToString (G, Dec)) ^ ". " ^
      (predToString (I.Decl (G, N.decLUName (G, Dec)), P))

  fun subToString (I.Shift n) = "^" ^ (Int.toString n)
    | subToString (I.Dot (I.Idx n, s)) = (Int.toString n) ^ "." ^ (subToString s)

  fun printSub s = print ((subToString s) ^ "\n")

fun statToString (CONST n) = "CONST(" ^ (Int.toString n) ^ ")"
  | statToString (AV n) =  "AV(" ^ (Int.toString n) ^ ")"
  | statToString (EV n) =  "EV(" ^ (Int.toString n) ^ ")"

      
   (*--------------------------------------------------------------------*)
   (* shifting substitutions *)

   (* shiftO O s = O'

      if O is an order 
         then we compose the substitutions in O with s
    *)

  (* substitution functions used by the interface *)
    fun shiftO (R.Arg ((U, us), (V, vs))) s =
	R.Arg ((U, (I.comp(us,s))), (V, (I.comp(vs,s))))
      | shiftO (R.Lex L) s = R.Lex (map (fn O => shiftO O s) L)
      | shiftO (R.Simul L) s = R.Simul (map (fn O => shiftO O s) L)


    fun shiftP (Less(O1, O2)) s = Less(shiftO O1 s, shiftO O2 s)
      | shiftP (Leq(O1, O2)) s = Leq(shiftO O1 s, shiftO O2 s)
      | shiftP (Eq(O1, O2)) s = Eq(shiftO O1 s, shiftO O2 s)
      | shiftP (Pi(D as I.Dec(X,V), P)) s = 
	Pi (I.decSub (D, s), 
	    shiftP P (I.dot1 s))


    fun shiftRCtx Rl s = map (fn p => shiftP p s) Rl







    (* my shifting *)

    fun shiftOnce s = I.comp(s, I.shift)
    fun subP s (Less((U, us), (U', us'))) =
	Less ((U, I.comp (us, s)), (U', I.comp (us',s)))
      | subP s (Leq((U, us), (U', us'))) = 
	Leq ((U, I.comp (us, s)), (U', I.comp (us',s)))
      | subP s (Eq((U, us), (U', us'))) = 
	Eq ((U, I.comp (us, s)), (U', I.comp (us',s)))
      | subP s (Pi(D, P)) =
	Pi (I.decSub (D, s), 
	    subP (I.dot1 s) P)

    fun subDCtx s D = map (subP s) D

    fun shiftPOnce D = subP I.shift D

    fun shiftDCtxOnce D = subDCtx I.shift D

    (*--------------------------------------------------------------------*)
(*    (\* Printing *\) *)

    fun ecloToString G Us = Print.expToString (G, (I.EClo Us))

    fun spineLength (I.Nil) = 0
      | spineLength (I.App (U,S)) = 1 + spineLength S
      | spineLength (I.SClo (S,s)) = (print "SClo detected!\n"; spineLength S)
	
     (*--------------------------------------------------------------------*)

    (* invariant: strsubord(a,b) =  B
		  B iff a is strictly is subordinate to b, 
                  but not equivalent to b
     *)
    fun strSubord (a,a') = Subordinate.below(a,a') 
			  andalso (not (Subordinate.equiv(a,a')))

    fun strSmallerType (V, V') = strSubord ((I.targetFam V), (I.targetFam V'))

    (* dropImplicit n (S, S', V))
       drops the first n Apps from S and S', and the first n Pis from V
       invariant: the lengths of S, S' and V are greater than n
     *)
    fun dropImplicit n (S, S', V) =
	let
	  fun dropImplicit' m (SSV as
				    (I.App(U,S), I.App(U', S'), I.Pi (_, V))) =
	      if (m = n) then SSV
	      else dropImplicit' (m+1) (S, S', V)
	in
	  dropImplicit' 0 (S, S', V)
	end
		 
	      


    (* 
     converts from an rctx to an I.eclo predicate list
     by throwing away types and disallowing lexicographic and 
     simultaneous orders
     *)
    fun dropTypes (Less (R.Arg (Us,Vs), R.Arg (Us', Vs'))) = Less (Us, Us')
      | dropTypes (Leq (R.Arg (Us,Vs), R.Arg (Us', Vs'))) = Leq (Us, Us')
      | dropTypes (Eq (R.Arg (Us,Vs), R.Arg (Us', Vs'))) = Eq (Us, Us')
      | dropTypes (Pi (D, P)) = Pi (D, dropTypes P)
      | dropTypes  _ = 
	raise Error "Lexicographic and simultaneous orders not supported by the LPO checker;\n hack them up with pairs instead"


    fun decType (I.Dec (_, E)) = W.normalize (E, I.id)

    fun varName G n =
	let 
	  val dec = I.ctxDec (G,n)
	in
	  (case (dec)
	    of (I.Dec(SOME(name), _)) => name
	     | (I.Dec(NONE, _)) => "(var #" ^ (Int.toString n) ^ ")")
	end

    (* returns the headStatus of a head, its type, and its drop list *)
    fun hstatus(G, Q, I.BVar n, s) = 
	let
	  val n' = (case (I.bvarSub(n, s))
		     of (I.Idx n') => n'
		      | (I.Exp (I.Root (I.BVar n', I.Nil))) => n')
	  val V = decType (I.ctxDec (G,n'))
	  val dl = L.typeToDropList V
	in
	  (case (I.ctxLookup (Q, n'))
			       of All => (AV n', V, dl)
				| _ => (EV n', V, dl)
				       )
	end
      | hstatus (G,Q, I.Const cid, s) = 
	let
	  val V = I.constType cid
	  val dl = L.cidDropList cid
	in
	  (CONST cid, V, dl)
	end

    (* given two heads, returns comparison information between them 
     *)
    fun hcompare (G,Q) ((h, s), (h', s')) =
	let
	  val (hinfo as (stath, V, dl)) = hstatus (G, Q, h, s)
	  val (hinfo' as (stath', V', dl')) = hstatus (G,Q, h', s')
	  val a = I.targetFam V
	  val a' = I.targetFam V'
	  fun famOrder (a,a') = if (strSubord (a,a')) then L.LT else L.NLE
	  val order =
	      (case (stath, stath')
		of (CONST cid, CONST cid') => L.orderCompare(cid,cid')
		 | (CONST cid, AV n') => famOrder(a,a')
		 | (AV n, CONST cid') => famOrder(a,a')
		 | (AV n, AV n') =>
		   (* Conv.conv too coarse valued here: 
		    could use simple type instead
		    *)
		   if (Conv.conv((V,I.id),(V',I.id))) 
		   then L.EQ else famOrder(a,a')
		 | _ => L.NLE
			)
	in
	  ((stath, a, dl), order, (stath', a', dl'))
	end
(*

	  val cdl = L.cidDropList
	  val vdl = L.typeToDropList o decType o (fn n => I.ctxDec (G,n))
	  fun famComp (V, V') = 
	      let
		val a = I.targetFam V
		val a' = I.targetFam V'
		val dl = L.getDropList V
		val dl' = L.getDropList V'
	      in
		if strSubord(a,a') then L.LT(dl,dl') else L.NLE(dl,dl')
	      end
	  val order = 
	      (case (stath, stath')
		of (CONST cid, CONST cid')  => L.orderCompare (cid, cid')
		 | (CONST cid, AV n') => famComp (cdl cid, vdl n')
		 | (CONST cid, EV n') => L.NLE (cdl cid, vdl n')
		 | (AV n, CONST cid') => famComp (vdl n, cdl cid')
		 | (AV n, AV n') => 
		   let
		     val V = vdl n
		     val V' = vdl n'
		   in
		     (* conv.conv too course valued here *)
		     if (Conv.conv ((V, I.id), (V', I.id))) then L.EQ(V,V')
		     else famComp(V, V')
		   end
		 | (AV n, EV n') => L.NLE (vdl n, vdl n')
		 | (EV n, CONST cid) => L.NLE (vdl n, cdl cid)
		 | (EV n, AV n') => L.NLE (vdl n, vdl n')
		 | (EV n, EV n') => L.NLE (vdl n, vdl n')
				    )
	in
	  (stath, order, stath')
	end
*)

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
    val debugString = ref "."

    fun lookupEq (GQ as (G,Q), D, Us0, Us1) = 
	let
(*
	  val prefix = !debugString
	  val _ = debugString := (!debugString) ^ "e"
	  val name0 = Print.expToString (G, W.normalize Us0)
	  val name1 = Print.expToString (G, W.normalize Us1)
	  val _ = print ("LookupEq: " ^ name0 ^ " =? " ^ name1 ^ "\n" ^ prefix ^ "\n")
	
*)
	  fun compare (Us, Us') = Conv.conv(Us,Us') orelse rightEq (GQ, nil, Us, Us')
	  fun lookupEq' nil = false
	    | lookupEq' (Less _ :: D') = lookupEq' D'
	    | lookupEq' (Eq (Us2, Us3) :: D') =
	      (* axiom rule *)
	      (compare (Us0, Us2) andalso compare(Us1, Us3))
	      orelse
	      (* axiom rule with refl *)
	      (compare (Us0, Us3) andalso compare(Us1, Us2)) 
	      (* transitivity rule with refl *)
	      orelse
	      (compare (Us0, Us2) andalso rightEq(GQ, D, Us1, Us3))
	      orelse
	      (compare (Us0, Us3) andalso rightEq(GQ, D, Us1, Us2))
	      orelse
	      (compare (Us1, Us2) andalso rightEq(GQ, D, Us0, Us3))
	      orelse
	      (compare (Us1, Us3) andalso rightEq(GQ, D, Us0, Us2))
	      orelse
	      lookupEq' D'
	  val b = lookupEq' D
(*	  val _ = print (prefix ^ " eq returned " ^ (Bool.toString b) ^ "\n")
	  val _ = debugString := prefix
*)

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
(*
	  val prefix = !debugString
	  val _ = debugString := (!debugString) ^ "l"
	  val name0 = ecloToString G Us0
	  val name1 = ecloToString G Us1
	  val _ = print ("LookupLt: " ^ name0 ^ " <? " ^ name1 ^ "\n" ^ prefix ^
 "\n")
*)

	  fun compare (Us,Us') =  rightEq (GQ, nil, Us, Us')
	  fun lookupLt' nil = false
	    | lookupLt' (Less (Us2, Us3) :: D') = 
	      (* axiom rule *)
	      (compare (Us0, Us2) andalso compare (Us1, Us3))
	      orelse (* missing rule *)
	      (compare (Us0, Us2) andalso rightLt(GQ, D, Us3, Us1))
	      orelse
	      (* lt-trans and lt-eq2 *)
	      ((compare (Us1, Us3))
	       andalso 
	       (rightLt(GQ, D, Us0, Us2) orelse rightEq(GQ, D, Us0, Us2)))
	      orelse
	      lookupLt' D'

	    | lookupLt'(Eq (Us2, Us3) :: D')  = 
	      (compare (Us1, Us2) andalso rightLt (GQ, D, Us0, Us1))
	      orelse
	      (compare (Us1, Us3) andalso rightLt (GQ, D, Us0, Us3))
	      orelse
	      lookupLt' D'
	  val b = lookupLt' D
(*
	  val _ = print (prefix ^ " lt returned " ^ (Bool.toString b) ^ "\n")
	  val _ = debugString := prefix
*)
	in
	  b
	end

(*
    and lookupLt (GQ as (G,Q), D, Us0, Us1) =
	let
	  val prefix = !debugString
	  val _ = debugString := (!debugString) ^ "l"
	  val name0 = ecloToString G Us0
	  val name1 = ecloToString G Us1
	  val _ = print ("LookupLt: " ^ name0 ^ " <? " ^ name1 ^ "\n" ^ prefix ^ "\n")
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
	  val _ = print (prefix ^ " " ^ (Bool.toString b) ^ "\n")
	  val _ = debugString := prefix
	in
	  b
	end
*)
    and rightEq ((G,Q), D, (I.Lam(Dec, U), s), (U', s')) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec, s)))
	  val Q1 = I.Decl (Q, All)
(*	  val D1 = shiftDCtx D shiftOnce *)
	  val D1 = shiftDCtxOnce D
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
(*	  val D1 = shiftDCtx D shiftOnce *)
	  val D1 = shiftDCtxOnce D
	  val Us1 = (U, shiftOnce s)
	  val Us1' = (U', I.dot1 s')
	in
	  rightEq ((G1, Q1), D1, Us1, Us1') 
	end
      | rightEq (GQ, D, Us as (I.Root _, _), Us' as (I.Root (I.Def _, _), _)) =
	rightEq (GQ, D, Us, (Whnf.expandDef Us'))
	     
      | rightEq (GQ as (G,Q), D, Us as (I.Root (h, S), s), 
		 Us' as (I.Root (h', S'), s')) =
	let
	  val ((stath, a, dl), order, (stath', a', dl')) = 
	      hcompare GQ ((h,s), (h',s'))
	in
	  (case (order)
	    of (L.EQ) => rightEqList (GQ, D, (S,s), (S',s'), dl)
	     | _ =>
	       (case (stath, stath')
		 of (EV n, EV n') =>
		    ((n = n') andalso rightEqList (GQ, D, (S,s), (S',s'), dl))
		    orelse lookupEq (GQ, D, Us, Us')
		  | (EV n, _) => lookupEq (GQ, D, Us,Us')
		  | (_, EV n') => lookupEq (GQ, D, Us,Us')
		  | _ => 
			 (* the only hope here is if D has contradictory
			 assumptions that can be deduced via transitivity.
			 For now, we won't implement this *) 
		    false
		)
	       )
	end


(*	  of (_, L.EQ(V, V'), _) => 
	     rightEqList (GQ, D, (S,s), (S',s'), V)
	   | (EV n, L.NLE(V, V'), EV n') => 
	     ((n = n') andalso rightEqList (GQ, D, (S,s), (S',s'), V))
	     orelse lookupEq (GQ, D, Us, Us')


	   | (_, _, EV _) => lookupEq (GQ, D, Us,Us')
	   | _ => false (/* the only hope here is if D has contradictory
			 assumptions that can be deduced via transitivity.
			 For now, we won't implement this */)
*)
		  

    and rightEqList (GQ as (G,Q), D, (S,s), (S',s'), dl) =
	let
	  fun rightEqList' (I.Nil) (I.Nil) nil = true
	    | rightEqList' (I.App (U,S)) (I.App (U',S')) (b::dl) =
		if b then rightEqList' S S' dl
		else rightEq (GQ, D, (U,s), (U', s')) 
		     andalso rightEqList' S S' dl
	in
	  rightEqList' S S' dl
	end

    and rightLt ((G,Q), D, (I.Lam(Dec, U), s), (U', s')) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec, s)))
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtxOnce D
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
	  val D1 = shiftDCtxOnce D
	  val Us1 = (U, shiftOnce s)
	  val Us1' = (U', I.dot1 s')
	in
	  rightLt ((G1, Q1), D1, Us1, Us1') 
	end

      | rightLt (GQ, D, Us as (I.Root _, _), Us' as (I.Root (I.Def _, _), _)) =
	rightLt (GQ, D, Us, (Whnf.expandDef Us'))

      | rightLt (GQ, D, Us as (I.Root (h, S), s), 
		 Us' as (I.Root (h', S'), s')) =
	let 
	  val ((stath, a, dl), order, (stath', a', dl')) =
	      hcompare GQ ((h,s), (h',s'))
	in
	(case (order)
	  of (L.LT) => rightLtA (GQ, D, (S,s), dl, Us')
	   | (L.EQ) => 	     
	     rightLex (GQ, D, (S,s), (S',s'), dl, Us')
	     orelse
	     rightLeS (GQ, D, Us, (S',s'), dl)
	   | (L.NLE) => 
	     (case (stath, stath')
	       of (_, EV _) => strSubord(a,a') orelse lookupLt (GQ, D, Us, Us')
		| (EV _, _) => 
		  rightLeS (GQ, D, Us, (S',s'), dl') orelse
		  lookupLt (GQ, D, Us, Us')
		| _ => rightLeS (GQ, D, Us, (S',s'), dl')
		       )
	     )
	end
(*
	  of (_, L.LT(V, V'), _) => rightLtA (GQ, D, (S,s), V, Us')
	   | (AV _, L.EQ(V, _), _) => 
	     rightLex (GQ, D, (S,s), (S',s'), V, Us')
	     orelse
	     rightLeS (GQ, D, Us, (S',s'), V)
	   | (CONST cid, L.EQ(V,_), _) => 
	     let
	       val (S, S', V) = dropImplicit (I.constImp cid) (S, S', V)
	     in
	       rightLex (GQ, D, (S,s), (S',s'), V, Us')
	       orelse
	       rightLeS (GQ, D, Us, (S',s'), V)
	     end
	   | (_, L.NLE(V,V'), EV _) =>
	     strSmallerType(V,V') orelse
	     lookupLt (GQ, D, Us, Us')
	   | (EV _, L.NLE(V,V'), _) => 
	     rightLeS (GQ, D, Us, (S',s'), V') orelse
	     lookupLt (GQ, D, Us, Us')
	   | (_, L.NLE(V,V'), _) => 
	     rightLeS (GQ, D, Us, (S',s'), V')
*)


    and rightLtA (GQ, D, (S,s), dl, Us') =
	let
	  fun rightLtA' (I.Nil) (nil) = true
	    | rightLtA' (I.App (U,S)) (b :: dl) =
	      if b then rightLtA' S dl
	      else rightLt (GQ, D, (U,s), Us') andalso rightLtA' S dl
	in
	  rightLtA' S dl
	end

    and rightLex (GQ as (G,Q), D, (S, s), (S',s'), dl, Us2) = 
	let
	  fun rightLex' (I.Nil) (I.Nil) nil = false
	    | rightLex' (I.App (U,S)) (I.App (U',S')) 
			(b :: dl) =
			if b then 
			  rightLex' S S' dl
		else
		  (rightLt (GQ, D, (U,s), (U',s')) 
		   andalso rightLtA (GQ, D, (S,s), dl, Us2))
		     orelse
		     (rightEq (GQ, D, (U,s), (U',s'))
		      andalso rightLex' S S' dl)
	in
	  rightLex' S S' dl
	end

		  

    and rightLeS (GQ, D, Us, (S', s'), dl) = 
	let
	  fun rightLeS' (I.Nil) (nil) = false
	    | rightLeS' (I.App (U', S')) (b::dl) =
	      if b then rightLeS' S' dl
	      else rightLe(GQ, D, Us, (U',s')) orelse rightLeS' S' dl
	in
	  rightLeS' S' dl
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
	  val D1 = shiftDCtxOnce D
	  val P1 = P
	in
	  rightDecompose ((G1,Q1), D1, P1)
	end

    fun leftEq ((I.Lam(Dec, U), s),  (U',s')) ((G,Q), D, D', P) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec, s)))
	  val Q1 = I.Decl (Q, All)
(*	  val D1 = shiftDCtx D shiftOnce
	  val D1' = shiftDCtx D' shiftOnce
*)
	  val D1 = shiftDCtxOnce D
	  val D1' = shiftDCtxOnce D'
	  val Us1 = (U, I.dot1 s)
	  val Us1' = (U', shiftOnce s')
	  val P1 = shiftPOnce P
	in
	  leftEq (Us1, Us1') ((G1,Q1), D1, D1', P1)
	end

      | leftEq ((Us as (I.Root (I.Def _, _), _)), Us') GQDP =
	leftEq (W.expandDef Us, Us') GQDP

      | leftEq ((U as I.Root _, s), (I.Lam(Dec', U'), s'))
	       ((G,Q), D, D', P) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec', s')))
	  val Q1 = I.Decl (Q, All)
(*	  val D1 = shiftDCtx D shiftOnce
	  val D1' = shiftDCtx D' shiftOnce
*)
	  val D1 = shiftDCtxOnce D
	  val D1' = shiftDCtxOnce D'
	  val Us1 = (U, shiftOnce s)
	  val Us1' = (U', I.dot1 s')
(*	  val P1 = shiftAP P shiftOnce *)
	  val P1 = shiftPOnce P
	in
	  leftEq (Us1, Us1') ((G1, Q1), D1, D1', P1)
	end
	  

      | leftEq (Us as (I.Root _, s), Us' as (I.Root (I.Def _, _), _)) GQDP =
	leftEq (Us, W.expandDef Us') GQDP
 
      | leftEq (Us as (U as I.Root (h, S), s), 
		Us' as (U' as I.Root (h', S'), s')) 
	       (GQDP as (GQ as (G,Q), D, D', P)) =
	       let
		 val ((stath, a, dl), order, (stath', a', dl')) =
		     hcompare GQ ((h,s), (h',s'))
	       in
	       (case (order)
		 of (L.EQ) => leftEqList GQDP ((S,s), (S',s'), dl)
		  | _ => 
		    (case (stath, stath')
		      of (CONST _, CONST _) => true
		       | (CONST _, AV _) => true
		       | (AV _, CONST _) => true
		       | (AV _, AV _) => true
		       | _ => leftDecompose (GQ, D, Less(Us,Us')::D', P)
			      )
		    )
	       end
(*
	  of (_, L.EQ(V, _), _) => leftEqList GQDP ((S,s), (S',s'), V)
	   | (CONST _, _, CONST _) => true
	   | (CONST _, _, AV _) => true
	   | (AV _, _, CONST _) => true
	   | (AV _, _, AV _) => true
	   | _ => leftDecompose (GQ, D, Less(Us,Us')::D', P)
*)


    and leftEqList (GQ, D, D', P) ((S,s), (S',s'), dl) =
	let
	  fun leftEqList' (I.Nil) (I.Nil) nil D =
	      leftDecompose (GQ, D, D', P)
	    | leftEqList' (I.App (U, S)) (I.App (U', S'))
			  (b::dl) D =
	      if b then leftEqList' S S' dl D
	      else leftEqList' S S' dl (Eq ((U,s), (U',s'))::D)
	in
	  leftEqList' S S' dl D
	end



    and leftLt ((I.Lam(Dec, U), s),  (U',s')) ((G,Q), D, D', P) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec, s)))
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtxOnce D
	  val D1' = shiftDCtxOnce D'
	  val Us1 = (U, I.dot1 s)
	  val Us1' = (U', shiftOnce s')
	  val P1 = shiftPOnce P
	in
	  leftLt (Us1, Us1') ((G1,Q1), D1, D1', P1)
	end

      | leftLt ((Us as (I.Root (I.Def _, _), _)), Us') GQDP =
	leftLt (W.expandDef Us, Us') GQDP

      | leftLt ((U as I.Root _, s), (I.Lam(Dec', U'), s'))
	       ((G,Q), D, D', P) =
	let
	  val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec', s')))
	  val Q1 = I.Decl (Q, All)
	  val D1 = shiftDCtxOnce D
	  val D1' = shiftDCtxOnce D'
	  val Us1 = (U, shiftOnce s)
	  val Us1' = (U', I.dot1 s')
	  val P1 = shiftPOnce P
	in
	  leftLt (Us1, Us1') ((G1, Q1), D1, D1', P1)
	end
	  
      | leftLt (Us as (I.Root _, s), Us' as (I.Root (I.Def _, _), _)) GQDP =
	leftLt (Us, W.expandDef Us') GQDP
 


      | leftLt (Us as (U as I.Root (h, S), s), 
		Us' as (U' as I.Root (h', S'), s')) 
	       (GQDP as (GQ as (G,Q), D, D', P)) =
	       let
		 val ((stath, a, dl), order, (stath', a', dl')) =
		     hcompare GQ ((h,s), (h',s'))
	       in
		 (case (order)
		   of (L.LT) => leftLtA GQDP ((S,s), dl, Us')
		    | (L.EQ) => leftLex GQDP ((S,s), (S',s'), dl, Us')
				   andalso
				   leftLeS GQDP (Us, (S',s'), dl)
		    | (L.NLE) => 
		      (case (stath, stath')
			of (EV _, _) =>
			   leftDecompose (GQ, D, Less(Us, Us')::D', P)
			 | (_, EV _) => 
			   leftDecompose (GQ, D, Less(Us, Us')::D', P)
			 | _ => leftLeS GQDP (Us, (S',s'), dl')
			 )
		      )
	       end
(*
	  of (_, L.LT(V, V'), _) => leftLtA GQDP ((S,s), V, Us')
	   | (_, L.EQ(V, _), _) => leftLex GQDP ((S,s), (S',s'), V, Us')
				   andalso
				   leftLeS GQDP (Us, (S',s'), V)
	   | (EV _, _, _) => 
	     leftDecompose (GQ, D, Less(Us, Us')::D', P)
	     
	   | (_, _, EV _) => leftDecompose (GQ, D, Less(Us, Us')::D', P)
	   | (_, L.NLE(_,V'), _) => leftLeS GQDP (Us, (S',s'), V')
*)



    and leftLtA (GQ as (G,Q), D, D', P) ((S,s), dl, Us') =
	let
	  (* val _ = print ("leftLta: Us' = " ^ (ecloToString G Us') ^ "\n")*)
	  fun leftLtA' (I.Nil) (nil) D =
	      leftDecompose (GQ, D, D', P)
	    | leftLtA' (I.App (U, S)) (b::dl) D = 
	      let
(*		val uname = ecloToString G (U,s)
		val _ = print ((if b then "     dropping " else "     not dropping ") ^ uname ^ "\n")
*)
	      in
		if b then leftLtA' S dl D
		else leftLtA' S dl (Less ((U,s), Us') ::D)
	      end
	in
	  leftLtA' S dl D
	end


    and leftLex (GQ, D, D', P) ((S,s), (S',s'), dl, Us2) =
	let
	  fun leftLex' (I.Nil) (I.Nil) (nil) D =
	      leftDecompose (GQ, D, D', P)
	    | leftLex' (I.App (U,S)) (I.App (U',S')) 
		       (b::dl) D =
		if b then leftLex' S S' dl D
		else (leftLtA (GQ, Less((U,s), (U',s'))::D, D', P) 
			      ((S,s), dl, Us2))
		     andalso
		     (leftLex' S S' dl (Eq((U,s),(U',s'))::D))
	in
	  leftLex' S S' dl D
	end



    and leftLeS (GQ, D, D', P) (Us, (S', s'), dl) = 
	let
	  fun leftLeS' (I.Nil) (nil) D = true
	    | leftLeS' (I.App(U', S')) (b::dl) D = 
		if b then leftLeS' S' dl D
		else leftDecompose (GQ, Leq (Us, (U',s'))::D, D', P)
		     andalso
		     leftLeS' S' dl D
	in
	  leftLeS' S' dl D
	end

    and leftLe (O,O') GQDP =
	(leftEq (O,O') GQDP) andalso (leftLt (O,O') GQDP)

(*    and leftAtomize L (Us as (U,s)) (Us' as (U',s')) (GQDP as (G,Q, D, D', P))
      =
      (case U
	of (I.Lam(Dec, U)) =>
	   let
	     val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec, s)))
	     val Q1 = I.Decl (Q, All)
	     val D1 = shiftDCtxOnce D
	     val D1' = shiftDCtxOnce D'
	     val Us1 = (U, I.dot1 s)
	     val Us1' = (U', shiftOnce s')
	     val P1 = shiftPOnce P
	   in
	     leftAtomize L Us1 Us1' (G1, Q1, D1, D1', P1)
	   end
	 | (I.Root (I.Def _, _)) => 
	   leftAtomize L (W.expandDef Us) Us' GQDP 
	 | (I.Root (h, S)) =>
	   (case (U') of
	      (I.Lam(Dec', U')) =>
	      let
		val G1 = I.Decl (G, N.decLUName (G, I.decSub(Dec', s')))
		val Q1 = I.Decl (Q, All)
		val D1 = shiftDCtxOnce D
		val D1' = shiftDCtxOnce D'
		val Us1 = (U, shiftOnce s)
		val Us1' = (U', I.dot1 s')
		val P1 = shiftPOnce P
	      in
		leftAtomize L Us1 Us1' (G1, Q1, D1, D1', P1)
	      end
	    | (I.Root (I.Def _, _)) => 
	      leftAtomize L Us (W.expandDef Us') GQDP
	    | (I.Root (h', S')) => raise Unimp "leftAtomize"
				  )
	   )
*)

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
	  val D1 = shiftDCtxOnce D
	  val D1' = shiftDCtxOnce D'
	  val P1' = P' (* shiftAP P' I.dot1 *) 
	  val P1 = shiftPOnce P
(*
	  val _ = print ("P' = " ^ predToString(G, (Pi (Dec,P'))) ^ "\n")
	  val _ = print ("P1' = " ^ predToString(G1, P1') ^ "\n")
*)
	in
	  leftDecompose ((G1, Q1), P1'::D1, D1', P1)
	end



    fun deduce (G:I.dctx, Q:qctx, D:rctx, P:order Predicate) = 
	leftDecompose ((G,Q), map dropTypes D, nil, dropTypes P) 
	handle (E as Unimp s) => (print (s ^ "\n"); 
				  raise E ;
				  false
				  )
  in
    val deduce = deduce (* fn x => let val b = deduce x val _ =  (print "deduced: "; print (Bool.toString b); print "\n-----------------------------------\n\n") in b end *)
    val shiftRCtx = shiftRCtx
    val shiftPred = shiftP
  end (* local *)
end; (* functor checking  *)
