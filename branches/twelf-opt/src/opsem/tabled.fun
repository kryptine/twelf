(* Abstract Machine for tabling*)
(* Author: Brigitte Pientka *)
(* Based on abstract machine in absmachine.fun *)

functor Tabled (structure IntSyn' : INTSYN
		structure CompSyn' : COMPSYN
		  sharing CompSyn'.IntSyn = IntSyn'
		structure Unify : UNIFY
		  sharing Unify.IntSyn = IntSyn'
		structure TabledSyn : TABLEDSYN
		  sharing TabledSyn.IntSyn = IntSyn'		  
		structure Assign : ASSIGN
		  sharing Assign.IntSyn = IntSyn'
		structure Index : INDEX
		  sharing Index.IntSyn = IntSyn'
		structure Queue : QUEUE
		structure TableParam : TABLEPARAM
		  sharing TableParam.IntSyn = IntSyn'
		  sharing TableParam.CompSyn = CompSyn'

		structure AbstractTabled : ABSTRACTTABLED
		  sharing AbstractTabled.IntSyn = IntSyn'
		  sharing AbstractTabled.TableParam = TableParam
		structure MemoTable : MEMOTABLE
		  sharing MemoTable.IntSyn = IntSyn' 
		  sharing MemoTable.CompSyn = CompSyn' 
		  sharing MemoTable.TableParam = TableParam 
		(* CPrint currently unused *)
		structure CPrint : CPRINT 
		  sharing CPrint.IntSyn = IntSyn'
		  sharing CPrint.CompSyn = CompSyn'
		(* CPrint currently unused *)
		structure Print : PRINT 
		  sharing Print.IntSyn = IntSyn'
		  
		structure Names : NAMES 
		  sharing Names.IntSyn = IntSyn'
		structure CSManager : CS_MANAGER
		  sharing CSManager.IntSyn = IntSyn')
  : TABLED =
struct

  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'
  structure Unify = Unify
  structure TabledSyn = TabledSyn

  local
    structure I = IntSyn
    structure C = CompSyn
    structure A = AbstractTabled
    structure T = TableParam
    structure MT = MemoTable      
  in
    
    (* ---------------------------------------------------------------------- *)
    (* Suspended goal: (p,s), G, sc, ftrail, answerRef, i

       current program state          : G |- p[s]
       forward trail                  : ftrail
       pointer to potential answers 
       in the memo-table              : answerRef
       Number of answer which already
       have been consumed  by this 
       current program state          : i

    *)
    datatype SuspType = Loop | Divergence
    (* note: that dctx and exp and DProg are not really needed *)     
    val SuspGoals : (((SuspType * (IntSyn.dctx * IntSyn.Exp * IntSyn.Sub) * CompSyn.DProg * 
		       (CompSyn.pskeleton -> unit)) * 
		      Unify.unifTrail * (IntSyn.Sub * T.answer) * int ref)  list) ref  = ref []

    exception Error of string

    (* ---------------------------------------------------------------------- *)
      
   fun cidFromHead (I.Const a) = a
     | cidFromHead (I.Def a) = a
     
   fun eqHead (I.Const a, I.Const a') = a = a'
     | eqHead (I.Def a, I.Def a') = a = a'
     | eqHead _ = false

    fun concat (I.Null, G') = G'
      | concat (I.Decl(G, D), G') = I.Decl(concat(G,G'), D)

    fun reverse (I.Null, G') = G'
      | reverse (I.Decl(G, D), G') = 
          reverse (G, I.Decl(G', D))

    fun compose'(IntSyn.Null, G) = G
      | compose'(IntSyn.Decl(G', D), G) = IntSyn.Decl(compose'(G', G), D)


    fun append(IntSyn.Null, G) = G
      | append(IntSyn.Decl(G', D), G) = IntSyn.Decl(append(G', G), D)


    fun shift (IntSyn.Null, s) = s
      | shift (IntSyn.Decl(G, D), s) = I.dot1 (shift(G, s))


    (* ---------------------------------------------------------------------- *)
    (* We write
       G |- M : g
     if M is a canonical proof term for goal g which could be found
     following the operational semantics.  In general, the
     success continuation sc may be applied to such M's in the order
     they are found.  Backtracking is modeled by the return of
     the success continuation.

     Similarly, we write
       G |- S : r
     if S is a canonical proof spine for residual goal r which could
     be found following the operational semantics.  A success continuation
     sc may be applies to such S's in the order they are found and
     return to indicate backtracking.
  *)

    (* ---------------------------------------------------------------------- *)

    (* ctxToEVarSub D = s*)

    fun ctxToEVarSub (I.Null, s) = s
      | ctxToEVarSub (I.Decl(G,I.Dec(_,A)), s) = 
      let
(*	val X = I.newEVar (I.Null, I.EClo (A,s))   (* ???? *) 
        bp Wed Feb 20 11:06:51 2002 *)
	val X = I.newEVar (I.Null, A)
      in
	I.Dot(I.Exp(X), ctxToEVarSub (G, s))
      end 

    fun ctxToAVarSub (I.Null, s) = s
      | ctxToAVarSub (I.Decl(G,I.Dec(_,A)), s) = 
      let
(*	val X = I.newEVar (I.Null, I.EClo (A,s))   (* ???? *) 
        bp Wed Feb 20 11:06:51 2002 *)
	val X = I.newEVar (I.Null, A)
      in
	I.Dot(I.Exp(X), ctxToAVarSub (G, s))
      end 

      | ctxToAVarSub (I.Decl(G,I.ADec(_,d)), s) = 
      let
	val X = I.newAVar ()
      in
	I.Dot(I.Exp(I.EClo(X, I.Shift(~d))), ctxToAVarSub (G, s))
      end 


    (* ---------------------------------------------------------------------- *)
    fun printSub (I.Shift n) = print ("I.Shift " ^ Int.toString n ^ "\n")
    | printSub (I.Dot(I.Idx n, s)) = (print ("Idx " ^ Int.toString n ^ " . "); printSub s)
    | printSub (I.Dot (I.Exp(I.EVar (_, _, _, _)), s)) = (print ("Exp (EVar _ ). "); printSub s)
    | printSub (I.Dot (I.Exp(I.AVar (_)), s)) = (print ("Exp (AVar _ ). "); printSub s)
    | printSub (I.Dot (I.Exp(I.EClo (I.AVar (_), _)), s)) = (print ("Exp (EClo(AVar _, _ )). "); printSub s)
    | printSub (I.Dot (I.Exp(I.EClo (_, _)), s)) = (print ("Exp (EClo _ ). "); printSub s)
    | printSub (I.Dot (I.Exp(_), s)) = (print ("Exp (_ ). "); printSub s)
    | printSub (I.Dot (I.Undef, s)) = (print ("Undef . "); printSub s)

    fun printResEqn (G, T.Trivial) = print "Trivial\n"
      | printResEqn (G, T.Unify(G', U, N, eqn)) = 
        let
	  val (G'') = compose'(G', G)
	  val s1 = shift (G', I.id) 
	  val _ = case s1 of I.Shift 0 => () | _ => print "s1 =/= id\n"
	in 
	  (print "Unify "; print (Print.expToString (I.Null, A.raiseType(G'', I.EClo(U, s1)))); print " = ";
	   print (Print.expToString (G'', I.EClo(N, s1)) ^ "\n");
	   printResEqn (G, eqn))
	  end 


    fun printResEqnSub (D, G, T.Trivial, s) = print "Trivial\n"
      | printResEqnSub (D, G, T.Unify(G', U, N, eqn), s) = 
        let
	  val (G'') = compose'(G', G)
	  val s1 = shift (G', s) 
          val d = I.ctxLength (G'')
	  val _ = print ("d = " ^ Int.toString d ^ "\n")
	in 
	  (print "Unify "; print (Print.expToString (I.Null, A.raiseType(compose'(G'', D), I.EClo(U, I.comp(s1, I.Shift d))))); print " = ";
	   print (Print.expToString (compose'(G'', D), I.EClo(N, I.comp(s1, I.Shift d))) ^ "\n");
	   printResEqnSub (D, G, eqn, s))
	  end 

   (* ---------------------------------------------------------------------- *)

   (* retrieve' (n, G, ((M, V), s), answ_i, sc) = ()
    
     G |- s : G'
     G' |- M : V atomic goal 

     and answ_i = s_1 .... s_n
   
     for all k from 1 to n:

     if G |- M [s_k] : V[s_k]
     then sc M[s_k] is evaluated 
          where any bound var in Gas, is replaced by
            an existential variable

     Effects: instantiation of EVars in V, s, and dp
              any effect  sc M  might have

    n is just a counter which answer substitution
    we are currently considering -- only for debugging 
     
   *)

  fun solveEqn ((T.Trivial, s), G) = true
    | solveEqn ((T.Unify(G',e1, N, eqns), s), G) =
      let
	val G'' = compose' (G', G)
	val s' = shift (G'', s)
      in
	Assign.unifiable (G'', (N, s'), (e1, s'))
	andalso solveEqn ((eqns, s), G)
     end

  (* instantiateSub (s, s') = r
     
      . |- s : D  and X_m, ...X_1, A_n, ...A_1
      . |- s': D  and X'_m, ...X'_1, A'_n, ..., A'_1
     

  *)
  fun lengthSub (I.Shift n) = 0
    | lengthSub (I.Dot(U, s)) = 1 + lengthSub (s)


  (* in general it should be possible to s1 o s and s2 o s'
     note: there is a problem that the final shift is not |D_i|
     apparently... even if we change it in abstract.fun it doesn't quite work right 
     
     *)

    (* unifySub (G, s1, s2) = ()
     
       Invariant:
       If   G |- s1 : G'
       and  G |- s2 : G'
       then unifySub (G, s1, s2) terminates with () 
	    iff there exists an instantiation I, such that
	    s1 [I] = s2 [I]

       Remark:  unifySub is used only to unify the instantiation of SOME variables
    *)
    (* conjecture: G == Null at all times *)
    (* Thu Dec  6 21:01:09 2001 -fp *)
    and unifySub (G, I.Shift (n1), I.Shift (n2)) = ()
         (* by invariant *)
      | unifySub (G, I.Shift(n), s2 as I.Dot _) = 
          unifySub (G, I.Dot(I.Idx(n+1), I.Shift(n+1)), s2)
      | unifySub (G, s1 as I.Dot _, I.Shift(m)) = 
	  unifySub (G, s1, I.Dot(I.Idx(m+1), I.Shift(m+1)))
      | unifySub (G, I.Dot(Ft1,s1), I.Dot(Ft2,s2)) =
	  ((case (Ft1, Ft2) of
	     (I.Idx (n1), I.Idx (n2)) => 
	       if n1 <> n2 then raise Error "SOME variables mismatch"
	       else ()                      
           | (I.Exp (U1), I.Exp (U2)) => Unify.unify (G, (U1, I.id), (U2, I.id))
	   | (I.Exp (U1), I.Idx (n2)) => Unify.unify (G, (U1, I.id), (I.Root (I.BVar (n2), I.Nil), I.id))
           | (I.Idx (n1), I.Exp (U2)) => Unify.unify (G, (I.Root (I.BVar (n1), I.Nil), I.id), (U2, I.id)));
(*	   | (Undef, Undef) => 
	   | _ => false *)   (* not possible because of invariant? -cs *)
	  unifySub (G, s1, s2))

  fun unifySub' (G, s1, s2) = (unifySub (G, s1, s2); true) handle Unify.Unify _ => false

    (* see retrieve *)      
   fun retrieve' (n, goal, G, Vs, (G', U'), asub, [], sc)  = ()
     | retrieve' (n, goal, G, Vs as (V,s), (G', U'), asub, (((DEVars, s1), O1)::A), sc) =  
     let 
       val Vpi = A.raiseType(G, V)
       val Upi = A.raiseType(G', U')

       val s1' = ctxToEVarSub (DEVars, I.id) (* from DEVars |- s1 : D  and D' |- asub : D
					        create: DEVars' |-  r1 : D' 
						s.t. s1 = asub o r1 *) 
     in
         CSManager.trail (fn () => if unifySub' (I.Null, I.comp(asub, s), I.comp(s1, s1'))  
				   then ((sc O1)) else ());
       retrieve' (n+1, goal, G, Vs, (G', U'), asub, A, sc)
     end 
   

   (* retrieve (G, (V, s), ((G', D', U'), A), sc) = ()
      Invariants:
     . |-   s : D    (s contains free vars)
     D |-  Pi G. V
       |- (Pi G. V)[s]
     D'|-  Pi G'. U'    
     for each i where i in [0...k] and  ((Di, si), Oi) in A 

    if . |- si' : Di
      (Pi G. V)[s] ==  (Pi G'.U')[si][si'] 
    then evaluate (sc Oi)

     !!! important part: . |- s : D
     !!! U = V, and G = G' 
     !!! goal, U, V, G, G' are really not important
     !!! what should happen: s is matched against s_i (where s_i is an answer)
     Effects: instantiation of EVars in s, and G
              any effects the success continuation might have   
   *)
    and retrieve (k, goal, G, Vs as (V, s), (H as ((G', U), (asub, answRef))), sc) =
        let
	  val lkp  = T.lookup(answRef) 
	  val asw' = List.take(rev(T.solutions(answRef)), 
			       T.lookup(answRef))
	  val answ' = List.drop(asw', !k) 
	in 
	k := lkp;
        retrieve' (0,goal, G, Vs, (G', U), asub, answ', sc)
	end

  (* ---------------------------------------------------------------------- *)
     
   (* solve ((g, s), dp, sc) => ()
     Invariants:
     dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
     G |- s : G'
     G' |- g  goal
     if  G |- M : g[s]
       then  sc M  is evaluated
     Effects: instantiation of EVars in g, s, and dp
     any effect  sc M  might have
     *)
   fun solve ((C.Atom(p), s), dp as C.DProg (G, dPool), sc) =     
     (if TabledSyn.tabledLookup (I.targetFam p) 
	then 
	  let 
	    val (G', DAVars, DEVars, U', eqn', s') = A.abstractEVarCtx (G, p, s)
	    val _ = if solveEqn ((eqn', s'), G')
		      then () 
		    else print "\nresidual equation not solvable!\n" 
	  in
	    case MT.callCheck (DAVars, DEVars, G', U', eqn') 
	      (* Side effect: D', G' |- U' added to table *)	    
	      of T.NewEntry (answRef) => 		
		matchAtom ((p,s), dp, 
			   (fn pskeleton =>			    
			    (case MT.answerCheck (G', U', s', answRef, pskeleton)
			       of T.repeated => ()
			     | T.new      => sc pskeleton)))
		
	       | T.RepeatedEntry(asub, answRef) => 
	       if T.noAnswers answRef then 	    
		 (* loop detected  
		  * NOTE: we might suspend goals more than once.
		  *     case: answer list for goal (p,s) is saturated
		  *           but not the whole table is saturated.
		  *)
		 (SuspGoals :=  ((Loop, (G', U',s'), dp, sc), Unify.suspend() , (asub, answRef), ref 0)::(!SuspGoals);  
		  ()) 
	       else  
		 (* loop detected
		  * new answers available from previous stages
		  * resolve current goal with all possible answers
		  *)	
		 let  
		   val le = T.lookup(answRef) 
		 in 
		   (* add to suspended goals the abstracted forms? *)
		  SuspGoals := ((Loop, (G', U',s'), dp, sc), Unify.suspend(), (asub, answRef), ref le)::(!SuspGoals);
		  retrieve (ref 0, A.raiseType(G, I.EClo(p,s)), G', (U' , s'), ((G', U'), (asub, answRef)), sc)
		end

	       | T.DivergingEntry(answRef) => 
		 (* loop detected  
		  * NOTE: we might suspend goals more than once.
		  *     case: answer list for goal (p,s) is saturated
		  *           but not the whole table is saturated.
		  *)
		 (print "Divergence - suspended\n";
		  SuspGoals :=  ((Divergence, (G', U', s'), dp, sc), Unify.suspend() , 
				 (I.id, answRef), ref 0)::(!SuspGoals); 
		  ())
	      end 
	else 
	  matchAtom ((p, s), dp, sc))
    
     | solve ((C.Impl(r, A, Ha, g), s), C.DProg (G, dPool), sc) =
       let
	 val D' = I.Dec(NONE, I.EClo(A,s))
       in
	 solve ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, SOME(r, s, Ha))),
		(fn O => sc O)) 
       end
     | solve ((C.All(D, g), s), C.DProg (G, dPool), sc) =
       let
	 val D' = I.decSub (D, s)
       in
	 solve ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl(dPool, NONE)),
		(fn O => sc O))
       end

   (* rsolve ((p,s'), (r,s), dp, sc) = ()
    Invariants:
    dp = (G, dPool) where G ~ dPool
    G |- s : G'
    G' |- r  resgoal
    G |- s' : G''
    G'' |- p : H @ S' (mod whnf)
    if G |- S : r[s]
       then sc S is evaluated
     Effects: instantiation of EVars in p[s'], r[s], and dp
     any effect  sc S  might have
     *)
   and rSolve (ps', (C.Eq(Q), s), C.DProg (G, dPool), sc) =    
       (if Unify.unifiable (G, ps', (Q, s)) (* effect: instantiate EVars *)
	    then 
	      sc [] 		          (* call success continuation *) 
	  else  ())		          (* fail *)
	  
	| rSolve (ps', (C.Assign(Q, eqns), s), dp as C.DProg(G, dPool), sc) = 
       (case Assign.assignable (G, ps', (Q, s)) of
	  SOME(cnstr) => 	    
	    aSolve((eqns, s), dp, cnstr, (fn S => sc S))
	| NONE => ())
	   
     | rSolve (ps', (C.And(r, A, g), s), dp as C.DProg (G, dPool), sc) =
       let
	(* is this EVar redundant? -fp *)
	val X = I.newEVar(G, I.EClo(A, s)) 
      in
        rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp,
		(fn S1 => solve ((g, s), dp, (fn S2 => sc (S1@S2)))))
      end
     | rSolve (ps', (C.Exists(I.Dec(_,A), r), s), dp as C.DProg (G, dPool), sc) =
       let
	 val X = I.newEVar(G, I.EClo(A, s)) 
       in
	 rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp, (fn S => sc S))
       end
    
     | rSolve (ps', (C.Axists(I.ADec(SOME(X), d), r), s), dp as C.DProg (G, dPool), sc) =
       let
	 val X' = I.newAVar ()
       in
	 rSolve (ps', (r, I.Dot(I.Exp(I.EClo(X', I.Shift(~d))), s)), dp, sc)
         (* we don't increase the proof term here! *)
       end


  (* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else res = Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)

  and aSolve ((C.Trivial, s), dp, cnstr, sc) = 
        (if Assign.solveCnstr cnstr then
	  (sc [])
	else 
	   ())
    | aSolve ((C.UnifyEq(G',e1, N, eqns), s), dp as C.DProg(G, dPool), cnstr, sc) =
      let
	val (G'') = compose'(G', G)
	val s' = shift (G', s)
      in 
	if Assign.unifiable (G'', (N, s'), (e1, s')) then  	  
	      aSolve ((eqns, s), dp, cnstr, sc)
	else ()
     end

  (* matchatom ((p, s), dp, sc) => ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *)
  and matchAtom (ps' as (I.Root(Ha,S),s), dp as C.DProg (G,dPool), sc) =
      let
        (* matchSig [c1,...,cn] = ()
	   try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
	fun matchSig nil = ()	(* return indicates failure *)
	  | matchSig ((Hc as I.Const c)::sgn') =
	    let
	      val C.SClause(r) = C.sProgLookup (cidFromHead Hc)
	    in
	      (* trail to undo EVar instantiations *)
	      CSManager.trail (fn () =>
			       (rSolve (ps', (r, I.id), dp,
					(fn S =>  sc ((C.Pc c)::S)))));
	      matchSig sgn'
	    end

        (* matchDProg (dPool, k) = ()
	   where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
	fun matchDProg (I.Null, _) =
	    (* dynamic program exhausted, try signature *)
	    ((* print "Dynamic clause pool exhausted\n";*)
	    matchSig (Index.lookup (cidFromHead Ha)))
	  | matchDProg (I.Decl (dPool', SOME(r, s, Ha')), k) =
	    if eqHead (Ha, Ha')	      
	      then 
		(* trail to undo EVar instantiations *)
		(CSManager.trail (fn () =>
				  rSolve (ps', (r, I.comp(s, I.Shift(k))), dp,
					  (fn S => sc ((C.Dc k)::S)))); 
		 matchDProg (dPool', k+1))
	    else matchDProg (dPool', k+1)
	  | matchDProg (I.Decl (dPool', NONE), k) =
	      matchDProg (dPool', k+1)


          fun matchConstraint (solve, try) =
              let
                val succeeded =
                  CSManager.trail
                    (fn () =>
                       case (solve (G, I.SClo (S, s), try))
                         of SOME(U) => (sc [C.Csolver]; true)
                          | NONE => false)
              in
                if succeeded
                then matchConstraint (solve, try+1)
                else ()
              end      

      in
        case I.constStatus(cidFromHead Ha)
          of (I.Constraint (cs, solve)) => matchConstraint (solve, 0)
           | _ => matchDProg (dPool, 1)
      end

  (* retrieval ((p, s), dp, sc, answRef, n) => ()
     Invariants:
     dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
     G |- s : G'
     G' |- p  goal
     answRef : pointer to corresponding answer list
     n       : #number of answers which were already consumed 
               by the current goal

     if answers are available 
      then retrieve all new answers
     else fail
     *)
  fun retrieval (Loop, (G', U', s'), dp, sc, (asub, answRef), n) =    
    if T.noAnswers answRef then 	    
      (* still  no answers available from previous stages *)
      (* NOTE: do not add the susp goal to suspGoal list
	        because it is already in the suspGoal list *)
      ()
      else 
	(*  new answers available from previous stages
	 * resolve current goal with all "new" possible answers
	 *)
	retrieve (n, I.EClo(A.raiseType(G', U'), s'), G', (U', s'),((G', U'), (asub, answRef)), sc)

(*    | retrieval (Divergence, (G', U',s'), dp as C.DProg(G, dPool), sc, (asub, answRef), n) =    
	matchAtom ((p,s), dp, 
		   (fn pskeleton =>
		    case MT.answerCheck (G', U', s', answRef, pskeleton)
		      of T.repeated => ()
		    | T.new      => sc pskeleton
			))
*)

  
    fun updateAbsParam () = ()
(*      (case (!T.termDepth) of
 	   NONE => ()
	 | SOME(n) => T.termDepth := SOME(n+1);
       case (!T.ctxDepth) of
 	   NONE => ()
	 | SOME(n) => T.ctxDepth := SOME(n+1);

       case (!T.ctxLength) of
 	   NONE => ()
	 | SOME(n) => T.ctxLength := SOME(n+1)
	     )
*)
    fun tableSize () =  MT.tableSize ()
    fun suspGoalNo () =  List.length(!SuspGoals)

  (*  nextStage () = bool       
     Side effect: advances lookup pointers
   *)

 fun nextStage () = 
   let   
     fun resume ([],n) = ()
       | resume ((((Susp, (G, U,s), dp, sc), trail, (asub, answRef), k)::Goals),n) =
       (CSManager.trail	(fn () => (Unify.resume trail; 	 				   
				   retrieval (Susp, (G, U,s), dp, sc, (asub, answRef), k)));
	resume (Goals, n-1))  
      val SG = rev(!SuspGoals) 
      val l = length(SG)
   in    
     if MT.updateTable () then 
       (* table changed during previous stage *)
	(updateAbsParam (); 
	 TableParam.stageCtr := (!TableParam.stageCtr) + 1;
	 resume (SG, l);
	true)
     else 
       (* table did not change during previous stage *)
       false
   end 

(*
 fun solExists (p,s) = 
   let
     val (G', D', U', eqn', s') = A.abstractEVarCtx (I.Null, p, s)       
   in 
     case MT.callCheck (G', D', U', eqn') of
       MT.NewEntry (_) => false
     | MT.RepeatedEntry(L) => true
   end 
*)

 fun reset () = (SuspGoals := []; MT.reset(); TableParam.stageCtr := 0)

  fun solveQuery ((g, s), dp as C.DProg (G, dPool), sc) =
    (* only work when query is atomic -- might extend subordination relation
       and then strengthening may not be sound *)
     case (!TableParam.strategy) of
       TableParam.Variant =>  solve((g, s), dp, sc)
     |  TableParam.Subsumption => solve((g, s), dp, sc) (* raise T.Error "subsumption part deleted"*)

  end (* local ... *)

 val solve = solveQuery


end; (* functor Tabled *)



