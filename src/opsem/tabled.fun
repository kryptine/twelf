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

    val SuspGoals : (((SuspType * (IntSyn.Exp * IntSyn.Sub) * CompSyn.DProg * (CompSyn.pskeleton -> unit)) * 
		      Unify.unifTrail * T.answer * int ref)  list) ref  = ref []

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
    | printSub (I.Dot (I.Exp(I.EClo (I.AVar (_), _)), s)) = (print ("Exp (AVar _ ). "); printSub s)
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


   (* see retrieve *)      
   fun retrieve' (n, goal, G, Vs, (G', U'), [], sc)  = ()
     | retrieve' (n, goal, G, Vs as (V,s), (G', U'), (((DEVars, s1), O1)::A),  sc) =  
     let 
       val Vpi = A.raiseType(G, V)
       val Upi = A.raiseType(G', U')
       val s1' = ctxToEVarSub (DEVars, I.id)
     in
       (* could be done more efficient by assigning the substitutions only ? *)
       (* s = s1 o s1' Wed Sep 18 17:29:06 2002 -bp 
          this would also make abstraction during retrieval superflous *)
       CSManager.trail (fn () => if Unify.unifiable(I.Null, (Vpi, s), (I.EClo(Upi, s1), s1')) 
	 then (sc O1) else ());
       retrieve' (n+1, goal, G, Vs, (G', U'), A, sc)
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

     Effects: instantiation of EVars in s, and G
              any effects the success continuation might have   
   *)
    and retrieve (k, goal, G, Vs as (V, s), (H as ((G', DAVars, DEVars, U, eqn), answ)), sc) =
        let
	  val lkp  = T.lookup(answ) 
	  val asw' = List.take(rev(T.solutions(answ)), 
			       T.lookup(answ))
	  val answ' = List.drop(asw', !k) 
	in 
	k := lkp;
        retrieve' (0,goal, G, Vs, (G', U), answ', sc)
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

(*	    val _ = (print "SOLVE : goal "; print (Print.expToString (I.Null, A.raiseType (G, I.EClo(p,s))) ^ "\n"))*)
	    val (G', DAVars, DEVars, U', eqn', s') = A.abstractEVarCtx (G, p, s)
(*	    val _ = (print "SOLVE : abstraction "; print (Print.expToString (I.Null, A.raiseType(DAVars, A.raiseType(DEVars, A.raiseType (G', U')))) ^ "\n"))*)
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
		
	       | T.RepeatedEntry(answRef) => 
	       if T.noAnswers answRef then 	    
		 (* loop detected  
		  * NOTE: we might suspend goals more than once.
		  *     case: answer list for goal (p,s) is saturated
		  *           but not the whole table is saturated.
		  *)
		 (SuspGoals :=  ((Loop, (p,s), dp, sc), Unify.suspend() , answRef, ref 0)::(!SuspGoals); 
		  ())
	       else 
		 (* loop detected
		  * new answers available from previous stages
		  * resolve current goal with all possible answers
		  *)	
		 let 
		   val le = T.lookup(answRef)
		 in 
		  SuspGoals := ((Loop, (p,s), dp, sc), Unify.suspend(), answRef, ref le)::(!SuspGoals);
		  retrieve (ref 0, A.raiseType(G, I.EClo(p,s)), G', (U' , s'), ((G', DAVars, DEVars, U', eqn'), answRef), sc)
		end

	       | T.DivergingEntry(answRef) => 
		 (* loop detected  
		  * NOTE: we might suspend goals more than once.
		  *     case: answer list for goal (p,s) is saturated
		  *           but not the whole table is saturated.
		  *)
		 (print "Divergence - suspended\n";
		  SuspGoals :=  ((Divergence, (p,s), dp, sc), Unify.suspend() , answRef, ref 0)::(!SuspGoals); 
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
					(fn S => sc ((C.Pc c)::S)))));
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
		let
(*		  val _ = print ("Pick dynamic assumption " ^ Int.toString k ^ "\n") *)
		in 
		  (* trail to undo EVar instantiations *)
		  (CSManager.trail (fn () =>
				    rSolve (ps', (r, I.comp(s, I.Shift(k))), dp,
					    (fn S => sc ((C.Dc k)::S)))); 
		   matchDProg (dPool', k+1))
		end 
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
  fun retrieval (Loop, (p,s), dp as C.DProg(G, dPool), sc, answRef, n) =    
    if T.noAnswers answRef then 	    
      (* still  no answers available from previous stages *)
      (* NOTE: do not add the susp goal to suspGoal list
	        because it is already in the suspGoal list *)
      ()
      else 
	let
	  val goal = A.raiseType(G, I.EClo(p,s))
	  val (G', DAVars, DEVars, U', eqn', s') =   A.abstractEVarCtx (G, p, s)
	    val _ = if solveEqn ((eqn', s'), G') 
		    then ()  
		  else print "\nresidual equation not solvable!\n"  
	in 
	(*  new answers available from previous stages
	 * resolve current goal with all "new" possible answers
	 *)
	retrieve (n, goal, G', (U', s'),((G', DAVars, DEVars, U', eqn'), answRef), sc)
	end 
    | retrieval (Divergence, (p,s), dp as C.DProg(G, dPool), sc, answRef, n) =    
	let
	  val (G', DAVars, DEVars, U', eqn', s') =   A.abstractEVarCtx (G, p, s)
	in 
	  matchAtom ((p,s), dp, 
		     (fn pskeleton =>
		      case MT.answerCheck (G', U', s', answRef, pskeleton)
			of T.repeated => ()
		      | T.new      => sc pskeleton
			  ))
	end 

  
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
       | resume ((((Susp, (p,s), dp as C.DProg (G, _), sc), trail, answRef, k)::Goals),n) =
       (CSManager.trail	(fn () => (Unify.resume trail; 	 				   
				   retrieval (Susp, (p,s), dp, sc, answRef, k)));
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



