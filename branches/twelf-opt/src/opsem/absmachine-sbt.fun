(* Abstract Machine using substitution trees *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)

functor AbsMachineSbt (structure IntSyn' : INTSYN
		    structure CompSyn' : COMPSYN
		      sharing CompSyn'.IntSyn = IntSyn'
		    structure Unify : UNIFY
		      sharing Unify.IntSyn = IntSyn'
		    structure SubTree : SUBTREE
		      sharing SubTree.IntSyn = IntSyn'
		      sharing SubTree.CompSyn = CompSyn'
                    structure Assign : ASSIGN
		      sharing Assign.IntSyn = IntSyn'

		    structure Index : INDEX
		      sharing Index.IntSyn = IntSyn'
		    (* CPrint currently unused *)
		    structure CPrint : CPRINT 
                      sharing CPrint.IntSyn = IntSyn'
                      sharing CPrint.CompSyn = CompSyn'

		    structure Print : PRINT 
                      sharing Print.IntSyn = IntSyn'

		    structure Names : NAMES 
                      sharing Names.IntSyn = IntSyn'
		    structure CSManager : CS_MANAGER
		      sharing CSManager.IntSyn = IntSyn')
  : ABSMACHINESBT =
struct

  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'

  local
    structure I = IntSyn
    structure C = CompSyn

    val mSig : ((IntSyn.Exp * IntSyn.Sub) * CompSyn.DProg * (CompSyn.Flatterm list -> unit) -> unit) ref = ref (fn (ps, dp, sc) => ())

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

  fun cidFromHead (I.Const a) = a
    | cidFromHead (I.Def a) = a

  fun eqHead (I.Const a, I.Const a') = a = a'
    | eqHead (I.Def a, I.Def a') = a = a'
    | eqHead _ = false

  (* Wed Mar 13 10:27:00 2002 -bp  *)
  (* should probably go to intsyn.fun *)
  fun compose'(IntSyn.Null, G) = G
    | compose'(IntSyn.Decl(G, D), G') = IntSyn.Decl(compose'(G, G'), D)

  fun shift (IntSyn.Null, s) = s
    | shift (IntSyn.Decl(G, D), s) = I.dot1 (shift(G, s))

  (* ctxToEVarSub D = s*)

    fun ctxToEVarSub (Gglobal, I.Null, s) = s
      | ctxToEVarSub (Gglobal, I.Decl(G,I.Dec(_,A)), s) = 
      let
	val s' = ctxToEVarSub (Gglobal, G, s)
	val X = I.newEVar (Gglobal, I.EClo(A,s'))
      in
	I.Dot(I.Exp(X),s')
      end 
      | ctxToEVarSub (Gglobal, I.Decl(G,I.ADec(_,d)), s) = 
      let
	val X = I.newAVar ()
      in
	I.Dot(I.Exp(I.EClo(X, I.Shift(~d))), ctxToEVarSub (Gglobal, G, s))
      end 
                              

  (* solve' ((g, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated with return value res
       else Fail
     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)
  fun solve' ((C.Atom(p), s), dp as C.DProg (G, dpool), sc)  = 
      ((* print "SOLVE "; print (Print.expToString (G, I.EClo(p,s)) ^ "\n");*)
       matchAtom ((p,s), dp, sc))
    | solve' ((C.Impl(r, A, Ha, g), s), C.DProg (G, dPool), sc) =
      let
	val D' = I.Dec(NONE, I.EClo(A,s))
      in
	solve' ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, SOME(r, s, Ha))), sc) 
      end
    | solve' ((C.All(D, g), s), C.DProg (G, dPool), sc) =
      let
	val D' = Names.decLUName (G, I.decSub (D, s)) 
      in
	solve' ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl(dPool, NONE)), sc)
      end

  (* rSolve ((p,s'), (r,s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- r  resgoal
       G |- s' : G''
       G'' |- p : H @ S' (mod whnf)
       if G |- S : r[s]
       then sc S is evaluated with return value res
       else Fail
     Effects: instantiation of EVars in p[s'], r[s], and dp
              any effect  sc S  might have
  *)
  and rSolve (ps', (C.Eq(Q), s), C.DProg (G, dPool), sc)  =     
      (if Unify.unifiable (G, ps', (Q, s)) (* effect: instantiate EVars *)
	 then sc nil			   (* call success continuation *)
       else ())			           (* fail *)

    | rSolve (ps', (C.Assign(Q, eqns), s), dp as C.DProg(G, dPool), sc) = 
	(case Assign.assignable (G, ps', (Q, s))
	   of SOME(cnstr) => aSolve ((eqns, s), dp, cnstr, (fn () => sc nil))
	    | NONE => ())

    | rSolve (ps', (C.And(r, A, g), s), dp as C.DProg (G, dPool), sc) =
      let
	(* is this EVar redundant? -fp *)
	val X = I.newEVar (G, I.EClo(A, s))
      in
(*        rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp,*)
        rSolve (ps', (r, I.comp(I.invShift, s)), dp,
		(fn skel1 => solve' ((g, s), dp,
				 (fn skel2 => sc (skel1 @ skel2)))))
      end 
(*        rSolve (ps', (r, I.comp(I.invShift, s)), dp,*)

    | rSolve (ps', (C.Exists(I.Dec(_,A), r), s), dp as C.DProg (G, dPool), sc) =
      let
	val X = I.newEVar (G, I.EClo (A,s))
      in
	rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp, sc)
      end
    | rSolve (ps', (C.Axists(I.ADec(_, d), r), s), dp as C.DProg (G, dPool), sc) =
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
       else Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)

  and aSolve ((C.Trivial, s), dp, cnstr, sc) = 
      (if Assign.solveCnstr cnstr
	 then sc ()
       else () (* Fail *))
    | aSolve ((C.UnifyEq(G',e1, N, eqns), s), dp as C.DProg(G, dPool), cnstr, sc) =
      let
	val G'' = compose' (G', G)
	val s' = shift (G', s)
      in 
	if Assign.unifiable (G'', (N, s'), (e1, s'))
	  then  aSolve ((eqns, s), dp, cnstr, sc)
	else ()   (* Fail *)
     end

 (* solve subgoals of static program clauses *)
  and sSolve ((C.True, s), dp, sc) = sc nil
    | sSolve ((C.Conjunct (g, Sgoals), s), dp as C.DProg(G, dPool), sc) = 
      solve' ((g, s), dp, (fn F1 => sSolve ((Sgoals, s), dp, (fn F2 => sc (F1 @ F2)))))


   (* match signature *)
  and matchSig (ps' as (I.Root(Ha,S),s), dp as C.DProg (G, dPool), sc) = 
      let
	fun mSig nil = ()	(* return on failure *)
	  | mSig ((Hc as I.Const c)::sgn') =
	  let
	    val C.SClause(r) = C.sProgLookup (cidFromHead Hc)
	  in 
	    (* trail to undo EVar instantiations *)
	    CSManager.trail
	    (fn () =>
	     rSolve (ps', (r, I.id), dp,
		     (fn S => sc ((C.Pc c) :: S))));
	    mSig (sgn')
	  end
      in 
	mSig(Index.lookup (cidFromHead Ha))
      end 


   and matchIndexSig (ps' as (I.Root(Ha,S),s), dp as C.DProg (G, dPool), sc) = 
         SubTree.matchSig (cidFromHead Ha, G, ps', 
			   (fn ((ConjGoals, s), clauseName) => 
			    sSolve ((ConjGoals, s), dp, (fn S => sc ((C.Pc clauseName) :: S)))))

  (* matchatom ((p, s), dp, sc) => res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated with return value res
       else Fail
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *)
  and matchAtom (ps' as (I.Root(Ha,S),s), dp as C.DProg (G, dPool), sc) =
      let
        (* matchDProg (dPool, k) = ()
	   where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
	fun matchDProg (I.Null, _) = 
	    (* dynamic program exhausted, try signature 
               there is a choice depending on how we compiled signature
             *)	  
	  (!mSig) (ps', dp, sc)

	  | matchDProg (I.Decl (dPool', SOME(r, s, Ha')), k) =
	    if eqHead (Ha, Ha')
	      then (CSManager.trail (* trail to undo EVar instantiations *)
                    (fn () => rSolve (ps', (r, I.comp(s, I.Shift(k))), dp,
                                      (fn S => sc ((C.Dc k) :: S))));
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

  in  
      fun solve args  = 
	    (case (!CompSyn.optimize) of
	       CompSyn.No => (mSig := matchSig ; solve' args)
	     | CompSyn.LinearHeads => (mSig := matchSig; solve' args)
(*	     | CompSyn.HeadAccess => (mSig := matchHASig; solve' args)
	     | CompSyn.FirstArg => (mSig := matchFASig; solve' args)*)
	     | CompSyn.Indexing => (mSig := matchIndexSig; solve' args))

  end (* local ... *) 

end; (* functor AbsMachineSbt *)


(* working version of mathHASig
  and matchHASig (deterministic, ps' as (I.Root(Ha,S),s), dp as C.DProg (G, dPool), sc) = 
      let
        exception SucceedOnce of I.Spine
	fun mSig nil = ()	(* return on failure *)
	  | mSig ((Hc as I.Const c)::sgn') =
	  let
	    val C.HeadGoals(H, Sgoals) = C.sProgDHLookup (cidFromHead Hc)
	    val C.Head(Q', G', eqns, cname) = H
	  in 
	    (* trail to undo EVar instantiations *)
	    CSManager.trail
	    (fn () =>
	     let 
	       val s' = ctxToEVarSub (G, G', I.id)
	     in 
	       case Assign.assignable (G, ps', (Q', s')) of
		 SOME(cnstr) => (aSolve((eqns, s'), dp, cnstr, 
					(fn () => (sSolve ((Sgoals, s'), dp, (fn S => sc (I.Root(Hc, S))))))))
	       | NONE => ()
	     end);
	    mSig (sgn')
	  end
	fun mSigDet nil = ()	(* return unit on failure *)
	  | mSigDet ((Hc as I.Const c)::sgn') =
	    let
	      val C.HeadGoals(H, Sgoals) = C.sProgDHLookup (cidFromHead Hc)
	      val C.Head(Q', G', eqns, cname) = H
	    in 
	      (* trail to undo EVar instantiations *)
	      (CSManager.trail
	       (fn () => 
		let 
		  val s' = ctxToEVarSub (G, G', I.id)
		in 
		  case Assign.assignable (G, ps', (Q', s')) of
		    SOME(cnstr) => (aSolve((eqns, s'), dp, cnstr, 
					   (fn () => (sSolve ((Sgoals, s'), dp, (fn S => sc (I.Root(Hc, S))))))))
		  | NONE => ()
		end);
	       mSigDet sgn')
	      handle SucceedOnce S =>  sc (I.Root(Hc, S))
	    end

      in 
	if deterministic then 	mSigDet (Index.lookup (cidFromHead Ha))	
	else mSig(Index.lookup (cidFromHead Ha))	
      end
*)