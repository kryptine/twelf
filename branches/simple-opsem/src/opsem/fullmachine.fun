(* Abstract Machine for full solver *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)
(* Modified: Kevin Watkins *)

functor FullMachine (structure IntSyn' : INTSYN
		     structure CompSyn' : COMPSYN
		     sharing CompSyn'.IntSyn = IntSyn'
		     structure Unify : UNIFY
		     sharing Unify.IntSyn = IntSyn'
                     structure Whnf : WHNF
                     sharing Whnf.IntSyn = IntSyn'
                     structure FullComp : FULLCOMP
		     sharing FullComp.IntSyn = IntSyn'
		     sharing FullComp.CompSyn = CompSyn'
		     structure Index : INDEX
		     sharing Index.IntSyn = IntSyn'
                     structure IndexSkolem : INDEX
                     sharing IndexSkolem.IntSyn = IntSyn'
                     structure CPrint : CPRINT
                     sharing CPrint.IntSyn = IntSyn'
                     sharing CPrint.CompSyn = CompSyn'
                     sharing CPrint.FullComp = FullComp
		     structure CSManager : CS_MANAGER
		     sharing CSManager.IntSyn = IntSyn')
	: ABSMACHINE =
struct

  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'
  structure Compile = FullComp

  local
    structure I = IntSyn
    structure C = CompSyn
    structure F = FullComp
  in

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

  (* gSolve ((g, s), dp, sc) => ()
     Invariants:
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated
     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)
  fun gSolve ((C.Atom(p), s), dp, sc) =
        matchAtom ((p, s), dp, sc)
    | gSolve ((C.Impl(r, A, a, g), s), C.DProg (G, dPool), sc) =
      let
	val D' = I.Dec (NONE, I.EClo (A, s))
      in
	gSolve ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, SOME(r, s, a))),
		(fn M => sc (I.Lam (D', M))))
      end
    | gSolve ((C.All(D, g), s), C.DProg (G, dPool), sc) =
      let
	val D' = I.decSub (D, s)
      in
	gSolve ((g, I.dot1 s), C.DProg (I.Decl (G, D'), I.Decl (dPool, NONE)),
		(fn M => sc (I.Lam (D', M))))
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
        if Unify.unifiable (G, ps', (Q, s)) (* effect: instantiate EVars *)
          then sc I.Nil			(* call success continuation *)
        else ()				(* fail *)
    | rSolve (ps', (C.And(r, A, g), s), dp as C.DProg (G, dPool), sc) =
      let
	(* is this EVar redundant? -fp *)
	val X = I.newEVar (G, I.EClo(A, s))
      in
        rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp,
		(fn S => gSolve ((g, s), dp,
				(fn M => sc (I.App (M, S))))))
      end
    | rSolve (ps', (C.Exists(I.Dec(_,A), r), s), dp as C.DProg (G, dPool), sc) =
      let
	val X = I.newEVar (G, I.EClo (A,s))
      in
	rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp,
		(fn S => sc (I.App(X,S))))
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
  and matchAtom (ps' as (I.Root(I.Const(a),S),s), dp as C.DProg (G,dPool), sc) =
      let
        (* matchSig [c1,...,cn] = ()
	   try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
	fun matchSig nil = ()	(* return indicates failure *)
	  | matchSig ((H as I.Const c)::sgn') =
	    let
	      val F.SClause(r) = F.sProgLookup c
	    in
	      (* trail to undo EVar instantiations *)
	      CSManager.trail (fn () =>
			       rSolve (ps', (r, I.id), dp,
				       (fn S => sc (I.Root(H, S))))) ;
	      matchSig sgn'
	    end

        (* matchDProg (dPool, k) = ()
	   where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
	fun matchDProg (I.Null, _) =
	    (* dynamic program exhausted, try signature *)
	    matchSig (Index.lookup a) 
	  | matchDProg (I.Decl (dPool', SOME(r, s, a')), k) =
	    if a = a'
	      then (* trail to undo EVar instantiations *)
		    (CSManager.trail (fn () =>
		                      rSolve (ps', (r, I.comp(s, I.Shift(k))), dp,
				              (fn S => sc (I.Root(I.BVar(k), S))))) ;
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
                         of SOME(U) => (sc (U) ; true)
                          | NONE => false)
              in
                if succeeded
                then matchConstraint (solve, try+1)
                else ()
              end      
      in
        case I.constStatus(a)
          of (I.Constraint (cs, solve)) => matchConstraint (solve, 0)
           | _ => matchDProg (dPool, 1)
      end

  fun qSolve ((C.QueryGoal(g), s), dp, sc) =
        gSolve((g, s), dp, sc)
    | qSolve ((C.QueryVar(U, _, q), s), dp, sc) =
        qSolve ((q, I.Dot(I.Exp(U), s)), dp, sc)

  (* isInstantiated (V) = SOME(cid) or NONE
     where cid is the type family of the atomic target type of V,
     NONE if V is a kind or object or have variable type.
  *)
  fun isInstantiated (I.Root (I.Const(cid), _)) = true
    | isInstantiated (I.Pi(_, V)) = isInstantiated V
    | isInstantiated (I.Root (I.Def(cid), _)) = true
    | isInstantiated (I.Redex (V, S)) = isInstantiated V
    | isInstantiated (I.Lam (_, V)) = isInstantiated V
    | isInstantiated (I.EVar (ref (SOME(V)),_,_,_)) = isInstantiated V
    | isInstantiated (I.EClo (V, s)) = isInstantiated V
    | isInstantiated _ = false
      

  fun gBSolve (max, (C.Atom(p), s), depth, dp, sc) =
        boundedMatchAtom (max, (p, s), depth, dp, sc)
    | gBSolve (max, (C.Impl(r, A, a, g), s), depth, C.DProg (G, dPool), sc) =
      let
        val D' = I.Dec (NONE, I.EClo (A, s))
      in
        gBSolve (max, (g, I.dot1 s), depth+1,
                       C.DProg (I.Decl (G, D'), I.Decl (dPool, SOME(r, s, a))),
                       (fn M => sc (I.Lam (D', M))))
      end
    | gBSolve (max, (C.All (D, g), s), depth, C.DProg (G, dPool), sc) =
      let
        val D' = I.decSub (D, s)
      in
        gBSolve (max, (g, I.dot1 s), depth+1,
                       C.DProg (I.Decl (G, D'), I.Decl (dPool, NONE)),
                       (fn M => sc (I.Lam (D', M))))
      end

  and rBSolve (max, NONE, (C.True, s), depth, dp, sc) = sc I.Nil
    | rBSolve (max, SOME ps', (C.Eq (Q), s), depth, C.DProg (G, dPool), sc) =
        if Unify.unifiable (G, ps', (Q, s))
          then sc I.Nil
        else ()
    | rBSolve (max, ps', (C.And (r, A, g), s), depth, dp as C.DProg (G, dPool), sc) =
      let
	(* is this EVar redundant? -fp *)
        val X = I.newEVar (G, I.EClo (A, s))
      in
        rBSolve (max, ps', (r, I.Dot (I.Exp (X), s)), depth, dp,
                       (fn S => gBSolve (max, (g, s), depth, dp,
                                               (fn M => sc (I.App (M, S))))))
      end
    | rBSolve (max, ps', (C.In (r, A, g), s), depth, dp as C.DProg (G, dPool), sc) =
      let
					(* G |- g goal *)
					(* G |- A : type *)
					(* G, A |- r resgoal *)
					(* G0, Gl  |- s : G *)
	val G0 = I.ctxDrop (G, depth)
	val dPool0 = I.ctxDrop (dPool, depth)
	val w = I.Shift (depth)		(* G0, Gl  |- w : G0 *)
	val iw = Whnf.invert w
					(* G0 |- iw : G0, Gl *)
	val s' = I.comp (s, iw)
					(* G0 |- w : G *)
	val X = I.newEVar (G0, I.EClo(A, s'))
					(* G0 |- X : A[s'] *)
	val X' = I.EClo (X, w)
					(* G0, Gl |- X' : A[s'][w] = A[s] *)
      in
	rBSolve (max, ps', (r, I.Dot (I.Exp (X'), s)), depth, dp,
		(fn S => 
		 if isInstantiated X then sc (I.App (X', S))
		 else gBSolve (max, (g, s'), 0, C.DProg (G0, dPool0),
			      (fn M => 
			       ((Unify.unify (G0, (X, I.id), (M, I.id)); 
				 sc (I.App (I.EClo (M, w), S))) 
				handle Unify.Unify _ => ())))))
      end
    | rBSolve (max, ps', (C.Exists (I.Dec (_, A), r), s), depth, dp as C.DProg (G, dPool), sc) =
      let
        val X = I.newEVar (G, I.EClo (A, s))
      in
        rBSolve (max, ps', (r, I.Dot (I.Exp (X), s)), depth, dp,
                       (fn S => sc (I.App (X, S))))
      end

  and boundedMatchAtom (0, _, _, _, _) = ()
    | boundedMatchAtom (max, ps' as (I.Root (I.Const (a), S), s),
                        depth, dp as C.DProg (G, dPool), sc) =
      let
        (* matchSig [c1,...,cn] = ()
	   try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
	fun matchSig nil = ()	(* return indicates failure *)
	  | matchSig (H::sgn') =
	    let
              val c = (case H
                         of I.Const c => c
                          | I.Skonst c => c)
	      val F.SClause(r) = F.sProgLookup c
	    in
	      (* trail to undo EVar instantiations *)
	      CSManager.trail (fn () =>
                rBSolve (max-1, SOME ps', (r, I.id), depth, dp,
                               (fn S => sc (I.Root (H, S))))) ;
	      matchSig sgn'
	    end

        (* matchDProg (dPool, k) = ()
	   where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
	fun matchDProg (I.Null, _) =
	    (* dynamic program exhausted, try signature *)
	      matchSig (IndexSkolem.lookup a) 
	  | matchDProg (I.Decl (dPool', SOME(r, s, a')), k) =
	    if a = a'
	      then (* trail to undo EVar instantiations *)
		    (CSManager.trail (fn () =>
		      rBSolve (max-1, SOME ps', (r, I.comp(s, I.Shift(k))),
                                     depth, dp,
                                     (fn S => sc (I.Root(I.BVar(k), S))))) ;
		     matchDProg (dPool', k+1))
	    else matchDProg (dPool', k+1)
	  | matchDProg (I.Decl (dPool', NONE), k) =
	      matchDProg (dPool', k+1)
      (*fun matchConstraint (solve, try) =
              let
                val succeeded =
                  CSManager.trail
                    (fn () =>
                       case (solve (G, I.SClo (S, s), try))
                         of SOME(U) => (sc (U) ; true)
                          | NONE => false)
              in
                if succeeded
                then matchConstraint (solve, try+1)
                else ()
              end      *)
      in
      (*case I.constStatus(a)
          of (I.Constraint (cs, solve)) => matchConstraint (solve, 0)
           | _ =>*) matchDProg (dPool, 1)
      end

  val trail = CSManager.trail

  fun solve (q, sc) = qSolve ((q, I.id), C.DProg (I.Null, I.Null), sc)
  fun gBoundedSolve (max, g, depth, dp, sc) =
        gBSolve (max, (g, I.id), depth, dp, sc)
  fun rBoundedSolve (max, r, depth, dp, sc) =
        rBSolve (max, NONE, (r, I.id), depth, dp, sc)

  val reset = CSManager.reset

  end (* local ... *)

end; (* functor FullMachine *)