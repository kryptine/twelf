(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)

functor AbsMachine (structure IntSyn' : INTSYN
		    structure CompSyn' : COMPSYN
		      sharing CompSyn'.IntSyn = IntSyn'
		    structure Unify : UNIFY
		      sharing Unify.IntSyn = IntSyn'

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
  : ABSMACHINE =
struct

  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'

  local
    structure I = IntSyn
    structure C = CompSyn

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
                              
  (* solve' ((g, s), dp, sc, bt) = ()
     Invariants:
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated
     Note: backtracking is allowed iff bt () = true
     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)
  fun solve' ((C.Atom(p), s), dp, sc, bt) = matchAtom ((p,s), dp, sc, bt)
    | solve' ((C.Impl(r, A, Ha, g), s), C.DProg (G, dPool), sc, bt) =
      let
	val D' = I.Dec(NONE, I.EClo(A,s))
      in
	solve' ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec (r, s, Ha))),
	        (fn M => sc (I.Lam (D', M))), bt)
      end
    | solve' ((C.All(D, g), s), C.DProg (G, dPool), sc, bt) =
      let
	val D' = I.decSub (D, s)
      in
	solve' ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl(dPool, C.Parameter)),
	        (fn M => sc (I.Lam (D', M))), bt)
      end

  (* rSolve ((p,s'), (r,s), dp, sc, bt) = ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- r  resgoal
       G |- s' : G''
       G'' |- p : H @ S' (mod whnf)
       if G |- S : r[s]
       then sc S is evaluated
     Note: backtracking is allowed iff bt () = true
     Effects: instantiation of EVars in p[s'], r[s], and dp
              any effect  sc S  might have
  *)
  and rSolve (ps', (C.Eq(Q), s), C.DProg (G, dPool), sc, bt) =     
      (if Unify.unifiable (G, ps', (Q, s)) (* effect: instantiate EVars *)
	 then sc I.Nil			(* call success continuation *)
       else ())				(* fail *)

    | rSolve (ps', (C.Assign(Q, eqns), s), dp as C.DProg(G, dPool), sc, bt) = 
	(case Assign.assignable (G, ps', (Q, s))
	   of SOME(cnstr) =>
                aSolve((eqns, s), dp, cnstr, (fn () => sc I.Nil), bt)
	    | NONE => ())

    | rSolve (ps', (C.And(r, A, g), s), dp as C.DProg (G, dPool), sc, bt) =
      let
	(* is this EVar redundant? -fp *)
	val X = I.newEVar (G, I.EClo(A, s))
      in
        rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp,
		(fn S => solve' ((g, s), dp, (fn M => sc (I.App (M, S))), bt)), bt)
      end
    | rSolve (ps', (C.Exists(I.Dec(_,A), r), s), dp as C.DProg (G, dPool), sc, bt) =
      let
	val X = I.newEVar (G, I.EClo (A,s))
      in
	rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp, (fn S => sc (I.App(X,S))), bt)
      end
    | rSolve (ps', (C.Axists(I.ADec(_, d), r), s), dp as C.DProg (G, dPool), sc, bt) =
      let
	val X' = I.newAVar ()
      in
	rSolve (ps', (r, I.Dot(I.Exp(I.EClo(X', I.Shift(~d))), s)), dp, sc, bt)
   	(* we don't increase the proof term here! *)
      end

  (* aSolve ((ag, s), dp, sc, bt) = ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated
     Note: backtracking is allowed iff bt () = true
     Effects: instantiation of EVars in ag[s], dp and sc () *)

  and aSolve ((C.Trivial, s), dp, cnstr, sc, bt) = 
      (if Assign.solveCnstr cnstr then sc () else ())
    | aSolve ((C.UnifyEq(G',e1, N, eqns), s), dp as C.DProg(G, dPool), cnstr, sc, bt) =
      let
	val G'' = compose' (G', G)
	val s' = shift (G', s)
      in 
	if Assign.unifiable (G'', (N, s'), (e1, s'))
	then aSolve ((eqns, s), dp, cnstr, sc, bt)
	else ()
     end

  (* matchatom ((p, s), dp, sc, bt) => ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated
     Note: backtracking is allowed iff bt () = true
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *)
  and matchAtom (ps' as (I.Root(Ha,S),s), dp as C.DProg (G,dPool), sc, bt) =
      let
        val deterministic = C.detTableCheck (cidFromHead Ha)
        (* matchSig [c1,...,cn] = ()
	   try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
	fun matchSig nil = ()	(* return unit on failure *)
	  | matchSig (Hc::sgn') =
	    let
	      val C.SClause(r) = C.sProgLookup (cidFromHead Hc)
              val btRef = ref true : bool ref
              val bt' = if deterministic
                        then (fn () => !btRef andalso bt ())
                        else bt
	      val _ =
	        (* trail to undo EVar instantiations *)
	        CSManager.trail
                  (fn () =>
                     rSolve (ps', (r, I.id), dp,
                             (fn S => (btRef := (not deterministic);
                                       sc (I.Root(Hc, S)))), bt'))
            in
	      if(bt' ())
              then matchSig sgn'
              else ()
	    end

        (* matchDProg (dPool, k) = ()
	   where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
	fun matchDProg (I.Null, _) =
	    (* dynamic program exhausted, try signature *)
	    matchSig (Index.lookup (cidFromHead Ha)) 
	  | matchDProg (I.Decl (dPool', C.Dec (r, s, Ha')), k) =
	    if eqHead (Ha, Ha')
	    then
              let
                val btRef = ref true : bool ref
                val bt' = if deterministic
                          then (fn () => !btRef andalso bt ())
                          else bt
	        val _ =
                  CSManager.trail (* trail to undo EVar instantiations *)
                    (fn () => rSolve (ps', (r, I.comp(s, I.Shift(k))), dp,
                                      (fn S => (btRef := (not deterministic);
                                                sc (I.Root(I.BVar(k), S)))), bt'))
              in
                if(bt' ())
                then matchDProg (dPool', k+1)
                else ()
              end
	    else matchDProg (dPool', k+1)
	  | matchDProg (I.Decl (dPool', C.Parameter), k) =
	      matchDProg (dPool', k+1)
        fun matchConstraint (solve, try) =
              let
                val resOpt =
                  CSManager.trail   (* trail to undo EVar instantiations *)
                    (fn () =>
                       case (solve (G, I.SClo (S, s), try))
                         of SOME(U) => SOME(sc (U))
                          | NONE => NONE)
              in
                case resOpt
                  of SOME _ =>
                       (if (not deterministic andalso bt ())
                        then matchConstraint (solve, try+1)
                        else ())
                   | NONE => ()
              end
      in
        case I.constStatus(cidFromHead Ha)
          of (I.Constraint (cs, solve)) => matchConstraint (solve, 0)
           | _ => matchDProg (dPool, 1)
      end
  in
    fun solve (gs, dp, sc) = solve'(gs, dp, (fn (U) => sc (U)), (fn () => true))
  end (* local ... *)

end; (* functor AbsMachine *)