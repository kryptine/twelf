(* Simple abstract machine *)
(* Author: Kevin Watkins *)

functor SimpMachine(structure IntSyn : INTSYN
                    structure CompSyn : COMPSYN
                      sharing CompSyn.IntSyn = IntSyn
                    structure CPrint : CPRINT
                      sharing CPrint.IntSyn = IntSyn
                      sharing CPrint.CompSyn = CompSyn
                    structure ElabSolution : ELABSOLUTION
                      sharing ElabSolution.IntSyn = IntSyn
                      sharing ElabSolution.CompSyn = CompSyn
                    structure SimpSyn : SIMPSYN
                      sharing SimpSyn.IntSyn = IntSyn
		    structure SimpWhnf : SIMPWHNF
		      sharing SimpWhnf.SimpSyn = SimpSyn
                    structure SimpUnify : SIMPUNIFY
                      sharing SimpUnify.SimpSyn = SimpSyn
                    structure SimpComp : SIMPCOMP
                      sharing SimpComp.IntSyn = IntSyn
                      sharing SimpComp.CompSyn = CompSyn
                      sharing SimpComp.SimpSyn = SimpSyn
                    structure Index : INDEX
                      sharing Index.IntSyn = IntSyn
                    structure IndexSkolem : INDEX
                      sharing IndexSkolem.IntSyn = IntSyn
                    structure CSManager : CS_MANAGER
                      sharing CSManager.IntSyn = IntSyn) : ABSMACHINE =
struct

  structure IntSyn = IntSyn
  structure CompSyn = CompSyn
  structure Compile = SimpComp

  structure I = IntSyn
  structure C = CompSyn
  structure S = SimpSyn
  structure F = SimpComp

  local
    val stats = Array.array(100, (0,0,0))
  in
    fun resetStats () = Array.modify (fn _ => (0,0,0)) stats
    fun printStat (n, ns, nd) =
          if n > 0 then print (Int.toString n^","^
			       Int.toString ns^"/"^
			       Int.toString nd^"\t")
	    else ()
    fun printStats () = (print "\n"; Array.app printStat stats)
    fun tick (max, ns, nd) =
        let
	  val (n, _, _) = Array.sub(stats, max-1)
	in
          Array.update(stats, max-1, (n+1, ns, nd));
	  if max = 1 andalso (n+1) mod 1000 = 0
	    then printStats ()
	  else ()
	end
  end

  fun trail f = (SimpUnify.mark (); f (); SimpUnify.unwind ())

  fun abstract (X, 0) = X
    | abstract (X, n) = abstract (S.Lam(X), n-1)

  fun gSolve ((S.Atom(p), s), dp, sc) = matchAtom ((p, s), dp, sc)
    | gSolve ((S.Impl(r, a, g), s), dp, sc) =
        gSolve ((g, S.dot1 s), I.Decl(dp, SOME(r, s, a)),
               fn sol => sc (C.ImplSol(sol)))
    | gSolve ((S.All(g), s), dp, sc) =
        gSolve ((g, S.dot1 s), I.Decl(dp, NONE),
               fn sol => sc (C.AllSol(sol)))

  and rSolve (ps, (S.Eq(U), s), dp, sc) =
        if SimpUnify.unifiable (ps, (U, s)) then sc(C.EqSol) else ()
    | rSolve (ps, (S.And(r, g), s), dp, sc) =
        rSolve (ps, (r, s), dp,
                fn rsol => gSolve ((g, s), dp,
                                  fn sol => sc (C.AndSol(rsol, sol))))
    | rSolve (ps, (S.Exists(n, r), s), dp, sc) =
        rSolve (ps, (r, S.Dot(S.Exp(abstract (S.newEVar (), n)), s)), dp,
                fn rsol => sc (C.ExistsSol(rsol)))

  and matchAtom (ps as (S.Root(S.Const(a), S), s), dp, sc) =
      let
        fun matchSig nil = ()
          | matchSig (I.Const(c)::sgn') =
            let
              val F.SClause(r) = F.sProgLookup(c)
            in
              trail
              (fn () =>
               rSolve (ps, (r, S.id), dp,
                       fn rsol => sc (C.SigAtom(c, rsol))));
              matchSig sgn'
            end

        fun matchDProg (I.Null, _) =
              matchSig (Index.lookup a)
          | matchDProg (I.Decl (dp', SOME(r, s, a')), k) =
              if a = a'
                then (trail
                      (fn () =>
                       rSolve (ps, (r, S.comp(s, S.Shift(k))), dp,
                               fn rsol => sc (C.DynAtom(k, rsol))));
                      matchDProg (dp', k+1))
              else matchDProg (dp', k+1)
          | matchDProg (I.Decl (dp', NONE), k) =
              matchDProg (dp', k+1)

        (* need to figure out how to make constraint solvers independent
           of differences between IntSyn and SimpSyn...
        fun matchConstraint (solve, try) =
            let
              val try_again =
                    trail
                    (fn () => case solve (...what here?...,
                                          S.SClo (S, s),
                                          try)
                                of SOME(_) => (sc (C.ConstrSol(try));
                                               true)
                                 | NONE => false)
            in
              if try_again
                then matchConstraint (solve, try+1)
              else ()
            end
        *)
      in
        case I.constStatus(a)
          of I.Normal => matchDProg (dp, 1)
            (* FAILS for constraints and foreign constants *)
      end

  fun qSolve ((S.QueryGoal(g), s), dp, sc) = gSolve((g, s), dp, sc)
    | qSolve ((S.QueryVar(U, q), s), dp, sc) =
        qSolve ((q, S.Dot(S.Exp(U), s)), dp, sc)

  fun gBSolve (max, (S.Atom(p), s), depth, dp, sc) =
        boundedMatchAtom (max, (p, s), depth, dp, sc)
    | gBSolve (max, (S.Impl(r, a, g), s), depth, dp, sc) =
        gBSolve (max, (g, S.dot1 s),
                 depth+1, I.Decl(dp, SOME(r, s, a)),
                 fn sol => sc (C.ImplSol(sol)))
    | gBSolve (max, (S.All(g), s), depth, dp, sc) =
        gBSolve (max, (g, S.dot1 s),
                 depth+1, I.Decl(dp, NONE),
                 fn sol => sc (C.AllSol(sol)))

  and rBSolve (max, NONE, (S.True, s), depth, dp, sc) =
        sc C.TrueSol
    | rBSolve (max, SOME ps, (S.Eq(U), s), depth, dp, sc) =
        if SimpUnify.unifiable (ps, (U, s)) then sc(C.EqSol) else ()
    | rBSolve (max, ps, (S.And(r, g), s), depth, dp, sc) =
        rBSolve (max, ps, (r, s), depth, dp,
                 fn rsol => gBSolve (max, (g, s), depth, dp,
                                     fn sol => sc (C.AndSol(rsol, sol))))
    | rBSolve (max, ps, (S.AndMeta(r, g), s), depth, dp, sc) =
      let
	val w = S.Shift (depth)
	val iw = SimpWhnf.invert w
      in
        rBSolve (max, ps, (r, s), depth, dp,
                 fn rsol => gBSolve (max, (g, S.comp (s, iw)),
                                     0, I.ctxDrop (dp, depth),
                                     fn sol => sc (C.AndSol(rsol, sol))))
      end
    | rBSolve (max, ps, (S.Exists(n, r), s), depth, dp, sc) =
        rBSolve (max, ps, (r, S.Dot(S.Exp(abstract (S.newEVar (), n)), s)),
                 depth, dp,
                 fn rsol => sc (C.ExistsSol(rsol)))
    | rBSolve (max, ps, (S.ExistsMeta(n, r), s), depth, dp, sc) =
      let
        val X = S.EClo (S.newEVar (), S.Shift (depth))
      in
        rBSolve (max, ps, (r, S.Dot (S.Exp (abstract (X, n)), s)),
                 depth, dp,
                 fn rsol => sc (C.ExistsSol(rsol)))
      end

  and boundedMatchAtom (0, _, _, _, _) = ()
    | boundedMatchAtom (max, ps as (S.Root(S.Const(a), S), s), depth, dp, sc) =
      let
	val nd = I.ctxLength dp
	val ns = List.length (IndexSkolem.lookup a)
	val _ = tick (max, ns, nd)
        fun matchSig nil = (if max >= 4 then print "E" else ())
          | matchSig (H::sgn') =
            let
              val c = (case H
                         of I.Const c => c
                          | I.Skonst c => c)
              val F.SClause(r) = F.sProgLookup(c)
            in
              trail
              (fn () =>
               rBSolve (max-1, SOME ps, (r, S.id), depth, dp,
                              fn rsol => sc (C.SigAtom(c, rsol))));
	      if max >= 4 then print "X" else ();
              matchSig sgn'
            end

        fun matchDProg (I.Null, _) =
              matchSig (IndexSkolem.lookup a)
          | matchDProg (I.Decl (dp', SOME(r, s, a')), k) =
              if a = a'
                then (trail
                      (fn () =>
                       rBSolve (max-1, SOME ps, (r, S.comp(s, S.Shift(k))),
                                      depth, dp,
                                      fn rsol => sc (C.DynAtom(k, rsol))));
		      if max >= 4 then print "X" else ();
                      matchDProg (dp', k+1))
              else (if max >= 4 then print "X" else ();
		      matchDProg (dp', k+1))
          | matchDProg (I.Decl (dp', NONE), k) =
              (if max >= 4 then print "X" else ();
		 matchDProg (dp', k+1))

        (* need to figure out how to make constraint solvers independent
           of differences between IntSyn and SimpSyn...
        fun matchConstraint (solve, try) =
            let
              val try_again =
                    trail
                    (fn () => case solve (...what here?...,
                                          S.SClo (S, s),
                                          try)
                                of SOME(_) => (sc (C.ConstrSol(try));
                                               true)
                                 | NONE => false)
            in
              if try_again
                then matchConstraint (solve, try+1)
              else ()
            end
        *)
      in
        case I.constStatus(a)
          of I.Normal => matchDProg (dp, 1)
            (* FAILS for constraints and foreign constants *)
      end

  fun solve (q, sc) =
      (
       resetStats();
       qSolve((SimpComp.translQuery(I.Null, q), S.id), I.Null,
              fn sol => (printStats();
(*                         print ("Solution is:\n" ^
                                CPrint.solToString "" sol);*)
                         CSManager.trail
                         (fn () =>
                          sc(ElabSolution.elaborate(sol, q)))))
       )

  fun gBoundedSolve (max, g, depth, (dp1 as C.DProg (G, dPool), dp2), sc) =
      (resetStats();
       gBSolve (max, (SimpComp.translGoal (G, (g, I.id)), S.id),
		depth, dp2,
		fn sol =>
		(printStats();
		 CSManager.trail
                 (fn () =>
                  sc (ElabSolution.elaborateMeta (sol, g, depth, dp1))))))
  fun rBoundedSolve (max, r, depth, (dp1 as C.DProg (G, dPool), dp2), sc) =
      (resetStats();
       rBSolve (max, NONE, (SimpComp.translResGoal (G, (r, I.id)), S.id),
		depth, dp2,
		fn rsol =>
		(printStats();
		 CSManager.trail
                 (fn () =>
                  sc (ElabSolution.elaborateRMeta (rsol, r, depth, dp1))))))

  fun reset () = (SimpUnify.reset (); CSManager.reset ())

end
