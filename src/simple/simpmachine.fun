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
                    structure SimpUnify : SIMPUNIFY
                      sharing SimpUnify.SimpSyn = SimpSyn
                    structure SimpComp : SIMPCOMP
                      sharing SimpComp.IntSyn = IntSyn
                      sharing SimpComp.CompSyn = CompSyn
                      sharing SimpComp.SimpSyn = SimpSyn
                    structure Index : INDEX
                      sharing Index.IntSyn = IntSyn
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

  fun trail f = (SimpUnify.mark (); f (); SimpUnify.unwind ())

  fun gSolve ((S.Atom(p), s), dp, sc) = matchAtom ((p, s), dp, sc)
    | gSolve ((S.Impl(r, a, g), s), dp, sc) =
        gSolve ((g, S.dot1 s), I.Decl(dp, SOME(r, s, a)),
               fn sol => sc (C.ImplSol(sol)))
    | gSolve ((S.All(g), s), dp, sc) =
        gSolve ((g, S.dot1 s), I.Decl(dp, NONE),
               fn sol => sc (C.AllSol(sol)))

  and rSolve (ps, (S.Eq(U), s), dp, sc) =
(*        ((SimpUnify.unify (ps, (U, s));
          print "succeed\n";
          sc (C.EqSol))
         handle SimpUnify.Unify(s) => print ("fail " ^ s ^ "\n")) *)
        if SimpUnify.unifiable (ps, (U, s)) then sc(C.EqSol) else ()
    | rSolve (ps, (S.And(r, g), s), dp, sc) =
        (* Assumes And is never truly dependent *)
        rSolve (ps, (r, S.Dot(S.Undef, s)), dp,
                fn rsol => gSolve ((g, s), dp,
                                  fn sol => sc (C.AndSol(rsol, sol))))
    | rSolve (ps, (S.Exists(n, r), s), dp, sc) =
      let
        val X = S.newEVar ()
        fun abstract (X, 0) = X
          | abstract (X, n) = abstract (S.Lam(X), n-1)
      in
        rSolve (ps, (r, S.Dot(S.Exp(abstract (X, n)), s)), dp,
                fn rsol => sc (C.ExistsSol(rsol)))
      end

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

  fun solve (q, sc) =
      (
       qSolve((SimpComp.translQuery(q), S.id), I.Null,
              fn sol => (
(*                         print ("Solution is:\n" ^
                                CPrint.solToString "" sol);*)
                         CSManager.trail
                         (fn () =>
                          sc(ElabSolution.elaborate(sol, q)))))
       )

  fun reset () = (SimpUnify.reset (); CSManager.reset ())

end
