(* Elaborate simple solution into full solution *)
(* Author: Kevin Watkins *)

functor ElabSolution(structure IntSyn : INTSYN
                     structure CompSyn : COMPSYN
                       sharing CompSyn.IntSyn = IntSyn
                     structure FullComp : FULLCOMP
                       sharing FullComp.IntSyn = IntSyn
                       sharing FullComp.CompSyn = CompSyn
                     structure Whnf : WHNF
                       sharing Whnf.IntSyn = IntSyn
                     structure Unify : UNIFY
                       sharing Unify.IntSyn = IntSyn
                     structure Print : PRINT
                       sharing Print.IntSyn = IntSyn
                     structure CPrint : CPRINT
                       sharing CPrint.IntSyn = IntSyn
                       sharing CPrint.CompSyn = CompSyn
                       sharing CPrint.FullComp = FullComp
                       ) : ELABSOLUTION =
struct

  structure IntSyn = IntSyn
  structure CompSyn = CompSyn

  structure I = IntSyn
  structure C = CompSyn
  structure F = FullComp

  (*
     The simple solution is not assumed to be valid in any way.  If
     not, the following exception should be raised rather than a match
     failure or some such.

     Actually, is this true?  It may be possible for partially
     successful unifications to cause instantiations which violate
     invariants?
  *)

  val BadSolution = Fail

  fun solve (sol, (C.Atom(p), s), dp) = matchAtom (sol, (p, s), dp)
    | solve (C.ImplSol(sol), (C.Impl(r, A, a, g), s), C.DProg (G, dPool)) =
      let
        val D' = I.Dec (NONE, I.EClo(A, s))
      in
        I.Lam (D', solve (sol, (g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, SOME(r, s, a)))))
      end
    | solve (C.AllSol(sol), (C.All(D, g), s), C.DProg(G, dPool)) =
      let
        val D' = I.decSub (D, s)
      in
        I.Lam (D', solve (sol, (g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, NONE))))
      end
    | solve _ = raise BadSolution ""

  and rSolve (C.EqSol, ps, (C.Eq(Q), s), C.DProg (G, dPool)) =
      if Unify.unifiable (G, ps, (Q, s))
        then I.Nil
      else raise BadSolution
        ("Unify " ^ Print.expToString(G, I.EClo(ps)) ^ "\n" ^
         " with " ^ Print.expToString(G, I.EClo(Q,s)) ^ "\n")
    | rSolve (C.AndSol(rsol, sol), ps, (C.And(r, A, g), s), dp as C.DProg (G, dPool)) =
      let
	(* is this EVar redundant? -fp *)
        (* I will assume so.  -kw
           val X = I.newEvar (G, I.EClo(A, s)) *)
        val S = rSolve (rsol, ps, (r, I.Dot (I.Undef, s)), dp)
        val M = solve (sol, (g, s), dp)
      in
        I.App (M, S)
      end
    | rSolve (C.ExistsSol(rsol), ps, (C.Exists(I.Dec(_,A), r), s), dp as C.DProg (G, dPool)) =
      let
        val X = I.newEVar (G, I.EClo(A, s))
      in
        I.App (X, rSolve (rsol, ps, (r, I.Dot (I.Exp(X), s)), dp))
      end
    | rSolve _ = raise BadSolution ""

  and matchAtom (C.DynAtom(k, rsol), ps, dp as C.DProg (G, dPool)) =
      (case I.ctxLookup (dPool, k)
            handle _ => raise BadSolution ""
         of SOME(r, s, _) => I.Root (I.BVar(k), rSolve (rsol, ps, (r, I.comp(s, I.Shift(k))), dp))
          | NONE => raise BadSolution "")
    | matchAtom (C.SigAtom(c, rsol), ps, dp) =
      (case F.sProgLookup c
         of F.SClause(r) => I.Root (I.Const(c), rSolve (rsol, ps, (r, I.id), dp))
          | F.Void => raise BadSolution "")
    | matchAtom (C.ConstrSol(k), (I.Root(I.Const(a), S), s), C.DProg (G, _)) =
      (case I.constStatus(a)
         of I.Constraint (cs, solve) =>
            (case solve (G, I.SClo (S, s), k)
               of SOME(U) => U
                | NONE => raise BadSolution "")
          | _ => raise BadSolution "")
    | matchAtom _ = raise BadSolution ""

  fun qSolve (sol, (C.QueryGoal(g), s), dp) = solve (sol, (g, s), dp)
    | qSolve (sol, (C.QueryVar(U, _, q), s), dp) =
        qSolve (sol, (q, I.Dot(I.Exp(U), s)), dp)

  fun solveMeta (sol, (C.Atom(p), s), depth, dp) =
        matchAtomMeta (sol, (p, s), depth, dp)
    | solveMeta (C.ImplSol(sol), (C.Impl(r, A, a, g), s),
                 depth, C.DProg (G, dPool)) =
      let
        val D' = I.Dec (NONE, I.EClo(A, s))
      in
        I.Lam (D', solveMeta (sol, (g, I.dot1 s),
                              depth+1, C.DProg (I.Decl(G, D'), I.Decl (dPool, SOME(r, s, a)))))
      end
    | solveMeta (C.AllSol(sol), (C.All(D, g), s),
                 depth, C.DProg(G, dPool)) =
      let
        val D' = I.decSub (D, s)
      in
        I.Lam (D', solveMeta (sol, (g, I.dot1 s),
                              depth+1, C.DProg (I.Decl(G, D'), I.Decl (dPool, NONE))))
      end
    | solveMeta _ = raise BadSolution ""

  and rSolveMeta (C.TrueSol, NONE, (C.True, s), depth, dp) = I.Nil
    | rSolveMeta (C.EqSol, SOME ps, (C.Eq(Q), s), depth, C.DProg (G, dPool)) =
      if Unify.unifiable (G, ps, (Q, s))
        then I.Nil
      else raise BadSolution
        ("Unify " ^ Print.expToString(G, I.EClo(ps)) ^ "\n" ^
         " with " ^ Print.expToString(G, I.EClo(Q,s)) ^ "\n")
    | rSolveMeta (C.AndSol(rsol, sol), ps, (C.And(r, A, g), s),
                  depth, dp as C.DProg (G, dPool)) =
      let
	(* is this EVar redundant? -fp *)
        (* I will assume so.  -kw
           val X = I.newEvar (G, I.EClo(A, s)) *)
        val S = rSolveMeta (rsol, ps, (r, I.Dot (I.Undef, s)), depth, dp)
        val M = solveMeta (sol, (g, s), depth, dp)
      in
        I.App (M, S)
      end
    | rSolveMeta (C.AndSol(rsol, sol), ps, (C.In(r, A, g), s),
                  depth, dp as C.DProg (G, dPool)) =
      let
					(* G, A |- r resgoal *)
					(* G0, Gl  |- s : G *)
	val G0 = I.ctxDrop (G, depth)
	val dPool0 = I.ctxDrop (dPool, depth)
	val w = I.Shift (depth)		(* G0, Gl  |- w : G0 *)
	val iw = Whnf.invert w
					(* G0 |- iw : G0, Gl *)
	val s' = I.comp (s, iw)
					(* G0 |- w : G *)
        val S = rSolveMeta (rsol, ps, (r, I.Dot (I.Undef, s)), depth, dp)
        val M = solveMeta (sol, (g, s'), 0, C.DProg (G0, dPool0))
      in
        I.App (I.EClo (M, w), S)
      end
    | rSolveMeta (C.ExistsSol(rsol), ps, (C.Exists(I.Dec(_,A), r), s),
                  depth, dp as C.DProg (G, dPool)) =
      let
        val X = I.newEVar (G, I.EClo(A, s))
      in
        I.App (X, rSolveMeta (rsol, ps, (r, I.Dot (I.Exp(X), s)), depth, dp))
      end
    | rSolveMeta (C.ExistsSol(rsol), ps, (C.In (r, A, g), s),
                  depth, dp as C.DProg (G, dPool)) =
      let
					(* G0, Gl  |- s : G *)
	val G0 = I.ctxDrop (G, depth)
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
        I.App (X', rSolveMeta (rsol, ps, (r, I.Dot (I.Exp (X'), s)), depth, dp))
      end
    | rSolveMeta _ = raise BadSolution ""

  and matchAtomMeta (C.DynAtom(k, rsol), ps, depth, dp as C.DProg (G, dPool)) =
      (case I.ctxLookup (dPool, k)
            handle _ => raise BadSolution ""
         of SOME(r, s, _) => I.Root (I.BVar(k), rSolveMeta (rsol, SOME ps, (r, I.comp(s, I.Shift(k))), depth, dp))
          | NONE => raise BadSolution "")
    | matchAtomMeta (C.SigAtom(c, rsol), ps, depth, dp) =
      (case F.sProgLookup c
         of F.SClause(r) => I.Root (I.Const(c), rSolveMeta (rsol, SOME ps, (r, I.id), depth, dp))
          | F.Void => raise BadSolution "")
    | matchAtomMeta (C.ConstrSol(k), (I.Root(I.Const(a), S), s), depth, C.DProg (G, _)) =
      (case I.constStatus(a)
         of I.Constraint (cs, solve) =>
            (case solve (G, I.SClo (S, s), k)
               of SOME(U) => U
                | NONE => raise BadSolution "")
          | _ => raise BadSolution "")
    | matchAtomMeta _ = raise BadSolution ""

  exception BadSolution of string

  fun catch f =
      (f ()
       handle e as BadSolution _ => raise e
            | _ => raise BadSolution "Unable to determine cause: invariants violated\n")

  fun elaborate(sol, q) =
        catch (fn () => qSolve(sol, (q, I.id), C.DProg (I.Null, I.Null)))
  fun elaborateMeta (sol, g, depth, dp) =
        catch (fn () => solveMeta (sol, (g, I.id), depth, dp))
  fun elaborateRMeta (rsol, r, depth, dp) =
        catch (fn () => rSolveMeta (rsol, NONE, (r, I.id), depth, dp))

end
