(* Elaborate simple solution into full solution *)
(* Author: Kevin Watkins *)

functor ElabSolution(structure IntSyn : INTSYN
                     structure CompSyn : COMPSYN
                       sharing CompSyn.IntSyn = IntSyn
                     structure FullComp : FULLCOMP
                       sharing FullComp.IntSyn = IntSyn
                       sharing FullComp.CompSyn = CompSyn
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
    | solve (C.ImplSol(sol), (C.Impl(r, A, a, g), s), F.DProg (G, dPool)) =
      let
        val D' = I.Dec (SOME "-", I.EClo(A, s))
      in
        I.Lam (D', solve (sol, (g, I.dot1 s), F.DProg (I.Decl(G, D'), I.Decl (dPool, SOME(r, s, a)))))
      end
    | solve (C.AllSol(sol), (C.All(D, g), s), F.DProg(G, dPool)) =
      let
        val D' = I.decSub (D, s)
      in
        I.Lam (D', solve (sol, (g, I.dot1 s), F.DProg (I.Decl(G, D'), I.Decl (dPool, NONE))))
      end
    | solve _ = raise BadSolution ""

  and rSolve (C.EqSol, ps, (C.Eq(Q), s), F.DProg (G, dPool)) =
      if Unify.unifiable (G, ps, (Q, s))
        then I.Nil
      else raise BadSolution
        ("Unify " ^ Print.expToString(G, I.EClo(ps)) ^ "\n" ^
         " with " ^ Print.expToString(G, I.EClo(Q,s)) ^ "\n")
    | rSolve (C.AndSol(rsol, sol), ps, (C.And(r, A, g), s), dp as F.DProg (G, dPool)) =
      let
	(* is this EVar redundant? -fp *)
        (* I will assume so.  -kw
           val X = I.newEvar (G, I.EClo(A, s)) *)
        val S = rSolve (rsol, ps, (r, I.Dot (I.Undef, s)), dp)
        val M = solve (sol, (g, s), dp)
      in
        I.App (M, S)
      end
    | rSolve (C.ExistsSol(rsol), ps, (C.Exists(I.Dec(_,A), r), s), dp as F.DProg (G, dPool)) =
      let
        val X = I.newEVar (G, I.EClo(A, s))
      in
        I.App (X, rSolve (rsol, ps, (r, I.Dot (I.Exp(X), s)), dp))
      end
    | rSolve _ = raise BadSolution ""

  and matchAtom (C.DynAtom(k, rsol), ps, dp as F.DProg (G, dPool)) =
      (case I.ctxLookup (dPool, k)
            handle _ => raise BadSolution ""
         of SOME(r, s, _) => I.Root (I.BVar(k), rSolve (rsol, ps, (r, I.comp(s, I.Shift(k))), dp))
          | NONE => raise BadSolution "")
    | matchAtom (C.SigAtom(c, rsol), ps, dp) =
      (case F.sProgLookup c
         of F.SClause(r) => I.Root (I.Const(c), rSolve (rsol, ps, (r, I.id), dp))
          | F.Void => raise BadSolution "")
    | matchAtom (C.ConstrSol(k), (I.Root(I.Const(a), S), s), F.DProg (G, _)) =
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

  exception BadSolution of string

  fun elaborate(sol, q) =
        qSolve(sol, (q, I.id), F.DProg (I.Null, I.Null))
(*         handle e as BadSolution _ => raise e
              | _ => raise BadSolution "Unable to determine cause: invariants violated\n")
        handle BadSolution s => (print s; raise BadSolution s)*)

end
