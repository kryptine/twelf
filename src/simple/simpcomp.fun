(* Compile regular goal into simple goal *)
(* Author: Kevin Watkins *)

functor SimpComp (structure Global : GLOBAL
                  structure IntSyn : INTSYN
                  structure Whnf : WHNF
                    sharing Whnf.IntSyn = IntSyn
                  structure Print : PRINT
                    sharing Print.IntSyn = IntSyn
                  structure CompSyn : COMPSYN
                    sharing CompSyn.IntSyn = IntSyn
                  structure PTCompile : PTCOMPILE
                    sharing PTCompile.IntSyn = IntSyn
                    sharing PTCompile.CompSyn = CompSyn
                  structure FullComp : FULLCOMP
                    sharing FullComp.IntSyn = IntSyn
                    sharing FullComp.CompSyn = CompSyn
                  structure SimpSyn : SIMPSYN
                    sharing SimpSyn.IntSyn = IntSyn) : SIMPCOMP =
struct

  structure IntSyn = IntSyn
  structure CompSyn = CompSyn
  structure SimpSyn = SimpSyn

  structure I = IntSyn
  structure C = CompSyn
  structure S = SimpSyn

  (* Dynamic programs: clause pool *)
  (* In the simple compiler there is no context because types
     are unnecessary. *)
  type DProg = CompSyn.DProg * ((SimpSyn.ResGoal * SimpSyn.Sub * IntSyn.cid) option) IntSyn.Ctx

  datatype ConDec =			(* Compiled constant declaration *)
    SClause of SimpSyn.ResGoal          (* c : A                      *)
  | Void 		                (* Other declarations are ignored  *)

  local
    val maxCid = Global.maxCid
    val sProgArray = Array.array (maxCid+1, Void) : ConDec Array.array
  in
    fun sProgInstall (cid, dec) = Array.update (sProgArray, cid, dec)
    fun sProgLookup (cid) = Array.sub (sProgArray, cid)
    fun sProgReset () = Array.modify (fn _ => Void) sProgArray
  end

  fun translHead (I.BVar(k)) = S.BVar(k)
    | translHead (I.Const(c)) = S.Const(c)
    | translHead (I.Skonst(c)) = S.Skonst(c)
    | translHead (I.Def(d)) = S.Def(d)
    | translHead (I.NSDef(d)) = S.NSDef(d)

  fun translExp (I.Root(C, S)) = S.Root(translHead(C), translSpine(S))
    | translExp (I.Lam(_, U)) = S.Lam(translExp(U))

  and translSpine (I.Nil) = S.Nil
    | translSpine (I.App(U, S)) = S.App(translExp(U), translSpine(S))

  (*
  and translSub (I.Shift(n)) = S.Shift(n)
    | translSub (I.Dot(Ft, s)) = S.Dot(translFront(Ft), translSub(s))

  and translFront (I.Idx(k)) = S.Idx(k)
    | translFront (I.Exp(U)) = S.Exp(translExp1(U))
    | translFront (I.Undef) = S.Undef
  *)

  and translExp1 (U) = translExp(Whnf.normalize(U, I.id))

  fun translStatus (I.Normal) = S.Normal

  fun translConDec (I.ConDec(name, i, status, _, _)) =
        S.ConDec(name, i, translStatus(status))
    | translConDec (I.ConDef(name, i, U, _, _)) =
        S.ConDef(name, i, translExp1 (U))
    | translConDec (I.AbbrevDef(name, i, U, _, _)) =
        S.AbbrevDef(name, i, translExp1 (U))
    | translConDec (I.SkoDec(name, i, _, _)) =
        S.SkoDec(name, i)

  fun translGoal (C.Atom(U)) = S.Atom(translExp1(U))
    | translGoal (C.Impl(r, _, a, g)) =
        S.Impl(translResGoal(r), a, translGoal(g))
    | translGoal (C.All(_, g)) = S.All(translGoal(g))

  and translResGoal (C.Eq(U)) = S.Eq(translExp1(U))
    | translResGoal (C.And(r, _, g)) =
        S.And(translResGoal(r), translGoal(g))
    | translResGoal (C.In(r, _, g)) =
        S.In(translResGoal(r), translGoal(g))
    | translResGoal (C.Exists(I.Dec(_, V), r)) =
        S.Exists(I.abstractions(V), translResGoal(r))
    | translResGoal (C.True) =
        S.True
        
  and translQuery (C.QueryGoal(g)) = S.QueryGoal(translGoal(g))
      (* must lower free variables of the query *)
    | translQuery (C.QueryVar(_, I.Dec(_, V), q)) =
      let
        val n = I.abstractions(V)
        fun abstract (U, 0) = U
          | abstract (U, n) = abstract (S.Lam(U), n-1)
      in
        S.QueryVar(abstract (S.newEVar(), n), translQuery(q))
      end

  fun compileCtx fromCS (G) =
      let
        fun compileCtx' (I.Null) = (I.Null, I.Null)
          | compileCtx' (I.Decl (G, D as I.Dec (_, A))) =
            let
              val a = I.targetFam A
              val r = PTCompile.compileClause fromCS A
              val (dp1, dp2) = compileCtx' (G)
            in
              (I.Decl (dp1, SOME (r, I.id, a)),
               I.Decl (dp2, SOME (translResGoal (r), S.id, a)))
            end
        val (dp1, dp2) = compileCtx' (G)
      in
        (C.DProg(G, dp1), dp2)
      end

  fun installResGoal (c, r) =
      (FullComp.installResGoal (c, r);
       sProgInstall (c, SClause(translResGoal(r))))
  fun install fromCS c =
      let
        val conDec = I.sgnLookup (c)
      in
        S.sgnInstall (c, translConDec (conDec));
        case PTCompile.compileConDec fromCS conDec
          of SOME(r) => installResGoal (c, r)
           | NONE => ()
      end

  fun reset () = (S.sgnReset (); sProgReset (); FullComp.reset ())

end
