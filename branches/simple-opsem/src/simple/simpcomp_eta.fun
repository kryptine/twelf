(* Compile regular goal into simple goal *)
(* Author: Kevin Watkins *)

functor SimpCompEta (structure Global : GLOBAL
                  structure IntSyn : INTSYN
                  structure Whnf : WHNF
                    sharing Whnf.IntSyn = IntSyn
                  structure Abstract : ABSTRACT
                    sharing Abstract.IntSyn = IntSyn
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

  fun headType (G, I.BVar(k)) =
      let
        val I.Dec(_, V) = I.ctxDec(G, k)
      in
        V
      end
    | headType (G, I.Const(c)) = I.constType(c)
    | headType (G, I.Skonst(c)) = I.constType(c)
    | headType (G, I.Def(d)) = I.constType(d)
    | headType (G, I.NSDef(d)) = I.constType(d)

  fun abstract (U, 0) = U
    | abstract (U, n) = abstract (S.Lam(U), n-1)

  fun translHead (I.BVar(k), k') = S.BVar(k+k')
    | translHead (I.Const(c), _) = S.Const(c)
    | translHead (I.Skonst(c), _) = S.Skonst(c)
    | translHead (I.Def(d), _) = S.Def(d)
    | translHead (I.NSDef(d), _) = S.NSDef(d)

  fun translExp (G, I.Root(C, S)) =
      let
        val (G', S', k) = translSpine (G, S, Whnf.normalize(headType(G, C), I.id))
      in
        abstract(S.Root(translHead(C, k), S'), k)
      end
    | translExp (G, I.Lam(D, U)) = S.Lam(translExp (I.Decl(G, D), U))

  and translExp' (G, Us) = translExp (G, Whnf.normalize Us)
  and translExp1 (G, U) = translExp(G, Whnf.normalize(U, I.id))

  (* etaTail (G, V, n) = (G', S, k)

     Invariants:
     If G |- V : L  and  V in nf
     then G' |~ S : V[^|S|] > a  and  k = n + |S|  and  a is atomic
  *)
  and etaTail (G, I.Pi((D, _), V), n) =
      let
        val (G', S, k) = etaTail (I.Decl(G, D), V, n+1)
      in
        (G', S.App(translExp (G', I.Root(I.BVar(k-n), I.Nil)), S), k)
      end
    | etaTail (G, _, n) = (G, S.Nil, n)

  and translSpine (G, I.Nil, V) = etaTail(G, V, 0)
    | translSpine (G, I.App(U, S), I.Pi(_, V)) =
      let
        val (G', S', k) = translSpine (G, S, V)
      in
        (G', S.App(translExp1 (G', I.EClo(U, I.Shift(k))), S'), k)
      end
    | translSpine (G, I.App _, I.Redex _) = raise Fail "Redex"
    | translSpine (G, I.App _, I.EVar _) = raise Fail "EVar"
    | translSpine (G, I.App _, I.EClo _) = raise Fail "EClo"
    | translSpine (G, I.App _, V) = raise Fail ("Type error: " ^ Print.expToString(G, V))
  
  fun translStatus (I.Normal) = S.Normal

  fun translConDec (I.ConDec(name, i, status, _, _)) =
        S.ConDec(name, i, translStatus(status))
    | translConDec (I.ConDef(name, i, U, _, _)) =
        S.ConDef(name, i, translExp1 (I.Null, U))
    | translConDec (I.AbbrevDef(name, i, U, _, _)) =
        S.AbbrevDef(name, i, translExp1 (I.Null, U))
    | translConDec (I.SkoDec(name, i, _, _)) =
        S.SkoDec(name, i)

  fun occursInExp (k, U) =
      (case Abstract.occursInExp (k, Whnf.normalize (U, I.id))
         of I.No => false
          | _ => true)

  fun occursInResGoal (k, C.True) = false
    | occursInResGoal (k, C.Eq (U)) = occursInExp (k, U)
    | occursInResGoal (k, C.And (r, A, g)) =
        occursInResGoal (k+1, r) orelse occursInExp (k, A)
    | occursInResGoal (k, C.In (r, A, g)) =
        occursInResGoal (k+1, r) orelse occursInExp (k, A)
    | occursInResGoal (k, C.Exists (I.Dec (_, V), r)) =
        occursInResGoal (k+1, r) orelse occursInExp (k, V)

  fun translGoal (G, (C.Atom (U), s)) = S.Atom (translExp' (G, (U, s)))
    | translGoal (G, (C.Impl (r, A, a, g), s)) =
        (* perhaps the definition of C.Impl should be changed so that
           instead of a type A we have a Dec D? -kw *)
        S.Impl (translResGoal (G, (r, s)), a,
                translGoal (I.Decl (G, I.Dec (NONE, A)), (g, I.dot1 s)))
    | translGoal (G, (C.All(D, g), s)) =
        S.All (translGoal (I.Decl (G, D), (g, I.dot1 s)))

  and translResGoal (G, (C.True, s)) = S.True
    | translResGoal (G, (C.Eq (U), s)) = S.Eq (translExp' (G, (U, s)))
    | translResGoal (G, (C.And (r, A, g), s)) =
        (* Assume And is never dependent *)
        (* perhaps the definition of C.And should be changed so that
           instead of a type A we have a Dec D? -kw *)
        S.And(translResGoal(G, (r, I.Dot (I.Undef, s))),
              translGoal(G, (g, s)))
    | translResGoal (G, (C.In(r, A, g), s)) =
        if occursInResGoal (1, r)
          then S.ExistsMeta (I.abstractions (Whnf.normalize (A, s)),
                             translResGoal (I.Decl (G, I.Dec (NONE, A)), (r, I.dot1 s)))
        else S.AndMeta (translResGoal (G, (r, I.Dot (I.Undef, s))),
                        translGoal (G, (g, s)))
    | translResGoal (G, (C.Exists(D as I.Dec(_, V), r), s)) =
        S.Exists (I.abstractions (Whnf.normalize (V, s)),
                  translResGoal (I.Decl (G, D), (r, I.dot1 s)))

  and translQuery (G, C.QueryGoal(g)) = S.QueryGoal(translGoal(G, (g, I.id)))
      (* must lower free variables of the query *)
    | translQuery (G, C.QueryVar(_, D as I.Dec(_, V), q)) =
      let
        val n = I.abstractions(Whnf.normalize(V, I.id))
      in
        S.QueryVar(abstract (S.newEVar(), n),
                   translQuery (I.Decl(G, D), q))
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
               I.Decl (dp2, SOME (translResGoal (G, (r, I.id)), S.id, a)))
            end
        val (dp1, dp2) = compileCtx' (G)
      in
        (C.DProg(G, dp1), dp2)
      end

  fun installResGoal (c, r) =
      (FullComp.installResGoal (c, r);
       sProgInstall (c, SClause(translResGoal(I.Null, (r, I.id)))))
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