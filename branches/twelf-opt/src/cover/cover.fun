(* Coverage Checking *)
(* Author: Frank Pfenning *)

functor Cover
  (structure Global : GLOBAL
   structure IntSyn' : INTSYN
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn'
   structure Abstract : ABSTRACT
     sharing Abstract.IntSyn = IntSyn'
   structure Unify : UNIFY		(* must be trailing! *)
     sharing Unify.IntSyn = IntSyn'
   structure Constraints : CONSTRAINTS
     sharing Constraints.IntSyn = IntSyn'
   structure ModeSyn' : MODESYN
     sharing ModeSyn'.IntSyn = IntSyn'
   structure Index : INDEX
     sharing Index.IntSyn = IntSyn'
   structure WorldSyn : WORLDSYN
     sharing WorldSyn.IntSyn = IntSyn'
   structure Names : NAMES
     sharing Names.IntSyn = IntSyn'
   structure Paths : PATHS
   structure Print : PRINT
     sharing Print.IntSyn = IntSyn'
   structure TypeCheck : TYPECHECK
     sharing TypeCheck.IntSyn = IntSyn'
   structure CSManager : CS_MANAGER
     sharing CSManager.IntSyn = IntSyn')
  : COVER =
struct
  structure IntSyn = IntSyn'
  structure ModeSyn = ModeSyn'

  exception Error of string

  local
    structure I = IntSyn
    structure M = ModeSyn
    structure W = WorldSyn
    structure P = Paths
    structure F = Print.Formatter

    (*****************)
    (* Strengthening *)
    (*****************)

    (* next section adapted from m2/metasyn.fun *)

    (* weaken (G, a) = w'

       Invariant:
       If   a is a type family
       then G |- w' : G'
       and  forall x:A in G'  A subordinate to a
     *)
    fun weaken (I.Null, a) = I.id
      | weaken (I.Decl (G', D as I.Dec (name, V)), a) =
	let
	  val w' = weaken (G', a)
	in
	  if Subordinate.belowEq (I.targetFam V, a) then I.dot1 w'
	  else I.comp (w', I.shift)
	end
      (* added next case, probably should not arise *)
      (* Sun Dec 16 10:42:05 2001 -fp !!! *)
      (*
      | weaken (I.Decl (G', D as I.BDec _), a) =
	   I.dot1 (weaken (G', a))
      *)

    (* createEVar (G, V) = X[w] where G |- X[w] : V

       Invariant:
       If G |- V : L
       then G |- X[w] : V
    *)
    fun createEVar (G, V) =
        let (* G |- V : L *)
	  val w = weaken (G, I.targetFam V)       (* G  |- w  : G'    *)
	  val iw = Whnf.invert w 	          (* G' |- iw : G     *)
	  val G' = Whnf.strengthen (iw, G)
	  val X' = I.newEVar (G', I.EClo (V, iw)) (* G' |- X' : V[iw] *)
	  val X = I.EClo (X', w)	          (* G  |- X  : V     *)
	in
	  X
	end

    (*************************)
    (* Coverage instructions *)
    (*************************)

    (* Coverage instructions mirror mode spines, but they
       are computed from modes differently for input and output coverage.

       Match  --- call match and generate candidates
       Skip   --- ignore this argument for purposes of coverage checking

       For input coverage, match input (+) and skip ignore ( * ) and output (-).

       For output coverage, skip input (+), and match output (-).
       Ignore arguments ( * ) should be impossible for output coverage
    *)
    datatype CoverInst =
        Match of CoverInst
      | Skip of CoverInst
      | Cnil

    (* inCoverInst (ms) = ci
       converts mode spine ms to cover instructions ci for input coverage
    *)
    fun inCoverInst (M.Mnil) = Cnil
      | inCoverInst (M.Mapp (M.Marg (M.Plus, x), ms')) =
          Match (inCoverInst ms')
      | inCoverInst (M.Mapp (M.Marg (M.Minus, x), ms')) =
	  Skip (inCoverInst ms')
      | inCoverInst (M.Mapp (M.Marg (M.Star, x), ms')) =
	  Skip (inCoverInst ms')

    (* outCoverInst (ms) = ci
       converts mode spine ms to cover instructions ci for output coverage
    *)
    fun outCoverInst (M.Mnil) = Cnil
      | outCoverInst (M.Mapp (M.Marg (M.Plus, x), ms')) =
          Skip (outCoverInst ms')
      | outCoverInst (M.Mapp (M.Marg (M.Minus, x), ms')) =
	  Match (outCoverInst ms')
      (* this last case should be impossible *)
      (* output coverage only from totality checking, where there can be *)
      (* no undirectional ( * ) arguments *)
      (*
      | outCoverInst (M.Mapp (M.Marg (M.Star, x), ms')) =
	  Skip (outCoverInst ms')
      *)

    (*
       Coverage goals have the form {{G}} {{L}} a @ S
       where G are splittable variables
       and L are local parameters (not splittable)
    *)
    (**********************************************)
    (* Creating the initial input coverage goal ***)
    (**********************************************)

    (* buildSpine n = n; n-1; ...; 1; Nil *)

    fun buildSpine 0 = I.Nil
      | buildSpine n = (* n > 0 *)
        I.App (I.Root (I.BVar(n), I.Nil), buildSpine (n-1))

    (* initCGoal' (a, 0, ., V) = ({x1:V1}...{xn:Vn} a x1...xn, n)
       for |- a : V and V = {x1:V1}...{xn:Vn} type

       Invariants for initCGoal' (a, k, G, V):
       G = {x1:V1}...{xk:Vk}
       V = {xk+1:Vk+1}...{xn:Vn} type 
       G |- V : type
    *)
    fun initCGoal' (a, k, G, I.Pi ((D, P), V)) =
        let
	  val D' = Names.decEName (G, D)
	  val (V', p) = initCGoal' (a, k+1, I.Decl(G, D'), V)
	in
          (I.Pi ((D', I.Maybe), V'), p)
	end
      | initCGoal' (a, k, G, I.Uni (I.Type)) =
          (I.Root (a, buildSpine k), k)

    (* initCGoal (a) = {x1:V1}...{xn:Vn} a x1...xn
       where a : {x1:V1}...{xn:Vn} type
    *)
    fun initCGoal (a) = initCGoal' (I.Const (a), 0, I.Null, I.constType (a))

    (****************)
    (*** Matching ***)
    (****************)

    datatype CoverClauses =
        Input of I.Exp list
      | Output of I.Exp * int (* for now, no factoring --- singleton list *)

    (* Equation G |- (U1,s1) = (U2,s2)
       Invariant: 
       G |- U1[s1] : V
       G |- U2[s2] : V  for some V

       U1[s1] has no EVars (part of coverage goal)
    *)
    datatype Equation = Eqn of I.dctx * I.eclo * I.eclo

    (* Splitting candidates *)
    (* Splitting candidates [k1,...,kl] are indices
       into coverage goal {xn:Vn}...{x1:V1} a M1...Mm, counting right-to-left
    *)
    datatype Candidates =
        Eqns of Equation list		(* equations to be solved, everything matches so far *)
      | Cands of int list		(* candidates for splitting, matching fails *)
      | Fail				(* coverage fails without candidates *)

    (* fail () = Fail
       indicate failure without splitting candidates
     *)
    fun fail () = Fail

    (* failAdd (k, cands) = cands'
       indicate failure, but add k as splitting candidate
    *)
    fun failAdd (k, Eqns _) = Cands (k::nil) (* no longer matches *)
      | failAdd (k, Cands (ks)) = Cands (k::ks) (* remove duplicates? *)
      | failAdd (k, Fail) = Fail

    (* addEqn (e, cands) = cands'
       indicate possible match if equation e can be solved
    *)
    fun addEqn (e, Eqns (es)) = Eqns (e::es) (* still may match: add equation *)
      | addEqn (e, cands as Cands (ks)) = (* already failed: ignore new constraints *)
          cands
      | addEqn (e, Fail) = Fail		(* already failed without candidates *)

    (* matchEqns (es) = true 
       iff  all equations in es can be simultaneously unified

       Effect: instantiate EVars right-hand sides of equations.
    *)
    fun matchEqns (nil) = true
      | matchEqns (Eqn (G, Us1, Us2)::es) =
        Unify.unifiable (G, Us1, Us2)
	andalso matchEqns (es)

    (* resolveCands (cands) = cands'
       resolve to one of
	 Eqns(nil) - match successful
	 Fail      - no match, no candidates
	 Cands(ks) - candidates ks
       Effect: instantiate EVars in right-hand sides of equations.
    *)
    fun resolveCands (Eqns (es)) =
        (* reversed equations Fri Dec 28 09:39:55 2001 -fp !!! *)
        (* why is this important? --cs !!! *)
        if matchEqns (List.rev es) then (Eqns (nil))
	else Fail
      | resolveCands (Cands (ks)) = Cands (ks)
      | resolveCands (Fail) = Fail

    (* collectConstraints (Xs) = constrs
       collect all the constraints that may be attached to EVars Xs

       try simplifying away the constraints in case they are "hard"
       disabled for now to get a truer approximation to operational semantics
    *)
    fun collectConstraints (nil) = nil
      | collectConstraints (I.EVar (_, _, _, ref nil)::Xs) =
          collectConstraints Xs
      | collectConstraints (I.EVar (_, _, _, ref constrs)::Xs) =
	  (* constrs <> nil *)
          (* Constraints.simplify constrs @ *) (* at present, do not simplify -fp *)
	  constrs @ collectConstraints Xs

    (* checkConstraints (cands, (Q, s)) = cands'
       failure if constraints remain in Q[s] which indicates only partial match
       Q[s] is the clause head after matching the coverage goal.

       Invariants: if cands = Eqns (es) then es = nil.
    *)
    (* This ignores LVars, because collectEVars does *)
    (* Why is that OK?  Sun Dec 16 09:01:40 2001 -fp !!! *)
    fun checkConstraints (G, Qs, Cands (ks)) = Cands (ks)
      | checkConstraints (G, Qs, Fail) = Fail
      | checkConstraints (G, Qs, Eqns _) = (* _ = nil *)
        let
	  val Xs = Abstract.collectEVars (G, Qs, nil)
	  val constrs = collectConstraints Xs
	in
	  case constrs
	    of nil => Eqns (nil)
	     | _ => Fail		(* constraints remained: Fail without candidates *)
	end

    (* Candidate Lists *)
    (*
       Candidate lists record constructors and candidates for each
       constructors or indicate that the coverage goal is matched.
    *)
    datatype CandList =
        Covered				(* covered---no candidates *)
      | CandList of Candidates list     (* cands1,..., candsn *)

    (* addKs (cands, klist) = klist'
       add new constructor to candidate list
    *)
    fun addKs (ccs as Cands(ks), CandList (klist)) = CandList (ccs::klist)
      | addKs (ces as Eqns(nil), CandList (klist)) = Covered
      | addKs (cfl as Fail, CandList (klist)) = CandList (cfl::klist)

    (* matchExp (G, d, (U1, s1), (U2, s2), cands) = cands'
       matches U1[s1] (part of coverage goal)
       against U2[s2] (part of clause head)
       adds new candidates to cands to return cands'
         this could collapse to Fail,
         postponed equations Eqns(es),
         or candidates Cands(ks)
       d is depth, k <= d means local variable, k > d means coverage variable

       Invariants:
       G |- U1[s1] : V
       G |- U2[s2] : V  for some V
       G = Gc, Gl where d = |Gl|
    *)
    fun matchExp (G, d, Us1, Us2, cands) =
        matchExpW (G, d, Whnf.whnf Us1, Whnf.whnf Us2, cands)

    and matchExpW (G, d, Us1 as (I.Root (H1, S1), s1), Us2 as (I.Root (H2, S2), s2), cands) =
        (case (H1, H2)
	   (* Note: I.Proj occurring here will always have the form
	      I.Proj (I.Bidx (k), i) *)
	   (* No skolem constants, foreign constants, FVars *)
	   of (I.BVar (k1), I.BVar(k2)) =>
	      if (k1 = k2)
		then matchSpine (G, d, (S1, s1), (S2, s2), cands)
	      else if k1 > d
		     then failAdd (k1-d, cands) (* k1 is coverage variable, new candidate *)
		   else fail ()		(* otherwise fail with no candidates *)
	    | (I.Const(c1), I.Const(c2)) =>
	      if (c1 = c2) then matchSpine (G, d, (S1, s1), (S2, s2), cands)
	      else fail ()		(* fail with no candidates *)
            | (I.Def (d1), I.Def (d2)) =>
	      if (d1 = d2)		(* because of strictness *)
		then matchSpine (G, d, (S1, s1), (S2, s2), cands)
	      else matchExpW (G, d, Whnf.expandDef Us1, Whnf.expandDef Us2, cands)
	    | (I.Def (d1), _) => matchExpW (G, d, Whnf.expandDef Us1, Us2, cands)
	    | (_, I.Def (d2)) => matchExpW (G, d, Us1, Whnf.expandDef Us2, cands)
	    | (I.BVar (k1), I.Const _) =>
	      if k1 > d
		then failAdd (k1-d, cands) (* k1 is coverage variable, new candidate *)
	      else fail ()		(* otherwise fail with no candidates *)
	    | (I.Const _, I.BVar _) => fail ()
	    | (I.Proj (I.Bidx (k), i), I.Proj (I.Bidx (k'), i')) =>
		if (k = k') andalso (i = i')
		  then matchSpine (G, d, (S1, s1), (S2, s2), cands)
		else fail ()		(* fail with no candidates *)
            | (I.BVar (k1), I.Proj _) =>
	      if k1 > d
		then failAdd (k1-d, cands) (* k1 is splittable, new candidate *)
	      else fail ()		(* otherwise fail with no candidates *)
	    | (I.Const _, I.Proj _) => fail ()
            | (I.Proj _, I.Const _) => fail ()
            | (I.Proj _, I.BVar _) => fail ()
            (* no other cases should be possible *)
	    )
      | matchExpW (G, d, (I.Lam (D1, U1), s1), (I.Lam (D2, U2), s2), cands) =
	   matchExp (I.Decl (G, I.decSub (D1, s1)), d+1, (U1, I.dot1 s1), (U2, I.dot1 s2), cands)
      | matchExpW (G, d, (I.Lam (D1, U1), s1), (U2, s2), cands) =
	   (* eta-expand *)
	   matchExp (I.Decl (G, I.decSub (D1, s1)), d+1,
		     (U1, I.dot1 s1),
		     (I.Redex (I.EClo (U2, I.shift),
			       I.App (I.Root (I.BVar (1), I.Nil), I.Nil)),
		      I.dot1 s2),
		     cands)
      | matchExpW (G, d, (U1, s1), (I.Lam (D2, U2), s2), cands) =
	   (* eta-expand *)
	   matchExp (I.Decl (G, I.decSub (D2, s2)), d+1,
		     (I.Redex (I.EClo (U1, I.shift),
			       I.App (I.Root (I.BVar (1), I.Nil), I.Nil)),
		      I.dot1 s1),
		     (U2, I.dot1 s2),
		     cands)
      | matchExpW (G, d, Us1, Us2 as (I.EVar _, s2), cands) =
	   addEqn (Eqn (G, Us1, Us2), cands)
      (* next 3 cases are only for output coverage *)
      (* not needed since we skip input arguments for output coverage *)
      (* see comments on CoverInst -fp Fri Dec 21 20:58:55 2001 !!! *)
      (*
      | matchExpW (G, d, (I.Pi ((D1, _), V1), s1), (I.Pi ((D2, _), V2), s2), cands) =
	let 
	  val cands' = matchDec (G, d, (D1, s1), (D2, s2), cands)
	in
	  matchExp (I.Decl (G, D1), d+1, (V1, I.dot1 s1), (V2, I.dot1 s2), cands')
	end 
      | matchExpW (G, d, (I.Pi _, _), _, cands) = fail ()
      | matchExpW (G, d, _, (I.Pi _, _), cands) = fail ()
      *)
      (* nothing else should be possible, by invariants *)
      (* No I.Uni, I.FgnExp, and no I.Redex by whnf *)

    and matchSpine (G, d, (I.Nil, _), (I.Nil, _), cands) = cands
      | matchSpine (G, d, (I.SClo (S1, s1'), s1), Ss2, cands) =
          matchSpine (G, d, (S1, I.comp (s1', s1)), Ss2, cands)
      | matchSpine (G, d, Ss1, (I.SClo (S2, s2'), s2), cands) =
	  matchSpine (G, d, Ss1, (S2, I.comp (s2', s2)), cands)
      | matchSpine (G, d, (I.App (U1, S1), s1), (I.App (U2, S2), s2), cands) =
	let
	  val cands' = matchExp (G, d, (U1, s1), (U2, s2), cands)
	in
	  matchSpine (G, d, (S1, s1), (S2, s2), cands')
	end

    and matchDec (G, d, (I.Dec (_, V1), s1), (I.Dec (_, V2), s2), cands) =
          matchExp (G, d, (V1, s1), (V2, s2), cands)
        (* BDec should be impossible here *)

    (* matchTop (G, (a @ S1, s1), (a @ S2, s2), ci) = cands
       matches S1[s1] (spine of coverage goal)
       against S2[s2] (spine of clause head)
       skipping over `skip' arguments in cover instructions

       Invariants:
       G |- a @ S1[s1] : type
       G |- a @ S2[s2] : type
       G contains coverage variables,
       S1[s1] contains no EVars
       cover instructions ci matche S1 and S2
    *)
    fun matchTop (G, d, Us1, Us2, ci, cands) =
          matchTopW (G, d, Whnf.whnf Us1, Whnf.whnf Us2, ci, cands)
    and matchTopW (G, d, (I.Root (I.Const (c1), S1), s1),
                         (I.Root (I.Const (c2), S2), s2), ci, cands) =
        if (c1 = c2)
	  then
	    (* unify spines, skipping output and ignore arguments in modeSpine *)
	    matchTopSpine (G, d, (S1, s1), (S2, s2), ci, cands)
	else fail () (* fails, with no candidates since type families don't match *)
      | matchTopW (G, d, (I.Pi ((D1,_), V1), s1),
		         (I.Pi ((D2,_), V2), s2), ci, cands) = 
	(* this case can only arise in output coverage *)
	(* we do not match D1 and D2, since D1 is always an instance of D2 *)
	(* and no splittable variables should be suggested here *)
	(* Sat Dec 22 23:53:44 2001 -fp !!! *)
	  matchTopW (I.Decl (G, D1), d+1, (V1, I.dot1 s1), (V2, I.dot1 s2), ci, cands)
    and matchTopSpine (G, d, (I.Nil, _), (I.Nil, _), Cnil, cands) = cands
      | matchTopSpine (G, d, (I.SClo (S1, s1'), s1), Ss2, ci, cands) =
          matchTopSpine (G, d, (S1, I.comp (s1', s1)), Ss2, ci, cands)
      | matchTopSpine (G, d, Ss1, (I.SClo (S2, s2'), s2), ci, cands) =
          matchTopSpine (G, d, Ss1, (S2, I.comp (s2', s2)), ci, cands)
      | matchTopSpine (G, d, (I.App (U1, S1), s1), (I.App (U2, S2), s2),
		       Match (ci'), cands) =
        (* an argument that must be covered (Match) *)
        let
	  val cands' = matchExp (G, d, (U1, s1), (U2, s2), cands)
	in
	   matchTopSpine (G, d, (S1, s1), (S2, s2), ci', cands')
	end
      | matchTopSpine (G, d, (I.App (U1, S1), s1), (I.App (U2, S2), s2),
		       Skip (ci'), cands) =
	(* an argument that need not be covered (Skip) *)
	   matchTopSpine (G, d, (S1, s1), (S2, s2), ci', cands)

    (* matchClause (G, (a @ S1, s1), V, ci) = cands
       as in matchTop, but r is clause
       NOTE: Simply use constant type for more robustness (see below)
    *)
    fun matchClause (G, ps', qs as (I.Root (_, _), s), ci) =
          checkConstraints (G, qs, resolveCands (matchTop (G, 0, ps', qs, ci, Eqns (nil))))
      | matchClause (G, ps', (I.Pi ((I.Dec(_, V1), _), V2), s), ci) =
        let
	  (* changed to use subordination and strengthening here *)
	  (* Sun Dec 16 10:39:34 2001 -fp *)
	  (* val X1 = createEVar (G, I.EClo (V1, s)) *)
	  (* changed back --- no effect *)
	  val X1 = I.newEVar (G, I.EClo (V1, s))
	  (* was: I.Null instead of G in line above Wed Nov 21 16:40:40 2001 *)
	in
	  matchClause (G, ps', (V2, I.Dot (I.Exp (X1), s)), ci)
	end

    (* matchSig (G, (a @ S, s), ccs, ci, klist) = klist'
       match coverage goal {{G}} a @ S[s]
       against each coverage clause V in ccs,
       adding one new list cand for each V to klist to obtain klist'

       Invariants:
       G |- a @ S[s] : type
       V consists of clauses with target type a @ S'
       ci matches S
       klist <> Covered
    *)
    fun matchSig (G, ps', nil, ci, klist) = klist
      | matchSig (G, ps', V::ccs', ci, klist) =
        let
	  val cands = CSManager.trail
	              (fn () => matchClause (G, ps', (V, I.id), ci))
	in
	  matchSig' (G, ps', ccs', ci, addKs (cands, klist))
	end

    (* matchSig' (G, (a @ S, s), ccs, ci, klist) = klist'
       as matchSig, but check if coverage goal {{G}} a @ S[s] is already matched
    *)
    and matchSig' (G, ps', ccs, ci, Covered) = Covered (* already covered: return *)
      | matchSig' (G, ps', ccs, ci, CandList (klist)) = (* not yet covered: continue to search *)
          matchSig (G, ps', ccs, ci, CandList (klist))

    (* matchBlocks (G, s', piDecs, V, k, i, ci, klist) = klist'
       Invariants:
       G |- s' : Gsome
       Gsome |- piDecs : ctx
       G |- V : type
       G_k = (Gsome, D1...D(i-1) piDecs)
     *)
    fun matchBlocks (G, s', nil, V, k, i, ci, klist) = klist
      | matchBlocks (G, s', I.Dec (_, V')::piDecs, V, k, i, ci, klist) =
        let
	  val cands = CSManager.trail
	              (fn () => matchClause (G, (V, I.id), (V', s'), ci))
	  val s'' = I.Dot (I.Exp (I.Root (I.Proj (I.Bidx k, i), I.Nil)), s')
	in
	  matchBlocks' (G, s'', piDecs, V, k, i+1, ci, addKs (cands, klist))
	end
    and matchBlocks' (G, s', piDecs, V, k, i, ci, Covered) = Covered
      | matchBlocks' (G, s', piDecs, V, k, i, ci, klist) = 
          matchBlocks (G, s', piDecs, V, k, i, ci, klist) (* klist <> Covered *)

    (* matchCtx (G, s', G', V, k, ci, klist) = klist'
       Invariants:
       G |- s' : G'
       G |- V : type
       s' o ^ = ^k
       ci matches for for V = a @ S
       klist <> Covered accumulates mode spines
    *)
    fun matchCtx (G, s', I.Null, V, k, ci, klist) = klist
      | matchCtx (G, s', I.Decl(G'', I.Dec(_, V')), V, k, ci, klist) =
        (* will always fail for input coverage *)
        let
	  (*  G'', V' |- ^ : G''
	      G |- s' : G'', V'  
          *)    
	  val s'' = I.comp (I.shift, s')
	  (*  G |- ^ o s' : G'' *)
	  val cands = CSManager.trail
	              (fn () => matchClause (G, (V, I.id), (V', s''), ci))
	in
	  matchCtx' (G, s'', G'', V, k+1, ci, addKs (cands, klist))
	end
      | matchCtx (G, s', I.Decl(G'', I.BDec(_, (cid, s))), V, k, ci, klist) =
        let
	  val (Gsome, piDecs) = I.constBlock cid	
	  val s'' = I.comp (I.shift, s')
	  (* G'' |- s : Gsome,
             G |- s'' : G''
             G |- s o s'' : Gsome
             Gsome |- piDecs : ctx
          *)
	  val klist' = matchBlocks (G, I.comp (s, s''), piDecs, V, k, 1, ci, klist)
	in
	  matchCtx' (G, s'', G'', V, k+1, ci, klist')
	end

    and matchCtx' (G, s', G', V, k, ci, Covered) = Covered
      | matchCtx' (G, s', G', V, k, ci, CandList (klist)) =
          matchCtx (G, s', G', V, k, ci, CandList (klist))

    (* as matchClause *)
    fun matchOut (G, V, ci, (V', s'), 0) =
        let
	  val cands = matchTop (G, 0, (V, I.id), (V', s'), ci, Eqns(nil))
	  val cands' = resolveCands (cands)
	  val cands'' = checkConstraints (G, (V', s'), cands')
	in
	  addKs (cands'', CandList (nil))
	end
      | matchOut (G, V, ci, (V' as I.Pi ((I.Dec(_, V1'), _), V2'), s'), p) = (* p > 0 *)
	let
	  val X1 = I.newEVar (G, I.EClo (V1', s'))
	in
	  matchOut (G, V, ci, (V2', I.Dot (I.Exp (X1), s')), p-1)
	end

    (* match (., V, p, ci, I/O(ccs)) = klist
       matching coverage goal {{G}} V against coverage clauses Vi in ccs
       yields candidates klist
       no local assumptions
       Invariants:
       V = {{G}} {{L}} a @ S where |G| = p
       cover instructions ci match S
       G |- V : type
    *)
    fun match (G, V as I.Root (I.Const (a), S), 0, ci, Input(ccs)) =
          matchCtx' (G, I.id, G, V, 1, ci,
		     matchSig (G, (V, I.id), ccs, ci, CandList (nil)))
      | match (G, V, 0, ci, Output (V', q)) =
	  matchOut (G, V, ci, (V', I.Shift (I.ctxLength G)), q)
      | match (G, I.Pi ((D, _), V'), p, ci, ccs) =
	  match (I.Decl (G, D), V', p-1, ci, ccs)

    (************************************)
    (*** Selecting Splitting Variable ***)
    (************************************)

    (* insert (k, ksn) = ksn'
       ksn is ordered list of ks (smallest index first) with multiplicities
    *)
    fun insert (k, nil) = ((k, 1)::nil)
      | insert (k, ksn as (k', n')::ksn') =
        (case Int.compare (k, k')
	   of LESS => (k, 1)::ksn
	    | EQUAL => (k', n'+1)::ksn'
	    | GREATER => (k', n')::insert (k, ksn'))

    (* join (ks, ksn) = ksn'
       ksn is as in function insert
    *)
    fun join (nil, ksn) = ksn
      | join (k::ks, ksn) = join (ks, insert (k, ksn))

    (* selectCand (klist) = ksnOpt
       where ksOpt is an indication of coverage (NONE)
       or a list of candidates with multiplicities

       Simple heuristic: select last splitting candidate from last clause tried
       This will never pick an index variable unless necessary.
    *)
    fun selectCand (Covered) = NONE	(* success: case is covered! *)
      | selectCand (CandList (klist)) = selectCand' (klist, nil)

    and selectCand' (nil, ksn) = SOME(ksn) (* failure: case G,V is not covered! *)
      | selectCand' (Fail::klist, ksn) = (* local failure (clash) and no candidates *)
          selectCand' (klist, ksn)
      | selectCand' (Cands(nil)::klist, ksn) = (* local failure but no candidates *)
	  selectCand' (klist, ksn)
      | selectCand' (Cands(ks)::klist, ksn) = (* found candidates ks <> nil *)
	  selectCand' (klist, join (ks, ksn))

    (*****************)
    (*** Splitting ***)
    (*****************)

    (* In a coverage goal {{G}} {{L}} a @ S we instantiate each
       declaration in G with a new EVar, then split one of these variables,
       then abstract to obtain a new coverage goal {{G'}} {{L'}} a @ S'
    *)

    (* instEVars ({x1:V1}...{xp:Vp} V, p, nil) = (V[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars
    *)       
    fun instEVars (Vs, p, XsRev) = instEVarsW (Whnf.whnf Vs, p, XsRev)
    and instEVarsW (Vs, 0, XsRev) = (Vs, XsRev)
      | instEVarsW ((I.Pi ((I.Dec (xOpt, V1), _), V2), s), p, XsRev) =
        let (* p > 0 *)
	  val X1 = I.newEVar (I.Null, I.EClo (V1, s)) (* all EVars are global *)
	in
	  instEVars ((V2, I.Dot (I.Exp (X1), s)), p-1, SOME(X1)::XsRev)
	end
      | instEVarsW ((I.Pi ((I.BDec (_, (l, t)), _), V2), s), p, XsRev) =
        (* G0 |- t : Gsome *)
	(* . |- s : G0 *)
	let (* p > 0 *)
	  val L1 = I.newLVar (l, I.comp(t, s))
	in
	  instEVars ((V2, I.Dot (I.Block (L1), s)), p-1, NONE::XsRev)
	end
    
    (* caseList is a list of possibilities for a variables
       to be split.  Maintained as a mutable reference so it
       can be updated in the success continuation.
    *)
    local 
      val caseList : (I.Exp * int) list ref = ref nil
    in
      fun resetCases () = (caseList := nil)
      fun addCase (V, p) = (caseList := (V,p) :: !caseList)
      fun getCases () = (!caseList)
    end

    (* createEVarSpine (G, (V, s)) = (S', (V', s'))

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic  
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [s']
       and  G |- S : V [s] >  V' [s']
    *)
    (* changed to use createEVar? *)
    (* Sun Dec 16 10:36:59 2001 -fp *)
    fun createEVarSpine (G, Vs) = createEVarSpineW (G, Whnf.whnf Vs)
    and createEVarSpineW (G, Vs as (I.Root _, s)) = (I.Nil, Vs)   (* s = id *)
      | createEVarSpineW (G, (I.Pi ((D as I.Dec (_, V1), _), V2), s)) =  
	let (* G |- V1[s] : L *)
	  val X = createEVar (G, I.EClo (V1, s))
	  val (S, Vs) = createEVarSpine (G, (V2, I.Dot (I.Exp (X), s)))
	in
	  (I.App (X, S), Vs)
	end
      (* Uni or other cases should be impossible *)

    (* createAtomConst (G, c) = (U', (V', s'))

       Invariant: 
       If   S |- c : Pi {V1 .. Vn}. V 
       then . |- U' = c @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomConst (G, H as I.Const (cid)) = 
        let
	  val V = I.constType cid
	  val (S, Vs) = createEVarSpine (G, (V, I.id))
	in
	  (I.Root (H, S), Vs)
	end
        (* mod: m2/metasyn.fun allows skolem constants *)

    (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant: 
       If   G |- k : Pi {V1 .. Vn}. V 
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomBVar (G, k) =
	let
	  val I.Dec (_, V) = I.ctxDec (G, k)
	  val (S, Vs) = createEVarSpine (G, (V, I.id))
	in
	  (I.Root (I.BVar (k), S), Vs)
	end

    (* end m2/metasyn.fun *)

    (* createAtomProj (G, #i(l), (V, s)) = (U', (V', s'))

       Invariant: 
       If   G |- #i(l) : Pi {V1 .. Vn}. Va
       and  G |- Pi {V1..Vn}. Va = V[s] : type
       then . |- U' = #i(l) @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomProj (G, H, (V, s)) = 
        let
	  val (S, Vs') = createEVarSpine (G, (V, s))
	in
	  (I.Root (H, S), Vs')
	end

    fun constCases (G, Vs, nil, sc) = ()
      | constCases (G, Vs, I.Const(c)::sgn', sc) =
        let
	  val (U, Vs') = createAtomConst (G, I.Const c)
	  val _ = CSManager.trail (fn () =>
				   if Unify.unifiable (G, Vs, Vs')
				     then sc U
				   else ())
	in
	  constCases (G, Vs, sgn', sc)
	end

    fun paramCases (G, Vs, 0, sc) = ()
      | paramCases (G, Vs, k, sc) =
        let
	  val (U, Vs') = createAtomBVar (G, k)
	  val _ = CSManager.trail (fn () =>
				   if Unify.unifiable (G, Vs, Vs')
				     then sc U
				   else ())
	in
	  paramCases (G, Vs, k-1, sc)
	end

    (* createEVarSub G' = s
     
       Invariant:
       If   . |- G' ctx
       then . |- s : G' and s instantiates each x:A with an EVar . |- X : A

       Update: Always use empty context. Sat Dec  8 13:19:58 2001 -fp
    *)
    fun createEVarSub (I.Null) = I.id
      | createEVarSub (I.Decl(G', D as I.Dec (_, V))) =
        let
	  val s = createEVarSub G'
	  val V' = I.EClo (V, s)
	  val X = I.newEVar (I.Null, V')
	in
	  I.Dot (I.Exp X, s)
	end

    (* hack *)
    fun blockName (cid) = I.conDecName (I.sgnLookup (cid))

    (* blockCases (G, Vs, B, (Gsome, piDecs), sc) = 

       If G |- V[s] : type
          . |- Gsome ctx and Gsome |- piDecs decList
       then sc is called for any x:A in piDecs such thtat
            G |- V[s] = A[t] : type
            where t instantiates variable in Gsome with new EVars
    *)
    fun blockCases (G, Vs, cid, (Gsome, piDecs), sc) =
        let
	  val t = createEVarSub Gsome	(* accounts for subordination *)
	  (* . |- t : Gsome *)
	  val lvar = I.newLVar (cid, t)
	  val t' = I.comp (t, I.Shift (I.ctxLength (G)))
	  (* G |- t' : Gsome *)
	in
	  blockCases' (G, Vs, (lvar, 1), (t', piDecs), sc)
	end
    and blockCases' (G, Vs, (lvar, i), (t, nil), sc) = ()
      | blockCases' (G, Vs, (lvar, i), (t, I.Dec (_, V')::piDecs), sc) =
        let
          (* G |- t : G' and G' |- ({_:V'},piDecs) decList *)
          (* so G |- V'[t'] : type *)
	  val (U, Vs') = createAtomProj (G, I.Proj (lvar, i), (V', t))
	  val _ = CSManager.trail (fn () => if Unify.unifiable (G, Vs, Vs')
					      then sc U
					    else ())
	  val t' = I.Dot (I.Exp (I.Root (I.Proj (lvar, i), I.Nil)), t)
	in
          blockCases' (G, Vs, (lvar, i+1), (t', piDecs), sc)
	end

    fun worldCases (G, Vs, W.Worlds (nil), sc) = ()
      | worldCases (G, Vs, W.Worlds (cid::cids), sc) =
          ( blockCases (G, Vs, cid, I.constBlock cid, sc) ;
	    worldCases (G, Vs, W.Worlds (cids), sc) )

    fun lowerSplit (G, Vs, W, sc) = lowerSplitW (G, Whnf.whnf Vs, W, sc)
    and lowerSplitW (G, Vs as (I.Root (I.Const a, _), s), W, sc) =
        let
	  val _ = constCases (G, Vs, Index.lookup a, sc) (* will trail *)
	  val _ = paramCases (G, Vs, I.ctxLength G, sc)	(* will trail *)
	  val _ = worldCases (G, Vs, W, sc) (* will trail *)
	in
	  ()
	end
      | lowerSplitW (G, (I.Pi ((D, P), V), s), W, sc) =
	let
	  val D' = I.decSub (D, s)
	in
	  lowerSplit (I.Decl (G, D'), (V, I.dot1 s), W, fn U => sc (I.Lam (D', U)))
	end

    (* splitEVar (X, W, sc) = ()

       calls sc () for all cases, after instantiation of X
       W are the currently possible worlds
    *)
    fun splitEVar ((X as I.EVar (_, GX, V, _)), W, sc) = (* GX = I.Null *)
          lowerSplit (I.Null, (V, I.id), W,
		      fn U => if Unify.unifiable (I.Null, (X, I.id), (U, I.id))
				then sc ()
			      else ())

    (* abstract (V, s) = V'
       where V' = {{G}} Vs' and G abstracts over all EVars in V[s]
       in arbitrary order respecting dependency

       Invariants: . |- V[s] : type
       Effect: may raise Constraints.Error (constrs)
     *)
    fun abstract (V, s) = 
        let
	  val (i, V') = Abstract.abstractDecImp (I.EClo (V, s))
	  val _ = if !Global.doubleCheck
		    then TypeCheck.typeCheck (I.Null, (V', I.Uni(I.Type)))
		  else ()
	in
	  (V', i)
	end

    (* splitVar ({{G}} V, p, k, W) = SOME [{{G1}} V1 ,..., {{Gn}} Vn]
                                  or NONE
       where {{Gi}} Vi are new coverage goals obtained by
       splitting kth variable in G, counting right-to-left.

       returns NONE if splitting variable k fails because of constraints

       W are the worlds defined for current predicate

       Invariants:
       |G| = p
       k <= |G|
       G |- V : type
       {{Gi}} Vi cover {{G}} V
    *)
    fun splitVar (V, p, k, W) =
        let
	  val ((V1, s), XsRev) = instEVars ((V, I.id), p, nil)
          (* split on k'th variable, counting from innermost *)
	  val SOME(X) = List.nth (XsRev, k-1)
	  val _ = if !Global.chatter >= 6
		    then print ("Split " ^ Print.expToString (I.Null, X) ^ " in "
				^ Print.expToString (I.Null, I.EClo(V1, s)) ^ ".\n")
		  else ()
	  val _ = resetCases ()
	  val _ = splitEVar (X, W, fn () => addCase (abstract (V1, s)))
          (*
	   if !Global.chatter >= 7
           then print ("Case: " ^ Print.expToString (I.Null, X) ^ " where\n"
		        ^ Print.expToString (I.Null, I.EClo(V1,s)) ^ ".\n")
           else ()
	   *)
	in
	  SOME (getCases ())
	end
        (* Constraints.Error could be raised by abstract *)
        handle Constraints.Error (constrs) =>
	  (if !Global.chatter >= 6	
	     then print ("Inactive split:\n" ^ Print.cnstrsToString (constrs) ^ "\n")
	   else ();
	   NONE)

    (**********************)
    (* Finitary Splitting *)
    (**********************)

    (* 
       A splittable variable X : V is called finitary
       if there are finitely many alternatives for V.
       This means there are finitely many (including 0)
       constructors (possibly including local variables) such that
       all free variables in the argument are not recursive
       with the target type of V.

       Splitting such variables can never lead to non-termination.
    *)

    fun targetBelowEq (a, I.EVar (ref(NONE), GY, VY, ref nil)) =
          Subordinate.belowEq (a, I.targetFam VY)
      | targetBelowEq (a, I.EVar (ref(NONE), GY, VY, ref (_::_))) =
	  (* if contraints remain, consider recursive and thereby unsplittable *)
	  true

    (* recursive X = true
       iff the instantiation of X : {{G}} a @ S contains an
           EVar Y : {{G'}} b @ S such that a <|= b

       This means there is no guarantee that X : {{G}} a @ S has only
       a finite number of instances
    *)
    fun recursive (X as I.EVar (ref(SOME(U)), GX, VX, _)) =
        let (* GX = I.Null*)
	    (* is this always true? --cs!!!*)
	  val a = I.targetFam VX
	  val Ys = Abstract.collectEVars (GX, (X, I.id), nil)
	  (* LVars are ignored here.  OK because never splittable? *)
	  (* Sat Dec 15 22:42:10 2001 -fp !!! *)
	  val recp = List.exists (fn Y => targetBelowEq (a, Y)) Ys
	in
	  recp
	end

    local
      val counter = ref 0
    in
      fun resetCount () = (counter := 0)
      fun incCount () = (counter := !counter + 1)
      fun getCount () = !counter
    end

    exception NotFinitary

    (* finitary1 (X, k, W, cands)
        = ((k, n)::cands) if X is finitary with n possibilities
        = cands if X is not finitary
    *)
    fun finitary1 (X as I.EVar(r, I.Null, VX, _), k, W, cands) =
        ( resetCount () ;
	  if !Global.chatter >= 7
	    then print ("Trying " ^ Print.expToString (I.Null, X) ^ " : "
			^ Print.expToString (I.Null, VX) ^ ".\n")
	  else () ;
	  ( splitEVar (X, W, fn () => if recursive X
					then raise NotFinitary
				      else incCount ()) ;
	    if !Global.chatter >= 7
	      then print ("Finitary with " ^ Int.toString (getCount ()) ^ " candidates.\n")
	    else () ;
	    (k, getCount ())::cands )
           handle NotFinitary => ( if !Global.chatter >= 7
				     then print ("Not finitary.\n")
				   else () ;
				   cands )
	)

    (* finitarySplits (XsRev, k, W, cands) = [(k1,n1),...,(km,nm)]@cands
       where all ki are finitary with ni possibilities for X(i+k)
    *)
    fun finitarySplits (nil, k, W, cands) = cands
      | finitarySplits (NONE::Xs, k, W, cands) =
        (* parameter blocks can never be split *)
          finitarySplits (Xs, k+1, W, cands)
      | finitarySplits (SOME(X)::Xs, k, W, cands) =
          finitarySplits (Xs, k+1, W,
			  CSManager.trail (fn () => finitary1 (X, k, W, cands)))

    (* finitary ({{G}} V, p, W) = [(k1,n1),...,(km,nm)]
       where ki are indices of splittable variables in G with ni possibilities
       and |G| = p
    *)
    fun finitary (V, p, W) =
        let
	  val ((V1, s), XsRev) = instEVars ((V, I.id), p, nil)
	in
	  finitarySplits (XsRev, 1, W, nil)
	end

    (***************************)
    (* Printing Coverage Goals *)
    (***************************)

    (* we pass in the mode spine specifying coverage, but currently ignore it *)
    fun abbrevCSpine (S, ci) = S

    (* fix to identify existential and universal prefixes *)
    fun abbrevCGoal (G, V, 0, ci) = (G, abbrevCGoal' (G, V, ci))
      | abbrevCGoal (G, I.Pi((D, P), V), p, ci) = (* p > 0 *)
        let 
	  val D' = Names.decEName (G, D)
	in
	  abbrevCGoal (I.Decl (G, D'), V, p-1, ci)
	end
    and abbrevCGoal' (G, I.Pi((D, P), V), ci) =
        let
	  val D' = Names.decUName (G, D)
	in
	  I.Pi ((D', P), abbrevCGoal' (I.Decl (G, D'), V, ci))
	end
      | abbrevCGoal' (G, I.Root (a, S), ci) =
 	  I.Root (a, abbrevCSpine (S, ci))
      (* other cases are impossible by CGoal invariant *)

    fun formatCGoal (V, p, ci) =
        let
	  val _ = Names.varReset I.Null
	  val (G, V') = abbrevCGoal (I.Null, V, p, ci)
	in
	  F.HVbox [Print.formatCtx (I.Null, G), F.Break, F.String "|-",
		   F.Space, Print.formatExp (G, V')]
	end

    fun formatCGoals ((V,p)::nil, ci) = [formatCGoal (V, p, ci)]
      | formatCGoals ((V,p)::Vs, ci) =
          formatCGoal (V, p, ci) :: F.String "," :: F.Break :: formatCGoals (Vs, ci)

    fun missingToString (Vs, ci) =
        F.makestring_fmt (F.Hbox [F.Vbox0 0 1 (formatCGoals (Vs, ci)), F.String "."])

    (*********************)
    (* Coverage Checking *)
    (*********************)

    (* findMin ((k1,n1),...,(km,nm)) = (ki,ni)
       where ni is the minimum among the n1,...,nm
       Invariant: m >= 1
    *)
    fun findMin ((k,n)::kns) = findMin'((k,n), kns)
    and findMin' ((k0,n0), nil) = (k0,n0)
      | findMin' ((k0,n0), (k',n')::kns) =
        if n' < n0
	  then findMin' ((k',n'), kns)
	else findMin' ((k0,n0), kns)

    (* need to improve tracing with higher chatter levels *)
    (* ccs = covering clauses *)

    (* cover (V, p, (W, ci), ccs, missing) = missing'
       covers ([(V1,p1),...,(Vi,pi)], (W, ci), ccs, missing) = missing'

       check if Match arguments (+ for input, - for output) in V or all Vi, respectively,
       are covered by clauses ccs, adding omitted cases to missing to yield missing'.

       V = {{G}} {{L}} a @ S where |G| = p and G contains the splittable
       variables while L contains the local parameters

       W are the worlds for type family a
       ci are the cover instructions matching S
    *)
    fun cover (V, p, wci as (W, ci), ccs, missing) =
        ( if !Global.chatter >= 6
	    then print (F.makestring_fmt (F.Hbox [F.String "?- ", formatCGoal (V, p, ci),
						  F.String "."]) ^ "\n")
	  else () ;
	  cover' (V, p, wci, ccs, missing) )

    and cover' (V, p, wci as (W, ci), ccs, missing) =
          split (V, p, selectCand (match (I.Null, V, p, ci, ccs)), wci, ccs, missing) 

    and split (V, p, NONE, wci, ccs, missing) = 
        (* V is covered: return missing patterns from other cases *)
        ( if !Global.chatter >= 6
	    then print ("Covered\n")
	  else ();
          missing )
      | split (V, p, SOME(nil), wci as (W, ci), ccs, missing) =
        (* no strong candidates: check for finitary splitting candidates *)
	( if !Global.chatter >= 6
	    then print ("No strong candidates---calculating weak candidates:\n")
	  else ();
	  splitWeak (V, p, finitary (V, p, W), wci, ccs, missing)
         )
      | split (V, p, SOME((k,_)::ksn), wci as (W, ci), ccs, missing) =
	(* some candidates: split first candidate, ignoring multiplicities *)
	(* candidates are in reverse order, so non-index candidates are split first *)
	(* splitVar shows splitting as it happens *)
	(case splitVar (V, p, k, W)
	   of SOME(cases) => covers (cases, wci, ccs, missing)
	    | NONE => (* splitting variable k generated constraints *)
	      split (V, p, SOME (ksn), wci, ccs, missing)) (* try other candidates *)

    and splitWeak (V, p, nil, wci, ccs, missing) =
        ( if !Global.chatter >= 6
	    then print ("No weak candidates---case not covered\n")
	  else () ;
	  (V,p)::missing )
      | splitWeak (V, p, ksn, wci, ccs, missing) = (* ksn <> nil *)
        (* commit to the minimal candidate, since no constraints can arise *)
	  split (V, p, SOME(findMin ksn::nil), wci, ccs, missing)

    and covers (nil, wci, ccs, missing) = missing
      | covers ((V,p)::cases', wci, ccs, missing) =
          covers (cases', wci, ccs, cover (V, p, wci, ccs, missing))

    (******************)
    (* Input Coverage *)
    (******************)

    (* constsToTypes [c1,...,cn] = [V1,...,Vn] where ci:Vi.
       Generates coverage clauses from signature.
    *)
    fun constsToTypes (nil) = nil
      | constsToTypes (I.Const(c)::cs') = I.constType(c)::constsToTypes(cs')

    (*******************)
    (* Output Coverage *)
    (*******************)

    (* createCoverClause (G, V, 0) = ({{G}} V, |G|)
       where {{G}} V is in NF
    *)
    fun createCoverClause (I.Decl (G, D), V, p) =
          createCoverClause (G, I.Pi ((D, I.Maybe), V), p+1)
      | createCoverClause (I.Null, V, p) =
	  (Whnf.normalize (V, I.id), p)

    (* createCoverGoal (., ({{G}} {{GL}} a @ S, s), p, ms) = V' with |G| = p
       createCoverGoal (GL, (a @ S, s), 0, ms) = a @ S'
       createCoverSpine ((S, s), (V', s'), ms) = S'

       where all variables in G are replaced by new EVars in V to yield V'
       and output arguments in S are replaced by new EVars in V to yield V'

       G are the externally quantified variables
       GL are the locally introduced parameter for the current subgoal a @ S

       Invariants: . |- ({{G}} {{GL}} a @ S)[s] : type
                   |G| = p
                   ms matches S
		   . | S[s] : V'[s'] > type
		   . |- V'[s'] : type
    *)
    fun createCoverGoal (G, Vs, p, ms) =
           createCoverGoalW (G, Whnf.whnf (Vs), p, ms)

    and createCoverGoalW (G, (I.Pi ((D1,P1), V2), s), 0, ms) =
        let
	  val D1' = I.decSub (D1, s)
	  val V2' = createCoverGoal (I.Decl (G, D1'), (V2, I.dot1 s), 0, ms)
	in
	  I.Pi ((D1',P1), V2')
	end
      | createCoverGoalW (G, (I.Pi ((D as I.Dec (_, V1), _), V2), s), p, ms) =
        let (* p > 0, G = I.Null *)
	  val X = I.newEVar (G, I.EClo (V1, s))
	in
	  createCoverGoal (G, (V2, I.Dot (I.Exp (X), s)), p-1, ms)
	end
      | createCoverGoalW (G, (I.Root (a as I.Const(cid), S), s), p, ms) = (* s = id, p >= 0 *)
	I.Root (a, createCoverSpine (G, (S, s), (I.constType (cid), I.id), ms))

    and createCoverSpine (G, (I.Nil, s), _, M.Mnil) = I.Nil
      | createCoverSpine (G, (I.App (U1, S2), s), (I.Pi ((I.Dec (_, V1), _), V2), s'),
			  M.Mapp (M.Marg (M.Minus, x), ms')) =
        (* replace output argument by new variable *)
        let
	  val X = createEVar (G, I.EClo (V1, s')) (* strengthen G based on subordination *)
	  val S2' = createCoverSpine (G, (S2, s), (V2, I.Dot (I.Exp (X), s')), ms')
	in
          I.App (X, S2')
	end
      | createCoverSpine (G, (I.App (U1, S2), s), (I.Pi (_, V2), s'), M.Mapp (_, ms')) =
	(* leave input ( + ) arguments as they are, ignore ( * ) impossible *)
	  I.App (I.EClo (U1, s),
		 createCoverSpine (G, (S2, s), Whnf.whnf (V2, I.Dot (I.Exp (I.EClo (U1, s)), s')),
				   ms'))
      | createCoverSpine (G, (I.SClo (S, s'), s), Vs, ms) =
	  createCoverSpine (G, (S, I.comp (s', s)), Vs, ms)


  in

    (* checkCovers (a, ms) = ()
       checks coverage for type family a with respect to mode spine ms
       Effect: raises Error (msg) otherwise
    *)
    fun checkCovers (a, ms) =
        let
	  val (V0, p) = initCGoal (a)
	  val _ = if !Global.doubleCheck
		    then TypeCheck.typeCheck (I.Null, (V0, I.Uni (I.Type)))
		  else ()
	  val _ = CSManager.reset ()
	  val cIn = inCoverInst ms	(* convert mode spine to cover instructions *)
	  val cs = Index.lookup a	(* lookup constants defining a *)
	  val ccs = constsToTypes cs	(* calculate covering clauses *)
	  val W = W.lookup a		(* world declarations for a; must be defined *)
	  val missing = cover (V0, p, (W, cIn), Input(ccs), nil)
	  val _ = case missing
	            of nil => ()	(* all cases covered *)
		     | _::_ => raise Error ("Coverage error --- missing cases:\n"
					    ^ missingToString (missing, ms) ^ "\n")
	in
	  ()
	end

    (* checkOut (G, (V, s)) = ()
       checks if the most general goal V' is locally output-covered by V
       Effect: raises Error (msg) otherwise
    *)
    fun checkOut (G, (V, s)) =
	let
	  val a = I.targetFam V
	  val SOME(ms) = ModeSyn.modeLookup a (* must be defined and well-moded *)
	  val cOut = outCoverInst ms	(* determine cover instructions *)
	  val (V', q) = createCoverClause (G, I.EClo(V, s), 0) (* abstract all variables in G *)
	  val _ = if !Global.doubleCheck
		    then TypeCheck.typeCheck (I.Null, (V', I.Uni (I.Type)))
		  else ()
	  val V0 = createCoverGoal (I.Null, (V', I.id), q, ms) (* replace output by new EVars *)
	  val (V0', p) = abstract (V0, I.id)	(* abstract will double-check *)
	  val W = W.lookup a
	  val missing = cover (V0', p, (W, cOut), Output(V',q), nil)
	  val _ = case missing
	            of nil => ()
		     | _::_ => raise Error ("Output coverage error --- missing cases:\n"
					    ^ missingToString (missing, ms) ^ "\n")
	in
	  ()
	end

  end
end;  (* functor Cover *)
