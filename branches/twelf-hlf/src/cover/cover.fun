(* Coverage Checking *)
(* Author: Frank Pfenning *)

functor Cover
  (structure Global : GLOBAL
   structure Whnf : WHNF
   structure Conv : CONV
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   structure Unify : UNIFY		(* must be trailing! *)
   (*! sharing Unify.IntSyn = IntSyn' !*)
   structure Constraints : CONSTRAINTS
   (*! sharing Constraints.IntSyn = IntSyn' !*)
   structure ModeTable : MODETABLE
   structure UniqueTable : MODETABLE
   structure Index : INDEX
   (*! sharing Index.IntSyn = IntSyn' !*)
   structure Subordinate : SUBORDINATE
   (*! sharing Subordinate.IntSyn = IntSyn' !*)

   structure WorldSyn : WORLDSYN
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   (*! structure Paths : PATHS !*)
   structure Print : PRINT
   (*! sharing Print.IntSyn = IntSyn' !*)
   structure TypeCheck : TYPECHECK
   (*! sharing TypeCheck.IntSyn = IntSyn' !*)
   (*! structure CSManager : CS_MANAGER !*)
   (*! sharing CSManager.IntSyn = IntSyn' !*)
   structure Timers : TIMERS)
  : COVER =
struct
  exception Error of string

  local
    structure I = IntSyn
    structure T = Tomega
    structure M = ModeSyn
    structure W = WorldSyn
    structure P = Paths
    structure F = Print.Formatter
    structure N = Names

    (*****************)
    (* Strengthening *)
    (*****************)

    (* next section adapted from m2/metasyn.fun *)

    (* original `weaken' code *)
    fun weaken (I.Null, a) = I.id
      | weaken (I.Decl (G', D as I.Dec (name, V)), a) =
	let
	    val w' = weaken (G', a)
	in
	  if Subordinate.belowEq (I.targetFam V, a) then I.dot1 w'
	  else I.comp (w', I.shift)
 	end

    (* debugging utility function *)
    fun strjoin d [] = ""
      | strjoin d [x] = x
      | strjoin d (h::tl) = h ^ d ^ strjoin d tl

    (* cantOccur : int list -> I.Exp -> bool *)
    (* cantOccur (params, tp) *)
    (* = true iff there is some param in the list params of deBruijn indices *)
    (* that has no occurrence in tp. *)
    fun cantOccur (params, tp) = List.exists (fn param => cantOccurOne param (tp, I.id)) params
    and cantOccurOne param (V, s) = cantOccurOneW param (Whnf.whnf (V, s))
    and cantOccurOneW param (I.Pi((I.Dec(_, A), dep), B), s) = cantOccurOne (param + 1) (B, I.dot1 s)
      | cantOccurOneW param (I.Root(I.Const a, S), s) = if I.hlfIsSubstructCid a 
							then I.noOccur (param, Whnf.normalizeWorldExp (spineLast (S, s)))
							else true (* *no* subtructural things can appear in an unrestricted type *)
      | cantOccurOneW _ _ = false

    (* span : I.Exp -> int list *)
    (* span V *)
    (* Given a type, returns a list of deBruijn indices of parameters that are *)
    (* certain to be in the world-label that any atomic term x (M1; ... Mn) is well-typed at, *) 
    (* for any x : V. We approximate this pessimistically by just substituting *)
    (* epsilon for every world argument. *)
    and span V = span' 0 (V, I.id)
    (* assume we have descended under n binders *)
    and span' n (V, s) = spanW' n (Whnf.whnf (V, s))
    and spanW' n (I.Pi(_, V), s) = span' (n + 1) (V, s)
      | spanW' n (I.Root(I.Const a, S), s) = if I.hlfIsSubstructCid a
					     then 
						 let val parms = Whnf.normalizeWorldExp (spineLast (S, I.id))
						     fun  go (I.Root(I.BVar n', _)::tl) = 
							  (* exclude locally bound variables *)
							  if n' > n 
							  then (n' - n) :: go tl
							  else go tl
							| go _ = [] (* also don't include evars *)
						 in
						     go parms
						 end
					     else []
      | spanW' n (V, s) = [] (* nil is conservative --- we won't strengthen anything with *no* paramaters *) 
    and spineLast (I.App(x, I.Nil), s) = (x, s)
      | spineLast (I.App(_, S), s) = spineLast (S, s)
      | spineLast (I.SClo(S, s'), s) = spineLast (S, I.comp (s', s))

    (* hlfWeaken (G, V) = w'

       w' is a strengthening [sic!] substitution that trims
       from G variables that cannot be used to produce anything
       of type V.

       Invariant:
       then G |- w' : G'

       G' is a subcontext of G after this strengthening has occurred.
       Traditionally, we only used subordination information,
       but here I'm doing some reasoning about worlds, too.
     *)
	
    fun hlfWeaken (G, W) =
	let
	    fun tos x = I.expToString(Whnf.normalize(x, I.id))
	    (* weak is given the current deBruijn index, and the type *)
	    fun weak (n, I.Null) = I.id
	      | weak (n, I.Decl (G', D as I.Dec (name, V))) =
		let
		    val a = I.targetFam W
		    val w' = weak (n + 1, G')
		    fun isWorld V = let val (V', s) = Whnf.whnf (V, I.id) in I.hlfIsWorldExp V' end
		    fun hlfShouldWeaken () = (if isWorld W then false
					      else 
						  if isWorld V 
						  then cantOccur ([n], W)
						  else cantOccur (map (fn x => x + n) (* shift because we got them from the ctx *)
								      (span V), W))
		    val shouldWeaken = 
			(not (Subordinate.belowEq (I.targetFam V, a)))
			orelse
			(!Global.hlf andalso hlfShouldWeaken())
		in
		    if not shouldWeaken 
		    then I.dot1 w'
		    else I.comp (w', I.shift)
		end
	in
	    weak (1, G)
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
	  val w = weaken (G, I.targetFam V)    (* G  |- w  : G'    *)
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

    (***************************)
    (* Printing Coverage Goals *)
    (***************************)

    (* labels for cases for tracing coverage checker *)
    datatype caseLabel =
        Top				(* ^ *)
      | Child of caseLabel * int        (* lab.n, n >= 1 *)

    fun labToString (Top) = "^"
      | labToString (Child(lab, n)) = labToString(lab) ^ "." ^ Int.toString(n)

    fun chatter chlev f =
        if !Global.chatter >= chlev
	  then print (f ())
	else ()

    fun pluralize (1, s) = s
      | pluralize (n, s) = s ^ "s"

    (* we pass in the mode spine specifying coverage, but currently ignore it *)
    fun abbrevCSpine (S, ci) = S

    (* fix to identify existential and universal prefixes *)
    fun abbrevCGoal (G, V, 0, ci) = (G, abbrevCGoal' (G, V, ci))
      | abbrevCGoal (G, I.Pi((D, P), V), p, ci) = (* p > 0 *)
        let 
	  val D' = N.decEName (G, D)
	in
	  abbrevCGoal (I.Decl (G, D'), V, p-1, ci)
	end
    and abbrevCGoal' (G, I.Pi((D, P), V), ci) =
        let
	  val D' = N.decUName (G, D)
	in
	  I.Pi ((D', P), abbrevCGoal' (I.Decl (G, D'), V, ci))
	end
      | abbrevCGoal' (G, I.Root (a, S), ci) =
 	  I.Root (a, abbrevCSpine (S, ci))
      (* other cases are impossible by CGoal invariant *)

    fun formatCGoal (V, p, ci) =
        let
	  val _ = N.varReset I.Null
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

    fun showSplitVar (V, p, k, ci) =
        let
	  val _ = N.varReset I.Null
	  val (G, V') = abbrevCGoal (I.Null, V, p, ci)
	  val I.Dec (SOME(x), _) = I.ctxLookup (G, k)
	in
	  "Split " ^ x ^ " in " ^ Print.expToString (G, V')
	end

    fun showPendingGoal (V, p, ci, lab) =
          F.makestring_fmt (F.Hbox [F.String(labToString(lab)), F.Space, F.String "?- ",
				    formatCGoal (V, p, ci), F.String "."])

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
        (* Eta-long invariant violation -kw *)
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
	  val D' = N.decEName (G, D)
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

    fun equationToString (Eqn (G, Us1, Us2)) =
        let val G' = Names.ctxLUName G
	  val fmt =
	      F.HVbox [Print.formatCtx (I.Null, G'), F.Break,
		       F.String "|-", F.Space,
		       Print.formatExp (G', I.EClo (Us1)), F.Break,
		       F.String "=", F.Space,
		       Print.formatExp (G', I.EClo (Us2))]
	in
	  F.makestring_fmt (fmt)
	end

    fun eqnsToString (nil) = ".\n"
      | eqnsToString (eqn::eqns) =
          equationToString (eqn) ^ ",\n"
	  ^ eqnsToString (eqns)

    (* Splitting candidates *)
    (* Splitting candidates [k1,...,kl] are indices
       into coverage goal {xn:Vn}...{x1:V1} a M1...Mm, counting right-to-left
    *)
    datatype Candidates =
        Eqns of Equation list		(* equations to be solved, everything matches so far *)
      | Cands of int list		(* candidates for splitting, matching fails *)
      | Fail				(* coverage fails without candidates *)

    fun candsToString (Fail) = "Fail"
      | candsToString (Cands(ks)) = "Cands [" ^ List.foldl (fn (k,str) => Int.toString k ^ "," ^ str) "]" ks
      | candsToString (Eqns(eqns)) = "Eqns [\n" ^ eqnsToString eqns ^ "]"

    (* fail () = Fail
       indicate failure without splitting candidates
     *)
    fun fail (msg) =
        (chatter 7 (fn () => msg ^ "\n");
	 Fail)

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

    fun unifiable (G, Us1, Us2) =
          Unify.unifiable (G, Us1, Us2)

    fun unifiableDX (G, Us1, Us2) =
	(print ("cxu unifiable? " ^ IntSyn.expToString (Whnf.normalize Us1) ^ " = " ^ IntSyn.expToString (Whnf.normalize Us2) ^ "\n");
         if Unify.unifiable (G, Us1, Us2)
	 then (print "yes!\n"; true)
	 else (print "no!\n"; false))

    (* matchEqns (es) = true 
       iff  all equations in es can be simultaneously unified

       Effect: instantiate EVars right-hand sides of equations.
    *)
    fun matchEqns (nil) = true
      | matchEqns (Eqn (G, Us1, Us2 as (U2, s2))::es) =
        (* For some reason, s2 is sometimes not a patSub when it should be *)
        (* explicitly convert if possible *)
        (* Sat Dec  7 20:59:46 2002 -fp *)
        (* was: unifiable (G, Us1, Us2) *)
        (case Whnf.makePatSub s2
	   of NONE => unifiable (G, Us1, Us2) (* constraints will be left in this case *)
            | SOME(s2') => unifiable (G, Us1, (U2, s2')))
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

    fun resolveCandsDX (e as Eqns (es)) = 
(
(*	 print "-- resolveCandsDX\n"; *)
(*	 app (fn x => print ((equationToString x handle Unprintable => "???") ^ "\n")) es;  *)
	 resolveCands e)
      | resolveCandsDX e = resolveCands e

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
	     | eqns => (print ("DX cover.fun remaining constrants " ^ IntSyn.cnstrsToString eqns ^ "\n"); Fail)
	(* constraints remained: Fail without candidates *)
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

    and matchExpW (G, d, Us1 as (U1 as I.Root (H1, S1), s1), Us2 as (U2 as I.Root (H2, S2), s2), cands) =
	if (I.hlfSpecialExp U1 orelse I.hlfSpecialExp U2)
	then addEqn (Eqn (G, Us1, Us2), cands)
        else
	 (case (H1, H2)
	   (* Note: I.Proj occurring here will always have the form
	      I.Proj (I.Bidx (k), i) *)
	   (* No skolem constants, foreign constants, FVars *)
	   of (I.BVar (k1), I.BVar(k2)) =>
	      if (k1 = k2)
		then matchSpine (G, d, (S1, s1), (S2, s2), cands)
	      else if k1 > d
		     then failAdd (k1-d, cands) (* k1 is coverage variable, new candidate *)
		   else fail ("local variable / variable clash") (* otherwise fail with no candidates *)
	    | (I.Const(c1), I.Const(c2)) =>
	      if (c1 = c2) then matchSpine (G, d, (S1, s1), (S2, s2), cands)
	      else fail ("constant / constant clash") (* fail with no candidates *)
            | (I.Def (d1), I.Def (d2)) =>
	      if (d1 = d2)		(* because of strictness *)
		then matchSpine (G, d, (S1, s1), (S2, s2), cands)
	      else matchExpW (G, d, Whnf.expandDef Us1, Whnf.expandDef Us2, cands)
	    | (I.Def (d1), _) => matchExpW (G, d, Whnf.expandDef Us1, Us2, cands)
	    | (_, I.Def (d2)) => matchExpW (G, d, Us1, Whnf.expandDef Us2, cands)
	    | (I.BVar (k1), I.Const _) =>
	      if k1 > d
		then failAdd (k1-d, cands) (* k1 is coverage variable, new candidate *)
	      else fail ("local variable / constant clash") (* otherwise fail with no candidates *)
	    | (I.Const _, I.BVar _) =>
		fail ("constant / local variable clash")
	    | (I.Proj (I.Bidx(k1), i1), I.Proj(I.Bidx(k2), i2)) =>
	      if k1 = k2 andalso i1 = i2
		then matchSpine (G, d, (S1, s1), (S2, s2), cands)
	      else fail ("block index / block index clash")
	    | (I.Proj (I.Bidx(k1), i1), I.Proj(I.LVar(r2, I.Shift(k2), (l2, t2)), i2)) =>
	      let
		val I.BDec (bOpt, (l1, t1)) = I.ctxDec (G, k1)
	      in
		if l1 <> l2 orelse i1 <> i2
		  then fail ("block index / block variable clash")
		else let val cands2 = matchSub (G, d, t1, t2, cands)
		         (* instantiate instead of postponing because LVars are *)
		         (* only instantiated to Bidx which are rigid *)
		         (* Sun Jan  5 12:03:13 2003 -fp *)
			 val _ = Unify.instantiateLVar (r2, I.Bidx (k1-k2))
		     in
		       matchSpine (G, d, (S1, s1), (S2, s2), cands2)
		     end
	      end
	    (* handled in above two cases now *)
	    (*
	    | (I.Proj (b1, i1), I.Proj (b2, i2)) =>
	       if (i1 = i2) then
		 matchSpine (G, d, (S1, s1), (S2, s2),
			     matchBlock (G, d, b1, b2, cands))
	       else fail ("block projection / block projection clash")
            *)
            | (I.BVar (k1), I.Proj _) =>
	      if k1 > d
		then failAdd (k1-d, cands) (* k1 is splittable, new candidate *)
	      else fail ("local variable / block projection clash") (* otherwise fail with no candidates *)
	    | (I.Const _, I.Proj _) => fail ("constant / block projection clash")
            | (I.Proj _, I.Const _) => fail ("block projection / constant clash")
            | (I.Proj _, I.BVar _) => fail ("block projection / local variable clash")
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

    (* matchBlock now unfolded into the first case of matchExpW *)
    (* Sun Jan  5 12:02:49 2003 -fp *)
    (*
    and matchBlock (G, d, I.Bidx(k), I.Bidx(k'), cands) =
        if (k = k') then cands
	  else fail ("block index / block index clash")
      | matchBlock (G, d, B1 as I.Bidx(k), I.LVar (r2, I.Shift(k'), (l2, t2)), cands) =
	(* Updated LVar --cs Sun Dec  1 06:24:41 2002 *)
	let
	  val I.BDec (bOpt, (l1, t1)) = I.ctxDec (G, k)
	in
	  if l1 <> l2 then fail ("block index / block label clash")
	  (* else if k < k' then raise Bind *)
	  (* k >= k' by invariant  Sat Dec  7 22:00:41 2002 -fp *)
	  else let 
		 val cands2 = matchSub (G, d, t1, t2, cands)
		 (* instantiate if matching is successful *)
		 (* val _ = print (candsToString (cands2) ^ "\n") *)
		 (* instantiate, instead of postponing because *)
		 (* LVars are only instantiated to Bidx's which are rigid *)
                 (* !!!BUG!!! r2 and B1 make sense in different contexts *)
                 (* fixed by k-k' Sat Dec  7 21:12:57 2002 -fp *)
		 val _ = Unify.instantiateLVar (r2, I.Bidx (k-k'))
	       in
		 cands2
	       end
	end
    *)

    and matchSub (G, d, I.Shift(n1), I.Shift(n2), cands) = cands
        (* by invariant *)
      | matchSub (G, d, I.Shift(n), s2 as I.Dot _, cands) = 
          matchSub (G, d, I.Dot(I.Idx(n+1), I.Shift(n+1)), s2, cands)
      | matchSub (G, d, s1 as I.Dot _, I.Shift(m), cands) =
	  matchSub (G, d, s1, I.Dot(I.Idx(m+1), I.Shift(m+1)), cands)
      | matchSub (G, d, I.Dot(Ft1,s1), I.Dot(Ft2,s2), cands) =
	let val cands1 =
	   (case (Ft1, Ft2) of
	     (I.Idx (n1), I.Idx (n2)) => 
	       if n1 = n2
		 then cands
	       else if n1 > d
		      then failAdd (n1-d, cands)
		    else fail ("local variable / local variable clash in block instance")
           | (I.Exp (U1), I.Exp (U2)) =>
		 matchExp (G, d, (U1, I.id), (U2, I.id), cands)
	   | (I.Exp (U1), I.Idx (n2)) =>
		 matchExp (G, d, (U1, I.id), (I.Root (I.BVar (n2), I.Nil), I.id), cands)
           | (I.Idx (n1), I.Exp (U2)) =>
		 matchExp (G, d, (I.Root (I.BVar (n1), I.Nil), I.id), (U2, I.id), cands))
	in
	  matchSub (G, d, s1, s2, cands1)
	end

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
	else fail ("type family clash") (* fails, with no candidates since type families don't match *)
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
          checkConstraints (G, qs, resolveCandsDX (matchTop (G, 0, ps', qs, ci, Eqns (nil))))
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
    fun matchClauseDX (G, psorig, ps, qs, ci) = 
	let
(*	    val _ = print ("- 1. coverage ctx " ^ I.ctxToString I.decToString G ^ "\n")
	    val _ = print ("- 2. coverage goal " ^ Print.expToString(I.Null, Whnf.normalize (psorig, I.id)) ^ "\n") handle Bind => (print "???\n")
	    val _ = print ("- 3. coverage clause " ^ Print.expToString(I.Null, Whnf.normalize qs) ^ "\n") handle Bind => (print "???\n") *)
	in
	    matchClause (G, ps, qs, ci)
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
    fun matchSigDX (G, ps, ps', nil, ci, klist) = klist
      | matchSigDX (G, ps, ps', V::ccs', ci, klist) =
        let
	  val cands = CSManager.trail
	              (fn () => matchClauseDX (G, ps, ps', (V, I.id), ci))
	in
	    case addKs (cands, klist) of
		Covered => ((* print "Immediately covered!\n";*) Covered)
	      | klist' => ((* print "Not immediately covered...\n";*) matchSigDX (G, ps, ps', ccs', ci, klist'))
	end

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

    fun matchDX (G, Vorig, V as I.Root (I.Const (a), S), 0, ci, Input(ccs)) =
        matchCtx' (G, I.id, G, V, 1, ci,
		   matchSigDX (G, Vorig, (V, I.id), ccs, ci, CandList (nil)))
      | matchDX (G, Vorig, V, 0, ci, Output (V', q)) =
	matchOut (G, V, ci, (V', I.Shift (I.ctxLength G)), q)
      | matchDX (G, Vorig, I.Pi ((D, _), V'), p, ci, ccs) =
	matchDX (I.Decl (G, D), Vorig, V', p-1, ci, ccs)

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
	  val L1 = I.newLVar (I.Shift(0), (l, I.comp(t, s)))
	  (* new -fp Sun Dec  1 20:58:06 2002 *)
	  (* new -cs  Sun Dec  1 06:27:57 2002 *)
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
	  val _ = chatter 6 (fn () => "Considering constant " ^ I.conDecName(I.sgnLookup c) ^ "\n")   (* XXX -jcreed *)
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
	  val t = createEVarSub Gsome
	  (* . |- t : Gsome *)
	  val sk = I.Shift (I.ctxLength(G))
	  val t' = I.comp (t, sk)
	  val lvar = I.newLVar (sk, (cid, t'))
	             (*  BUG. Breach in the invariant:
                         G |- sk : .
			 . |- t: Gsome
			 G <> .

			 replace t by t' in I.newLVar (sk, (cid, t))
		      --cs Fri Jan  3 11:07:41 2003 *)
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

    fun worldCases (G, Vs, T.Worlds (nil), sc) = ()
      | worldCases (G, Vs, T.Worlds (cid::cids), sc) =
          ( blockCases (G, Vs, cid, I.constBlock cid, sc) ;
	    worldCases (G, Vs, T.Worlds (cids), sc) )

    fun lowerSplit (G, Vs, W, sc) = lowerSplitW (G, Whnf.whnf Vs, W, sc)
    and lowerSplitW (G, Vs as (I.Root (I.Const a, _), s), W, sc) =
        let
	    (* XXX stopgap measure to refrain from splitting world variables -jcreed *)
	    val _ = if I.hlfIsWorld a 
		    then raise Constraints.Error []  
		    else ()
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
		      fn U =>  if Unify.unifiable (I.Null, (X, I.id), (U, I.id))
			       then  sc ()
			       else  ())

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

    (* building up towards hlfAbstract *)

    fun hlfCreateEVar (G, V) =
        let (* G |- V : L *)
	    val Gstr = Print.ctxToString (I.Null, G)
	    val Vstr = Print.expToString (G, V)
(*	    val _ = print ("DX createEvar  " ^ Gstr ^ " |- " ^ Vstr ^ "\n")  *)
	    val ow = weaken (G, I.targetFam V)              
	    val w = hlfWeaken (G, V)              
(*  	    val _ = print ("DX <- " ^ I.subToString ow ^ "\n") *)
(* 	    val _ = print ("DX -> " ^ I.subToString w ^ "\n") *)
	    val iw = Whnf.invert w 	          (* G' |- iw : G     *)
	    val G' = Whnf.strengthen (iw, G)
	    val X' = I.newEVar (G', I.EClo (V, iw)) (* G' |- X' : V[iw] *)
	    val X = I.EClo (X', w)	          (* G  |- X  : V     *)
	in
	    X
	end

    fun hlfCreateLoweredEVarW (G, (I.Pi ((D, _), V), s)) =
        let
          val D' = I.decSub (D, s)
        in
          I.Lam (D', hlfCreateLoweredEVar (I.Decl (G, D'), (V, I.dot1 s)))
        end
      | hlfCreateLoweredEVarW (G, Vs) = hlfCreateEVar (G, I.EClo Vs)

    and hlfCreateLoweredEVar (G, Vs) = hlfCreateLoweredEVarW (G, Whnf.whnfExpandDef Vs)

    fun hlfInstEVars (Vs, p, XsRev) = hlfInstEVarsW (Whnf.whnf Vs, p, XsRev)
    and hlfInstEVarsW (Vs, 0, XsRev) = (Vs, XsRev)
      | hlfInstEVarsW ((I.Pi ((I.Dec (xOpt, V1), _), V2), s), p, XsRev) =
        let (* p > 0 *)
	  val X1 = hlfCreateLoweredEVar (I.Null, (V1, s)) (* all EVars are global *)
	in
	  hlfInstEVars ((V2, I.Dot (I.Exp (X1), s)), p-1, SOME(X1)::XsRev)
	end
      | hlfInstEVarsW ((I.Pi ((I.BDec (_, (l, t)), _), V2), s), p, XsRev) =
        (* G0 |- t : Gsome *)
	(* . |- s : G0 *)
	let (* p > 0 *)
	  val L1 = I.newLVar (I.Shift(0), (l, I.comp(t, s)))
	  (* new -fp Sun Dec  1 20:58:06 2002 *)
	  (* new -cs  Sun Dec  1 06:27:57 2002 *)
	in
	  hlfInstEVars ((V2, I.Dot (I.Block (L1), s)), p-1, NONE::XsRev)
	end

    fun hlfAbstract (V, s) =
	let val (V1, i) = abstract (V, s)
	    val ((V2, s2), XsRev) = hlfInstEVars((V1, I.id), i, nil)
	    val (V3, i3) = abstract (V2, s2)
	in
	    (V3, i3)
	end

    (* addFinitaryCases (V, s) Calls addCase for all cases that arise
    from the post-unification coverage goal V[s], splitting along all
    finitary case splits that can be discerned from the constraints
    remaining in V[s].

    If there are no remaining constraints at all, then we just add the
    abstracted case (V,s)

    The only finitary splits attempted for now are certain ones
    arising from the HLF constraint domain. If there are still
    constraints remaining after those, then (re)raise
    Constraints.Error *)

    (* raised when we get a constraint that is not known to be finitary *)
    exception FinitaryCasesFailure

    fun addFinitaryCases (V, s) = 
	let

	    val newCases : (IntSyn.Exp * int) list ref
	      = ref []

       (* consider cnstr k 
          Splits over the (finite) solutions of cnstr, and calls
          continuation k on each, within a trailing scope. 

	  Raises exception if we don't know how to finitely split. *)

	    fun consider cnstr k =
		let
		    fun carryOut [] k = ()
		      | carryOut (h::tl) k =
			let 
			    (* cf. awakeCnstr in unify.fun *)
			    fun awake (I.Eqn (G, U1, U2)) = 
				(Unify.solveConstraint cnstr;
				 Unify.unify (G, (U1, I.id), (U2, I.id))
				 handle Unify.Unify _ => raise Error "unexpected Unify")
			      | awake I.Solved = ()
			      | awake (I.FgnCnstr _) = raise Error "unexpected FgnCnstr"
			in
			    CSManager.trail (fn () => (h(); awake (!cnstr); k()));
			    carryOut tl k
			end
		in
		    case Unify.finitaryConstraint cnstr of
			SOME insts => carryOut insts k
		      | NONE => raise FinitaryCasesFailure
		end

       (* addFinitaryCases cnstrs (V, s) 
       cnstrs is remaining constraints *)

	    fun addFinitaryCases' [] (V, s) = 
		let
(*		    val _ = print "[cover.fun] about to abstract...\n"
		    val _ = print ("--- " ^ IntSyn.expToString (Whnf.normalize (V,s)) ^"\n") *)
		    val c = hlfAbstract (V, s)
(* 		    val _ = print "...Succeeded at abstracting!\n" *)
		in
		    addCase c
		end 
	      (* The above line will *not* recurse and handle further
	       solvable constraints - this is ok for now. Indeed I am
	       a bit worried about whether termination would hold
	       unless that recursion were done non-naively. -jcreed *)
	      | addFinitaryCases' (h::tl) (V, s) = consider h (fn () => addFinitaryCases' tl (V, s))
	in
	    addCase (hlfAbstract (V, s))
            handle (e as Constraints.Error (cnstrs)) =>
		   ((chatter 1 (fn () => "[cover.fun] Splitting, got constraints: " ^ Print.cnstrsToString (cnstrs) ^ "\n");
		     addFinitaryCases' cnstrs (V, s);
		     print "[cover.fun] Ok, adding new cases.\n";
		     app addCase (!newCases))
		    handle FinitaryCasesFailure => (print "[cover.fun] couldn't fsplit...\n"; raise e))
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
    fun splitVar (V, p, k, (W, ci)) =
        let
	  val _ = chatter 6 (fn () => showSplitVar (V, p, k, ci) ^ "\n")
	  val ((V1, s), XsRev) = instEVars ((V, I.id), p, nil)
          (* split on k'th variable, counting from innermost *)
	  val SOME(X) = List.nth (XsRev, k-1)
	  val _ = resetCases ()
	  val _ = splitEVar (X, W, fn () => addFinitaryCases (V1, s))	(* may raise Constraints.Error *)
	in
	  SOME (getCases ())
	end
        (* Constraints.Error could be raised by abstract *)
        handle Constraints.Error (constrs) =>
	  (chatter 7 (fn () => "Inactive split:\n" ^ Print.cnstrsToString (constrs) ^ "\n");
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

    (* Stolen from abstract.fun *)

    fun occursInExp (k, I.Uni _) = false
      | occursInExp (k, I.Pi (DP, V)) = occursInDecP (k, DP) orelse occursInExp (k+1, V)
      | occursInExp (k, I.Root (H, S)) = occursInHead (k, H) orelse occursInSpine (k, S)
      | occursInExp (k, I.Lam (D, V)) = occursInDec (k, D) orelse occursInExp (k+1, V)
      | occursInExp (k, I.FgnExp (cs, ops)) = false
        (* foreign expression probably should not occur *)
        (* but if they do, variable occurrences don't count *)
        (* occursInExp (k, Whnf.normalize (#toInternal(ops) (), I.id)) *)
      (* no case for Redex, EVar, EClo *)

    and occursInHead (k, I.BVar (k')) = (k = k')
      | occursInHead (k, _) = false

    and occursInSpine (_, I.Nil) = false
      | occursInSpine (k, I.App (U, S)) = occursInExp (k, U) orelse occursInSpine (k, S)
      (* no case for SClo *)

    and occursInDec (k, I.Dec (_, V)) = occursInExp (k, V)
    and occursInDecP (k, (D, _)) = occursInDec (k, D)

    (* occursInMatchPos (k, U, ci) = true
       if k occur in U in a matchable position according to the coverage
       instructions ci
    *)
    fun occursInMatchPos (k, I.Pi (DP, V), ci) =
          occursInMatchPos (k+1, V, ci)
      | occursInMatchPos (k, I.Root (H, S), ci) =
	  occursInMatchPosSpine (k, S, ci)
    and occursInMatchPosSpine (k, I.Nil, Cnil) = false
      | occursInMatchPosSpine (k, I.App(U, S), Match(ci)) =
          occursInExp (k, U) orelse occursInMatchPosSpine (k, S, ci)
      | occursInMatchPosSpine (k, I.App(U, S), Skip(ci)) =
          occursInMatchPosSpine (k, S, ci)

    (* instEVarsSkip ({x1:V1}...{xp:Vp} V, p, nil, ci) = (V[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars that actually occur in a "Match" argument
       and ci are the coverage instructions (Match or Skip) for the target type of V
    *)
    fun instEVarsSkip (Vs, p, XsRev, ci) = InstEVarsSkipW (Whnf.whnf Vs, p, XsRev, ci)
    and InstEVarsSkipW (Vs, 0, XsRev, ci) = (Vs, XsRev)
      | InstEVarsSkipW ((I.Pi ((I.Dec (xOpt, V1), _), V2), s), p, XsRev, ci) =
        let (* p > 0 *)
	  val X1 = I.newEVar (I.Null, I.EClo (V1, s)) (* all EVars are global *)
	  val EVarOpt = if occursInMatchPos (1, V2, ci)
			  then SOME(X1)
			else NONE
	in
	  instEVarsSkip ((V2, I.Dot (I.Exp (X1), s)), p-1, EVarOpt::XsRev, ci)
	end
      | InstEVarsSkipW ((I.Pi ((I.BDec (_, (l, t)), _), V2), s), p, XsRev, ci) =
        (* G0 |- t : Gsome *)
	(* . |- s : G0 *)
	let (* p > 0 *)
	  val L1 = I.newLVar (I.Shift(0), (l, I.comp(t, s)))
	  (* -fp Sun Dec  1 21:09:38 2002 *)
	  (* -cs Sun Dec  1 06:30:59 2002 *)
	in
	  instEVarsSkip ((V2, I.Dot (I.Block (L1), s)), p-1, NONE::XsRev, ci)
	end

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

    (* finitary1 (X, k, W, f, cands)
        = ((k, n)::cands) if X is finitary with n possibilities
        = cands if X is not finitary
    *)
    (* The function f has been added to ensure that k is splittable without 
       constraints.   In the previous version, this check was not performed.
       nat : type.
       z : nat.
       s : nat -> nat.

       eqz :  nat -> type.
       eqz_z : eqz z.

       unit : type.
       * : unit.

       test : {f : unit -> nat} eqz (f * ) -> type.
       %worlds () (test _ _).
       %covers test +F +Q.  %% loops! 
        Counterexample due to Andrzej.  Fix due to Adam.
	Mon Oct 15 15:08:25 2007 --cs 
    *)
    fun finitary1 (X as I.EVar(r, I.Null, VX, _), k, W, f, cands) =
        ( resetCount () ;
	  chatter 7 (fn () => "Trying " ^ Print.expToString (I.Null, X) ^ " : "
		     ^ Print.expToString (I.Null, VX) ^ ".\n") ;
	  ( splitEVar (X, W, fn () => (f (); if recursive X
					then raise NotFinitary
				      else incCount ())) ;
	    chatter 7 (fn () => "Finitary with " ^ Int.toString (getCount ()) ^ " candidates.\n");
	    (k, getCount ())::cands )
           handle NotFinitary => ( chatter 7 (fn () => "Not finitary.\n");
				   cands )
	         | Constraints.Error (constrs) =>
	                         ( chatter 7 (fn () => "Inactive finitary split.\n");
				   cands )
	)

    (* finitarySplits (XsRev, k, W, cands) = [(k1,n1),...,(km,nm)]@cands
       where all ki are finitary with ni possibilities for X(i+k)
    *)
    fun finitarySplits (nil, k, W, f, cands) = cands
      | finitarySplits (NONE::Xs, k, W, f, cands) =
        (* parameter blocks can never be split *)
          finitarySplits (Xs, k+1, W, f, cands)
      | finitarySplits (SOME(X)::Xs, k, W, f, cands) =
          finitarySplits (Xs, k+1, W, f,
			  CSManager.trail (fn () => finitary1 (X, k, W, f,cands)))


    (* finitary ({{G}} V, p, W) = [(k1,n1),...,(km,nm)]
       where ki are indices of splittable variables in G with ni possibilities
       and |G| = p
       and ci are the coverage instructions for the target type of V
    *)
    fun finitary (V, p, W, ci) =
        let
	  val ((V1, s), XsRev) = instEVarsSkip ((V, I.id), p, nil, ci)

	in
	  finitarySplits (XsRev, 1, W, fn () => abstract (V1, s), nil)
	end


    (***********************************)
    (* Contraction based on uniqueness *)
    (***********************************)

    (* eqExp (U[s], U'[s']) = true iff G |- U[s] == U'[s'] : V
       Invariants:
         G |- U[s] : V
         G |- U'[s'] : V
         U[s], U'[s'] contain no EVars
       Note that the typing invariant is satisfied because
       input arguments can only depend on other input arguments,
       but not undetermined or output arguments.
       Similar remarks apply to functions below
    *)
    fun eqExp (Us, Us') = Conv.conv (Us, Us')

    (* eqInpSpine (ms, S1[s1], S2[s2]) = true
       iff U1[s1] == U2[s2] for all input (+) arguments in S1, S2
       according to uniqueness mode spine ms
       Invariants: typing as in eqExp, ms ~ S1, ms ~ S2
    *)
    fun eqInpSpine (ms, (I.SClo(S1,s1'),s1), Ss2) =
          eqInpSpine (ms, (S1, I.comp(s1',s1)), Ss2)
      | eqInpSpine (ms, Ss1, (I.SClo(S2,s2'),s2)) =
          eqInpSpine (ms, Ss1, (S2, I.comp(s2',s2)))
      | eqInpSpine (M.Mnil, (I.Nil,s), (I.Nil,s')) = true
      | eqInpSpine (M.Mapp(M.Marg(M.Plus,_), ms'),
		  (I.App(U,S),s), (I.App(U',S'),s')) =
          eqExp ((U,s), (U',s'))
	  andalso eqInpSpine (ms', (S,s), (S',s'))
      | eqInpSpine (M.Mapp(_, ms'), (I.App(U,S),s), (I.App(U',S'),s')) =
	  (* ignore Star, Minus, Minus1 *)
	  eqInpSpine (ms', (S,s), (S',s'))
      (* other cases should be impossible since spines must match *)

    (* eqInp (G, k, a, S[s], ms) = [k1+k,...,kn+k]
       where k1,...,kn are the deBruijn indices of those declarations
       ki:a @ Si in such that G0 |- Si[^ki+k] == S[s] on all input arguments
       according to mode spine ms.
       Here G = ...kn:a @ Sn, ..., k1:a @ S1, ...
    *)
    fun eqInp (I.Null, k, a, Ss, ms) = nil
      | eqInp (I.Decl(G', I.Dec(_, I.Root (I.Const(a'), S'))), k, a, Ss, ms) =
        (* defined type families disallowed here *)
        if a = a' andalso eqInpSpine (ms, (S', I.Shift(k)), Ss)
	  then k::eqInp (G', k+1, a, Ss, ms)
	else eqInp (G', k+1, a, Ss, ms)
      | eqInp (I.Decl(G', I.Dec(_, I.Pi _)), k, a, Ss, ms) =
          eqInp (G', k+1, a, Ss, ms)
      | eqInp (I.Decl(G', I.NDec _), k, a, Ss, ms) =
	  eqInp (G', k+1, a, Ss, ms)
      | eqInp (I.Decl(G', I.BDec(_, (b, t))), k, a, Ss, ms) =
	  eqInp (G', k+1, a, Ss, ms)
      (* other cases should be impossible *)

    (* contractionCands (G, k) = [[k11,...,k1{n1}],...,[km1,...,km{nm}]]
       where each [kj1,...,kj{nj}] are deBruijn indices in G (counting from right)
       such that kji:aj @ Sji ... kj{nj}:aj @ Sj{nj} and
       Sji...Sj{nj} agree on their input arguments according to the 
       uniqueness mode spine for aj
    *)
    fun contractionCands (I.Null, k) = nil
      | contractionCands (I.Decl(G', I.Dec(_, I.Root (I.Const(a), S))), k) =
        (* defined type families disallowed here *)
        (* using only one uniqueness declaration per type family *)
        (case UniqueTable.modeLookup a
	   of NONE => contractionCands (G', k+1)
            | SOME(ms) => 
	      case eqInp (G', k+1, a, (S, I.Shift(k)), ms)
		of nil => contractionCands (G', k+1)
		 | ns => (k::ns)::contractionCands (G', k+1))
      | contractionCands (I.Decl(G', I.Dec(_, I.Pi _)), k) =
          (* ignore Pi --- contraction cands unclear *)
          contractionCands (G', k+1)
      | contractionCands (I.Decl(G', I.NDec _), k) =
          contractionCands (G', k+1)
      | contractionCands (I.Decl(G', I.BDec(_, (b, t))), k) =
          (* ignore blocks --- contraction cands unclear *)
	  contractionCands (G', k+1)

    (* isolateSplittable ((G0, {{G1}}V, p) = ((G0@G1), V) where |G1| = p
       This isolates the splittable variable G1@G1 from an old-style
       coverage goal ({{G}}V, p)
    *)
    fun isolateSplittable (G, V, 0) = (G, V)
      | isolateSplittable (G, I.Pi((D,_), V'), p) =
          isolateSplittable (I.Decl(G, D), V', p-1)

    (* unifyUOutSpine (ms, S1[s1], S2[s2]) = true
       iff U1[s1] == U2[s2] for all unique output (-1) arguments in S1, S2
       according to uniqueness mode spine ms
       Invariants: the input arguments in S1[s1] and S2[s2] must be known
          to be equal, ms ~ S1, ms ~ S2
       Effect: EVars in S1[s1], S2[s2] are instantianted, both upon
          failure and success
    *)
    fun unifyUOutSpine (ms, (I.SClo(S1,s1'),s1), Ss2) =
          unifyUOutSpine (ms, (S1, I.comp(s1', s1)), Ss2)
      | unifyUOutSpine (ms, Ss1, (I.SClo(S2,s2'),s2)) =
	  unifyUOutSpine (ms, Ss1, (S2, I.comp(s2',s2)))
      | unifyUOutSpine (M.Mnil, (I.Nil,s1), (I.Nil,s2)) = true
      | unifyUOutSpine (M.Mapp(M.Marg(M.Minus1,_),ms'), (I.App(U1,S1),s1), (I.App(U2,S2),s2)) =
          Unify.unifiable (I.Null, (U1,s1), (U2,s2)) (* will have effect! *)
	  andalso unifyUOutSpine (ms', (S1,s1), (S2,s2))
      | unifyUOutSpine (M.Mapp(_,ms'), (I.App(U1,S1),s1), (I.App(U2,S2), s2)) =
	  (* if mode = + already equal by invariant; otherwise ignore *)
          unifyUOutSpine (ms', (S1,s1), (S2,s2))
      (* Nil/App or App/Nil cannot occur by invariants *)

    (* unifyUOuttype (a @ S1, a @ S2) = true
       iff S1 and S2 unify on all unique output (-1) arguments in S1, S2
       according to uniqueness mode declaration for a (both args must have same a)
       Invariants: the input args in S1, S2 must be known to be equal
          and a must have a uniqueness mode
       Effect: Evars may be instantiated by unification
    *)
    fun unifyUOutType (V1, V2) = 
          unifyUOutTypeW (Whnf.whnf (V1, I.id), Whnf.whnf(V2, I.id))
    and unifyUOutTypeW ((I.Root(I.Const(a1),S1),s1), (I.Root(I.Const(a2),S2),s2)) =
        (* a1 = a2 by invariant *)
        let
	  val SOME(ms) = UniqueTable.modeLookup a1 (* must succeed by invariant *)
	in
	  unifyUOutSpine (ms, (S1,s1), (S2,s2))
	end
	(* must be constant-headed roots by invariant *)

    (* unifyUOutEvars (X1, X2) = true
       iff . |- X1 : a @ S1, . |- X2 : a @ S2 and the unique output arguments
       in V1 and V2 unify
       Invariants: the input args in S1, S2, must be known to be equal
         Both types start with the same a, a must have a uniqueness mode
       Effect: Evars may be instantiated by unification
    *)
    fun unifyUOutEVars (SOME(I.EVar(_, G1, V1, _)), SOME(I.EVar(_, G2, V2, _))) =
	  (* G1 = G2 = Null *)
          unifyUOutType (V1, V2)

    (* unifyUOut2 ([X1,...,Xp], k1, k2) = (see unifyOutEvars (X{k1}, X{k2})) *)
    fun unifyUOut2 (XsRev, k1, k2) =
          unifyUOutEVars (List.nth (XsRev, k1-1), List.nth (XsRev, k2-1))

    (* unifyOut1 ([X1,...,Xp], [k1, k2, ..., kn] = true
       if X{k1} "==" X{k2} "==" ... "==" X{kn} according to unifyOutEvars
    *)
    fun unifyUOut1 (XsRev, nil) = true
      | unifyUOut1 (XsRev, k1::nil) = true
      | unifyUOut1 (XsRev, k1::k2::ks) =
          unifyUOut2 (XsRev, k1, k2)
	  andalso unifyUOut1 (XsRev, k2::ks)

    (* unifyOut ([X1,...,Xp], [[k11,...,k1{n1}],...,[km1,...,km{nm}]]) = true
       if unifyOut1 ([X1,...,Xp], [kj1,...,kj{nj}]) for each j
    *)
    fun unifyUOut (XsRev, nil) = true
      | unifyUOut (XsRev, ks::kss) =
          unifyUOut1 (XsRev, ks)
	  andalso unifyUOut (XsRev, kss)

    (* contractAll ({{G}}V, p, ucands) = SOME(V',p')
       iff (V',p') is the result of contracting unique output arguments
           according to contraction candidates ucands
           of variables in G where all input arguments agree
       returns NONE if unique output arguments are non-unifiable
       may be the identity if output arguments are already identity
          or unsolvable constraints during contraction
       Invariants: p = |G| (G contains the splittable variables)
    *)
    fun contractAll (V, p, ucands) =
        let
	  val ((V1, s), XsRev) = instEVars ((V, I.id), p, nil) (* as in splitVar *)
	in
	  if unifyUOut (XsRev, ucands)
	    then SOME (abstract (V1, s)) (* as in splitVar, may raise Constraints.Error *)
	  else NONE			(* unique outputs not simultaneously unifiable *)
	end

    (* contract ({{G}}V0, p, ci, lab) = SOME(V',p')
       iff (V',p') is the result of contracting unique output arguments
           of variables in G where all input arguments agree
       returns NONE if unique output arguments are non-unifiable
       may be the identity if output arguments are already identity
          or unsolvable constraints during contraction
       ci and lab are used for printing
       Invariants: p = |G| (G contains the splittable variables)
    *)
    fun contract (V, p, ci, lab) =
        let
	  val (G, _) = isolateSplittable (I.Null, V, p)	(* ignore body of coverage goal *)
	  val ucands = contractionCands (G, 1)
	  val n = List.length ucands
	  val _ = if n > 0
		    then chatter 6 (fn () => "Found " ^ Int.toString n ^ " contraction "
				    ^ pluralize (n, "candidate") ^ "\n")
		  else ()
	  val VpOpt' = if n > 0
			 then (contractAll (V, p, ucands)
			       handle Constraints.Error _ =>
				      ( chatter 6 (fn () => "Contraction failed due to constraints\n");
				        SOME(V, p) ))
					(* no progress if constraints remain *)
		       else SOME(V, p)	(* no candidates, no progress *)
	  val _ = case VpOpt'
	            of NONE => chatter 6 (fn () => "Case impossible: conflicting unique outputs\n")
		     | SOME(V',p') => chatter 6 (fn () => showPendingGoal (V', p', ci, lab) ^ "\n")
	in
	  VpOpt'
	end

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

    (* cover (V, p, (W, ci), ccs, lab, missing) = missing'
       covers ([(V1,p1),...,(Vi,pi)], (W, ci), ccs, missing) = missing'

       check if Match arguments (+ for input, - for output) in V or all Vi, respectively,
       are covered by clauses ccs, adding omitted cases to missing to yield missing'.

       V = {{G}} {{L}} a @ S where |G| = p and G contains the splittable
       variables while L contains the local parameters

       W are the worlds for type family a
       ci are the cover instructions matching S

       lab is the label for the current goal for tracing purposes
    *)
    fun cover (V, p, wci as (W, ci), ccs, lab, missing) =
        ( chatter 6 (fn () => showPendingGoal (V, p, ci, lab) ^ "\n");
	  cover' (contract(V, p, ci, lab), wci, ccs, lab, missing) )

    and cover' (SOME(V, p), wci as (W, ci), ccs, lab, missing) =
          split (V, p, selectCand (matchDX (I.Null, V, V, p, ci, ccs)), wci, ccs, lab, missing) 
      | cover' (NONE, wci, ccs, lab, missing) =
	(* V is covered by unique output inconsistency *)
	( chatter 6 (fn () => "Covered\n");
	  missing )

    and split (V, p, NONE, wci, ccs, lab, missing) = 
        (* V is covered: return missing patterns from other cases *)
        ( chatter 6 (fn () => "Covered\n");
          missing )
      | split (V, p, SOME(nil), wci as (W, ci), ccs, lab, missing) =
        (* no strong candidates: check for finitary splitting candidates *)
	( chatter 6 (fn () => "No strong candidates---calculating weak candidates\n");
	  splitWeak (V, p, finitary (V, p, W, ci), wci, ccs, lab, missing) )
      | split (V, p, SOME((k,_)::ksn), wci as (W, ci), ccs, lab, missing) =
	(* some candidates: split first candidate, ignoring multiplicities *)
	(* candidates are in reverse order, so non-index candidates are split first *)
	(* splitVar shows splitting as it happens *)
	(case splitVar (V, p, k, wci)
	   of SOME(cases) => covers (cases, wci, ccs, lab, missing)
	    | NONE => (* splitting variable k generated constraints *)
	      split (V, p, SOME (ksn), wci, ccs, lab, missing)) (* try other candidates *)

    and splitWeak (V, p, nil, wci, ccs, lab, missing) =
        ( chatter 6 (fn () => "No weak candidates---case " ^ labToString(lab) ^ " not covered\n");
	  (V,p)::missing )
      | splitWeak (V, p, ksn, wci, ccs, lab, missing) = (* ksn <> nil *)
        (* commit to the minimal candidate, since no constraints can arise *)
	  split (V, p, SOME(findMin ksn::nil), wci, ccs, lab, missing)

    and covers (cases, wci, ccs, lab, missing) =
        ( chatter 6 (fn () => "Found " ^ Int.toString (List.length cases)
		              ^ pluralize (List.length cases, " case") ^ "\n");
	  covers' (cases, 1, wci, ccs, lab, missing) )

    and covers' (nil, n, wci, ccs, lab, missing) =
        ( chatter 6 (fn () => "All subcases of " ^ labToString(lab) ^ " considered\n");
	  missing )
      | covers' ((V,p)::cases', n, wci, ccs, lab, missing) =
          covers' (cases', n+1, wci, ccs, lab, cover (V, p, wci, ccs, Child(lab, n), missing))

    (******************)
    (* Input Coverage *)
    (******************)

    (* constsToTypes [c1,...,cn] = [V1,...,Vn] where ci:Vi.
       Generates coverage clauses from signature.
    *)
    fun constsToTypes (nil) = nil
      | constsToTypes (I.Const(c)::cs') = I.constType(c)::constsToTypes(cs')
      | constsToTypes (I.Def(d)::cs') = I.constType(d)::constsToTypes(cs')

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
    fun checkNoDef (a) =
        (case I.sgnLookup a
           of I.ConDef _ =>
	        raise Error ("Coverage checking " ^ N.qidToString (N.constQid a)
			     ^ ":\ntype family must not be defined.")
            | _ => ())

    (* checkCovers (a, ms) = ()
       checks coverage for type family a with respect to mode spine ms
       Effect: raises Error (msg) otherwise
    *)
    fun checkCovers (a, ms) =
        let
	  val _ = chatter 4 (fn () => "Input coverage checking family " ^ N.qidToString (N.constQid a)
			     ^ "\n")
	  val _ = checkNoDef (a)
	  val _ = Subordinate.checkNoDef (a)
	          handle Subordinate.Error (msg) =>
		    raise Error ("Coverage checking " ^ N.qidToString (N.constQid a) ^ ":\n"
				 ^ msg)
	  val (V0, p) = initCGoal (a)
	  val _ = if !Global.doubleCheck
		    then TypeCheck.typeCheck (I.Null, (V0, I.Uni (I.Type)))
		  else ()
	  val _ = CSManager.reset ()
	  val cIn = inCoverInst ms	(* convert mode spine to cover instructions *)
	  val cs = Index.lookup a	(* lookup constants defining a *)
	  val ccs = constsToTypes cs	(* calculate covering clauses *)
	  val W = W.lookup a		(* world declarations for a; must be defined *)
	  val missing = cover (V0, p, (W, cIn), Input(ccs), Top, nil)
	  val _ = case missing
	            of nil => ()	(* all cases covered *)
		     | _::_ => raise Error ("Coverage error --- " ^ Int.toString (length missing) ^ " missing case(s):\n"
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
	  val SOME(ms) = ModeTable.modeLookup a (* must be defined and well-moded *)
	  val cOut = outCoverInst ms	(* determine cover instructions *)
	  val (V', q) = createCoverClause (G, I.EClo(V, s), 0) (* abstract all variables in G *)
	  val _ = if !Global.doubleCheck
		    then TypeCheck.typeCheck (I.Null, (V', I.Uni (I.Type)))
		  else ()
	  val V0 = createCoverGoal (I.Null, (V', I.id), q, ms) (* replace output by new EVars *)
	  val (V0', p) = abstract (V0, I.id)	(* abstract will double-check *)
	  val W = W.lookup a
	  val missing = cover (V0', p, (W, cOut), Output(V',q), Top, nil)
	  val _ = case missing
	            of nil => ()
		     | _::_ => raise Error ("Output coverage error --- missing cases:\n"
					    ^ missingToString (missing, ms) ^ "\n")
	in
	  ()
	end

(* XXX removed TOmega stuff temporarily since it was confusing my
    searches with identically-named functions *)

    fun coverageCheckCases (w, Cs, G) = ()
  end
end; (* functor Cover *)
