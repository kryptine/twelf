(* Simple unifier *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)
(* Modified: Kevin Watkins *)

functor SimpUnify(structure SimpSyn : SIMPSYN
                  structure SimpWhnf : SIMPWHNF
                    sharing SimpWhnf.SimpSyn = SimpSyn
                  structure Trail : TRAIL) : SIMPUNIFY =
struct

  structure SimpSyn = SimpSyn

  open SimpSyn

  exception Unify of string

  datatype Action =
    Instantiate of Exp option ref
  | Add of cnstr list ref
  | Solve of cnstr * Cnstr

  val globalTrail = Trail.trail () : Action Trail.trail
    
  fun undo (Instantiate refU) =
        (refU := NONE)
    | undo (Add (cnstrs as ref(cnstr :: cnstrL))) =
        (cnstrs := cnstrL)
    | undo (Solve (cnstr, Cnstr)) =
        (cnstr := Cnstr)

  fun reset () = Trail.reset globalTrail

  fun mark () = Trail.mark globalTrail

  fun unwind () = Trail.unwind (globalTrail, undo)

  fun addConstraint (cnstrs, cnstr) =
        (cnstrs := cnstr :: (!cnstrs);
         Trail.log (globalTrail, Add (cnstrs)))

  fun solveConstraint (cnstr as ref (Cnstr)) =
        (cnstr := Solved;
         Trail.log (globalTrail, Solve (cnstr, Cnstr)))

  (* Associate a constraint to an expression *)
  (* delayExpW ((U, s), cnstr) = ()

     Invariant: 
     If   G' |- s : G    G |- U : V    (U,s)  in whnf
     then
     the constraint cnstr is added to all the rigid EVar occurrences in U[s]
  *)
  fun delayExpW ((Root (_, S), s), cnstr) =
        (delaySpine ((S, s), cnstr))
    | delayExpW ((Lam (U), s), cnstr) =
        (* was it ever significant that constraints were associated
           with the declaration of the parameter? *)
        (delayExp ((U, dot1 s), cnstr))
    | delayExpW ((EVar (r, cnstrs), s), cnstr) =
        addConstraint(cnstrs, cnstr)
  (*| delayExpW ((FgnExp (cs, ops), s), cnstr) = (* s = id *)
        delayExp ((#toInternal(ops) (), s), cnstr) *)
    (* no other cases by invariant *)

  (* delayExp ((U, s), cnstr) = ()
     as in delayExpCW, except that the argument may not be in whnf 
  *)
  and delayExp (Us, cnstr) =
        delayExpW (SimpWhnf.whnf Us, cnstr)

  (* delaySpine ((S, s), cnstr) = ()

     Invariant: 
     If   G' |- s : G    G |- S : V > W
     then      G  |- S' : V' > W'
     the constraint cnstr is added to all the rigid EVar occurrences in S[s]
  *)
  and delaySpine ((Nil, s), cnstr) = ()
    | delaySpine ((App (U, S), s), cnstr) =
        (delayExp ((U, s), cnstr); delaySpine ((S, s), cnstr))
    | delaySpine ((SClo(S, s'), s), cnstr) =
        delaySpine ((S, comp (s', s)), cnstr)

  local
    val awakenCnstrs = ref nil : cnstr list ref
  in
    fun resetAwakenCnstrs () = (awakenCnstrs := nil)

    fun nextCnstr () = 
          case !awakenCnstrs
            of nil => NONE
             | (ref Cnstr :: cnstrL) => 
                 (awakenCnstrs := cnstrL; SOME(Cnstr))

    (* Instantiating EVars  *)
    fun instantiateEVar (refU, V, cnstrL) =
          (refU := SOME(V);
           Trail.log (globalTrail, Instantiate (refU));
           awakenCnstrs := cnstrL @ !awakenCnstrs)
  end  (* local *)

  (* intersection (s1, s2) = s'
     s' = s1 /\ s2 (see JICSLP'96)
       
     Invariant: 
     If   G |- s1 : G'    s1 patsub
     and  G |- s2 : G'    s2 patsub
     then G' |- s' : G'' for some G''  
     and  s' weaksub
  *)
  fun intersection (Dot (Idx (k1), s1), Dot (Idx (k2), s2)) = 
        if (k1 = k2) then dot1 (intersection (s1, s2))
        else comp (intersection (s1, s2), shift)
    | intersection (s1 as Dot _, Shift (n2)) =
	intersection (s1, Dot (Idx (n2+1), Shift (n2+1)))
    | intersection (Shift (n1), s2 as Dot _) = 
        intersection (Dot (Idx (n1+1), Shift (n1+1)), s2)
    | intersection (Shift _ , Shift _) = id
        (* both substitutions are the same number of shifts by invariant *)
      (* all other cases impossible for pattern substitutions *)


  (* weakenSub (G1, s, ss) = w'
     
     Invariant:
     If    G |- s : G1       (* s patsub *)
     and   G2 |- ss : G      (* ss strsub *)
     then  G1 |- w' : G1'    (* w' weaksub *)
  *)

  fun weakenSub (Shift n, Shift _) = id
    | weakenSub (Shift 0, Dot (Undef, ss)) =
        comp (weakenSub (Shift 0, ss), shift)
    | weakenSub (Shift 0, Dot (_, ss)) =
        dot1 (weakenSub (Shift 0, ss))
    | weakenSub (Shift n, Dot (_, ss)) =
        weakenSub (Shift (n-1), ss)
    | weakenSub (Dot (Idx n, s'), ss) =
        (case bvarSub (n, ss)
           of Undef => comp (weakenSub (s', ss), shift)
            | Idx _ => dot1 (weakenSub (s', ss)))
         (* no other cases, ss is strsub *)
    | weakenSub (Dot (Undef, s'), ss) =
        comp (weakenSub (s', ss), shift)

  (* prune (G, (U, s), ss, rOccur) = U[s][ss]

     G |- U : V    G' |- s : G  (G' |- U[s] : V[s])
     G'' |- ss : G'

     Effect: prunes EVars in U[s] according to ss
             raises Unify if U[s][ss] does not exist, or rOccur occurs in U[s]
  *)
  fun pruneExp  (Us, ss, rOccur, prunable) =
        pruneExpW (SimpWhnf.whnf Us, ss, rOccur, prunable)
  and pruneExpW ((Lam (V), s), ss, rOccur, prunable) =
	Lam (pruneExp ((V, dot1 s), dot1 ss, rOccur, prunable))
    | pruneExpW ((Root (H, S), s (* = id *)), ss, rOccur, prunable) = 
        Root (pruneHead (H, ss, rOccur, prunable),
              pruneSpine ((S, s), ss, rOccur, prunable))
    | pruneExpW ((X as EVar (r, cnstrs), s), ss, rOccur, prunable) = 
        if (rOccur = r) then raise Unify "Variable occurrence"
        else if SimpWhnf.isPatSub (s) then
             let
               val w = weakenSub (s, ss)
             in
               if SimpWhnf.isId w
		 then EClo (X, comp (s, ss))
               else if prunable then
                 let
                   val Y = newEVar ()
                   val Yw = EClo (Y, w)
                   val _ = instantiateEVar (r, Yw, !cnstrs)
                 in
                   EClo (Yw, comp (s, ss))
                 end
               else raise Unify "Not prunable"
             end
             else (* s1 not patsub *)
               (
                EClo (X, pruneSub (s, ss, rOccur))
                handle Unify (msg) => 
                  if prunable then
                    let 
                      val Y = newEVar ()
                      val _ = addConstraint (cnstrs, ref (Eqn (EClo (X, s),
                                                               EClo (Y, SimpWhnf.invert ss))))
                    in
                      Y
                    end
                  else raise Unify (msg)
               )
  (*| pruneExpW ((FgnExp (_, ops), s), ss, rOccur, prunable) =
        #map(ops) (fn U => pruneExp ((U, s), ss, rOccur, prunable))*)
      (* other cases impossible since (U,s1) whnf *)
  and pruneSpine ((Nil, s), ss, rOccur, prunable) = Nil
    | pruneSpine ((App (U, S), s), ss, rOccur, prunable) = 
        App (pruneExp ((U, s), ss, rOccur, prunable),
             pruneSpine ((S, s), ss, rOccur, prunable))
    | pruneSpine ((SClo (S, s'), s), ss, rOccur, prunable) = 
        pruneSpine ((S, comp (s', s)), ss, rOccur, prunable)
  and pruneHead (BVar k, ss, rOccur, prunable) = 
      (case (bvarSub (k, ss))
         of Undef => raise Unify "Parameter dependency"
          | Idx k' => BVar k')
    | pruneHead (H as Const _, ss, rOccur, prunable) = H
    | pruneHead (H as Skonst _, ss, rOccur, prunable) = H
    | pruneHead (H as Def _, ss, rOccur, prunable) = H
  (*| pruneHead (G, H as FgnConst _, ss, rOccur, prunable) = H*)
   (* pruneSub never allows pruning *)
  and pruneSub (Shift (0), ss, rOccur) =
        if defined(ss)
          then ss
        else raise Unify "Not prunable"
    | pruneSub (Shift (n), Dot (_, s), rOccur) =
        pruneSub (Shift (n-1), s, rOccur)
    | pruneSub (Shift (n), Shift (m), rOccur) =
        Shift (n+m)
    | pruneSub (Dot (Idx (n), s'), ss, rOccur) =
        (case bvarSub (n, ss)
           of Undef => raise Unify "Not prunable"
            | Ft => Dot (Ft, pruneSub (s', ss, rOccur)))
    | pruneSub (Dot (Exp (U), s'), ss, rOccur) =
	(* below my raise Unify *)
	Dot (Exp (pruneExp ((U, id), ss, rOccur, false)),
	     pruneSub (s', ss, rOccur))
    (* pruneSub (G, Dot (Undef, s), ss, rOccur) is impossible *)
    (* By invariant, all EVars X[s] are such that s is defined everywhere *)
    (* Pruning establishes and maintains this invariant *)

  (* unifyExpW (G, (U1, s1), (U2, s2)) = ()
     
     Invariant:
     If   G |- s1 : G1   G1 |- U1 : V1    (U1,s1) in whnf
     and  G |- s2 : G2   G2 |- U2 : V2    (U2,s2) in whnf 
     and  G |- V1 [s1] = V2 [s2]  : L    (for some level L)
     then if   there is an instantiation I :  
               s.t. G |- U1 [s1] <I> == U2 [s2] <I>
          then instantiation is applied as effect, () returned
          else exception Unify is raised
     Other effects: EVars may be lowered
                    constraints may be added for non-patterns
  *)
  and (*unifyExpW (Us1 as (FgnExp (_, ops), _), Us2) =
      (case (#unifyWith(ops) (EClo Us2))
           of (Succeed residualL) =>
              let
                fun execResidual (Assign (G, EVar(r, _, _, cnstrs), W, ss)) =
                  let
                    val W' = pruneExp (G, (W, id), ss, r, true)
                          in
                            instantiateEVar (r, W', !cnstrs)
                          end
                      | execResidual (Delay (U, cnstr)) =
                          delayExp ((U, id), cnstr)
                  in
                    List.app execResidual residualL
                  end
              | Fail => raise Unify "Foreign Expression Mismatch")

    | unifyExpW (G, Us1, Us2 as (FgnExp (_, ops), _)) =
          (case (#unifyWith(ops) (G, EClo Us1))
             of (Succeed opL) =>
                  let
                    fun execOp (Assign (G, EVar(r, _, _, cnstrs), W, ss)) =
                          let
                            val W' = pruneExp (G, (W, id), ss, r, true)
                          in
                            instantiateEVar (r, W', !cnstrs)
                          end
                      | execOp (Delay (U, cnstr)) = delayExp ((U, id), cnstr)
                  in
                    List.app execOp opL
                  end
              | Fail => raise Unify "Foreign Expression Mismatch")

    |*) unifyExpW (Us1 as (Root (H1, S1), s1), Us2 as (Root (H2, S2), s2)) =
	(* s1 = s2 = id by whnf *)
        (* order of calls critical to establish unifySpine invariant *)
        (case (H1, H2) of 
	   (BVar(k1), BVar(k2)) => 
	     if (k1 = k2) then unifySpine ((S1, s1), (S2, s2))
	     else raise Unify "Bound variable clash"
         | (Const(c1), Const(c2)) => 	  
             if (c1 = c2) then unifySpine ((S1, s1), (S2, s2))
             else raise Unify "Constant clash"
         | (Skonst(c1), Skonst(c2)) => 	  
	     if (c1 = c2) then unifySpine ((S1, s1), (S2, s2))
             else raise Unify "Skolem constant clash"
         | (Def (d1), Def (d2)) =>
             if (d1 = d2) then (* because of strict *) 
               unifySpine ((S1, s1), (S2, s2))
             else unifyExpW (SimpWhnf.expandDef (Us1),
                             SimpWhnf.expandDef (Us2))
         | (Def (d1), _) =>
             unifyExpW (SimpWhnf.expandDef Us1, Us2)
         | (_, Def(d2)) =>
             unifyExpW (Us1, SimpWhnf.expandDef Us2)
       (*| (FgnConst (cs1, ConDec (n1, _, _, _, _)), FgnConst (cs2, ConDec (n2, _, _, _, _))) =>
             (* we require unique string representation of external constants *)
             if (cs1 = cs2) andalso (n1 = n2) then ()
             else raise Unify "Foreign Constant clash"
         | (FgnConst (cs1, ConDef (n1, _, W1, _, _)), FgnConst (cs2, ConDef (n2, _, V, W2, _))) =>
             if (cs1 = cs2) andalso (n1 = n2) then ()
             else unifyExp (G, (W1, s1), (W2, s2))
         | (FgnConst (_, ConDef (_, _, W1, _, _)), _) =>
             unifyExp (G, (W1, s1), Us2)
         | (_, FgnConst (_, ConDef (_, _, W2, _, _))) =>
             unifyExp (G, Us1, (W2, s2))*)
         | _ => raise Unify "Head mismatch")

    | unifyExpW ((Lam (U1), s1), (Lam (U2), s2)) =           
        unifyExp ((U1, dot1 s1),(U2, dot1 s2))

    | unifyExpW ((Lam (U1), s1), (U2, s2)) = (*raise Fail "Eta violation"*)
	(* ETA: can't occur if eta expanded*)
	unifyExp ((U1, dot1 s1),
                  (Redex (EClo (U2, shift), App (Root (BVar (1), Nil), Nil)), dot1 s2))
        (* for rhs:  (U2[s2])[^] 1 = U2 [s2 o ^] 1 = U2 [^ o (1. s2 o ^)] 1
                     = (U2 [^] 1) [1.s2 o ^] *) 

    | unifyExpW ((U1, s1), (Lam (U2), s2)) = (*raise Fail "Eta violation"*)
        (* Cannot occur if expressions are eta expanded *)
	unifyExp ((Redex (EClo (U1, shift), App (Root (BVar (1), Nil), Nil)), dot1 s1),
                  (U2, dot1 s2))  
	(* same reasoning holds as above *)

    | unifyExpW (Us1 as (U1 as EVar(r1, cnstrs1), s1),
                 Us2 as (U2 as EVar(r2, cnstrs2), s2)) =
        (* postpone, if s1 or s2 are not patsub *)
        if r1 = r2 then 
          if SimpWhnf.isPatSub(s1) then 
            if SimpWhnf.isPatSub(s2) then
              let
                val s' = intersection (s1,s2)	(* compute s' directly? *)
              in
                instantiateEVar (r1, EClo (newEVar (), s'), !cnstrs1)
              end
            else addConstraint (cnstrs2, ref (Eqn (EClo Us2, EClo Us1)))
          else addConstraint (cnstrs1, ref (Eqn (EClo Us1, EClo Us2)))
        else
          if SimpWhnf.isPatSub(s1) then 
            let
              val ss1 = SimpWhnf.invert s1
              val U2' = pruneExp (Us2, ss1, r1, true)   (* prunable set to true -cs *)
            in
              (* instantiateEVar (r1, EClo (U2, comp(s2, ss1)), !cnstrs1) *)
              (* invertExpW (Us2, s1, ref NONE) *)
              instantiateEVar (r1, U2', !cnstrs1)
            end
          else if SimpWhnf.isPatSub(s2) then 
            let
              val ss2 = SimpWhnf.invert s2
              val U1' = pruneExp (Us1, ss2, r2, true)
            in
              (* instantiateEVar (r2, EClo (U1, comp(s1, ss2)), !cnstr2) *)
              (* invertExpW (Us1, s2, ref NONE) *)
              instantiateEVar (r2, U1', !cnstrs2)
            end
          else addConstraint (cnstrs1, ref (Eqn (EClo Us1, EClo Us2)))

    | unifyExpW (Us1 as (EVar(r, cnstrs), s), Us2 as (U2,s2)) =
        if SimpWhnf.isPatSub(s) then
	  let val ss = SimpWhnf.invert s
	      val U2' = pruneExp (Us2, ss, r, true) (* could raise occurs-check *)
	  in
	    (* instantiateEVar (r, EClo (U2, comp(s2, ss)), !cnstrs) *)
	    (* invertExpW (Us2, s, r) *)
	    instantiateEVar (r, U2', !cnstrs)
	  end
	else 
          addConstraint (cnstrs, ref (Eqn (EClo Us1, EClo Us2)))

    | unifyExpW (Us1 as (U1,s1), Us2 as (EVar (r, cnstrs), s)) =
	if SimpWhnf.isPatSub(s) then 
	  let val ss = SimpWhnf.invert s
	      val U1' = pruneExp (Us1, ss, r, true)
	  in
	    (* instantiateEVar (r, EClo (U1, comp(s1, ss)), !cnstrs) *)
	    (* invertExpW (Us1, s, r) *)
	    instantiateEVar (r, U1', !cnstrs)
	  end
        else
          addConstraint (cnstrs, ref (Eqn (EClo Us1, EClo Us2)))

    | unifyExpW (Us1, Us2) = 
        raise Unify ("Expression clash")

  (* covers most remaining cases *)
  (* the cases for EClo or Redex should not occur because of whnf invariant *)

  (* unifyExp (G, (U1, s1), (U2, s2)) = ()
     as in unifyExpW, except that arguments may not be in whnf 
  *)
  and unifyExp (Us1 as (E1,s1), Us2 as (E2,s2)) = 
        unifyExpW (SimpWhnf.whnf Us1, SimpWhnf.whnf Us2)

  (* unifySpine (G, (S1, s1), (S2, s2)) = ()
     
     Invariant:
     If   G |- s1 : G1   G1 |- S1 : V1 > W1 
     and  G |- s2 : G2   G2 |- S2 : V2 > W2 
     and  G |- V1 [s1] = V2 [s2]  : L    (for some level L)
     and  G |- W1 [s1] = W2 [s2]  
     then if   there is an instantiation I :
               s.t. G |- S1 [s1] <I> == S2 [s2] <I> 
          then instantiation is applied as effect, () returned
	  else exception Unify is raised
     Other effects: EVars may be lowered,
                    constraints may be added for non-patterns
  *)
  and unifySpine ((Nil,_), (Nil,_)) = ()
    | unifySpine ((SClo (S1, s1'), s1), Ss) = unifySpine ((S1, comp (s1', s1)), Ss)
    | unifySpine (Ss, (SClo (S2, s2'), s2)) = unifySpine (Ss, (S2, comp (s2', s2)))
    | unifySpine ((App (U1, S1), s1), (App (U2, S2), s2)) = 
        (unifyExp ((U1, s1), (U2, s2)) ; 
         unifySpine ((S1, s1), (S2, s2)))
    (* Nil/App or App/Nil cannot occur by typing invariants *)

  fun unify1W (Us1, Us2) =
        (unifyExpW (Us1, Us2); awakeCnstr (nextCnstr ()))

  and unify1 (Us1, Us2) =
        (unifyExp (Us1, Us2); awakeCnstr (nextCnstr ()))

  and awakeCnstr (NONE) = ()
    | awakeCnstr (SOME(Solved)) = awakeCnstr (nextCnstr ())
    | awakeCnstr (SOME(Eqn (U1, U2))) = unify1 ((U1, id), (U2, id))
  (*| awakeCnstr (SOME(FgnCnstr (cs, ops))) =
        if (#awake(ops)()) then ()
        else raise Unify "Foreign constraint violated"*)

  fun unifyW (Us1, Us2) =
        (resetAwakenCnstrs (); unify1W (Us1, Us2))

  fun unify (Us1, Us2) =
        (resetAwakenCnstrs (); unify1 (Us1, Us2))

  fun unifiable (Us1, Us2) =
        (unify (Us1, Us2); true)
        handle Unify _ => false

end
