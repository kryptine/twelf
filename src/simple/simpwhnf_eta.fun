(* Weak head-normal forms for simple syntax *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)
(* Modified: Kevin Watkins *)

functor SimpWhnfEta (structure SimpSyn : SIMPSYN) : SIMPWHNF =
struct

  structure SimpSyn = SimpSyn

  open SimpSyn

  (*
     Weak Head-Normal Form (whnf)

     whnf ::= (L, s) | (Pi DP. U, s)
            | (Root(n,S), id) | (Root(c,S), id) | (Root(d,S), id) | (Root(F[s'], S), id)
            | (Root(fgnC,S), id) where fgnC is a foreign constant
            | (Lam D. U, s) | (X, s) where X is uninstantiated, X of base type
                                     during type reconstruction, X might have variable type
            | (FgnExp, id) where FgnExp is a foreign expression

     Normal Form (nf)

	UA ::= L | Pi (DA,P). UA
             | Root(n,SA) | Root(c,SA) | Root(d,SA) | Root(fgnC,SA)
             | Lam DA. UA | FgnExp
	DA ::= x:UA
	SA ::= Nil | App (UA, SA)

     Existential Normal Form (enf)

     Existential normal forms are like normal forms, but also allows
     X[s] where X is uninstantiated with no particular restriction on s
     or type of X.

     An existential normal form is a hereditary weak head-normal form.
  *)

  (* functions previously in the Pattern functor *)
  (* eventually, they may need to be mutually recursive with whnf *)

  (* isPatSub s = B

     Invariant:
     If    G |- s : G' 
     and   s = n1 .. nm ^k
     then  B iff  n1, .., nm pairwise distinct
             and  ni <= k or ni = _ for all 1 <= i <= m
  *)
  fun isPatSub (Shift(k)) = true
    | isPatSub (Dot (Idx (n), s)) = 
        let fun checkBVar (Shift(k)) = (n <= k)
              | checkBVar (Dot (Idx (n'), s)) = 
                  n <> n' andalso checkBVar (s)
              | checkBVar (Dot (Undef, s)) =
		  checkBVar (s)
              | checkBVar _ = false
	in
          checkBVar s andalso isPatSub s
        end
    | isPatSub (Dot (Undef, s)) = isPatSub s
    | isPatSub _ = false

  exception Eta

  (* etaContract (U, s, n) = k'

     Invariant: 
     if   G, V1, .., Vn |- s : G1  and  G1 |- U : V
     then if   lam V1...lam Vn. U[s] =eta*=> k 
	  then k' = k
          and  G |- k' : Pi V1...Pi Vn. V [s]
	  else Eta is raised
	    (even if U[s] might be eta-reducible to some other expressions).
  *)
  (* optimization(?): quick check w/o substitution first *)
  fun etaContract (Root (BVar(k), S), s, n) =
      (case bvarSub (k, s)
	 of Idx (k') => if k' > n
                          then (etaContract' (S, s, n); k'-n)
                        else raise Eta
          | _ => raise Eta)
    | etaContract (Lam (U), s, n) =
        etaContract (U, dot1 s, n+1)
    | etaContract (EClo (U, s'), s, n) =
        etaContract (U, comp (s', s), n)
    | etaContract (EVar (ref (SOME(U)), _), s, n) =
        etaContract (U, s, n)
    | etaContract _ = raise Eta
      (* Should fail: (c@S), (d@S), (F@S), X *)
      (* Not treated (fails): U@S *)
      (* Could weak head-normalize for more thorough checks *)
      (* Impossible: L, Pi D.V *)

  (* etaContract' (S, s, n) = R'

     Invariant:
     If  G |- s : G1    and  G1 |- S : V > W
     then if   S[s] =eta*=> n ; n-1 ; ... ; 1 ; Nil
	  then () 
     else Eta is raised
  *)
  and etaContract' (Nil, s, 0) = ()
    | etaContract' (App(U, S), s, n) =
        if etaContract (U, s, 0) = n
          then etaContract' (S, s, n-1)
        else raise Eta
    | etaContract' (SClo (S, s'), s, n) =
	etaContract' (S, comp (s', s), n)
    | etaContract' _ = raise Eta

  (* dotEta (Ft, s) = s'
       
     Invariant: 
     If   G |- s : G1, V  and G |- Ft : V [s]
     then Ft  =eta*=>  Ft1
     and  s' = Ft1 . s
     and  G |- s' : G1, V
  *)
  fun dotEta (Ft as Idx _, s) = Dot (Ft, s)
    | dotEta (Ft as Exp (U), s) =
      let
        val Ft' = Idx (etaContract (U, id, 0))
                  handle Eta => Ft
      in
        Dot (Ft', s)
      end
    | dotEta (Ft as Undef, s) = Dot (Ft, s)
 

  (* whnfRedex ((U, s1), (S, s2)) = (U', s')

     Invariant:
     If    G |- s1 : G1   G1 |- U : V1,   (U,s1) whnf 
           G |- s2 : G2   G2 |- S : V2 > W2
	   G |- V1 [s1] == V2 [s2] == V : L
     then  G |- s' : G',  G' |- U' : W'
     and   G |- W'[s'] == W2[s2] == W : L
     and   G |- U'[s'] == (U[s1] @ S[s2]) : W
     and   (U',s') whnf

     Effects: EVars may be lowered to base type.
  *)
  fun whnfRedex (Us, (SClo (S, s2'), s2)) =
        whnfRedex (Us, (S, comp (s2', s2)))
    | whnfRedex (Us as (Root R, s1), (Nil, s2)) = Us
    | whnfRedex ((Lam (U1), s1), (App (U2, S), s2)) =
        whnfRedex (whnf (U1, dotEta (frontSub (Exp (U2), s2), s1)), (S, s2))
    | whnfRedex (Us as (Lam _, s1), _) = Us  (* S2[s2] = Nil *)
    | whnfRedex (Us as (EVar _, s1), (Nil, s2)) = Us
  (*| whnfRedex (Us as (FgnExp _, _), _) = Us*)
    (* Other cases impossible since (U,s1) whnf *)

  (* whnfRoot ((H, S), s) = (U', s')

     Invariant:
     If    G |- s : G1      G1 |- H : V
                            G1 |- S : V > W
     then  G |- s' : G'     G' |- U' : W'
     and   G |- W [s] = W' [s'] : L

     Effects: EVars may be instantiated when lowered
  *)
  and whnfRoot ((BVar (k), S), s)   =
      (case bvarSub (k, s)
         of Idx (k) => (Root (BVar (k), SClo (S, s)), id)
          | Exp (U) => whnfRedex (whnf (U, id), (S, s)))
	  (* Undef should be impossible *)
    | whnfRoot ((NSDef (d), S), s) =
      let
        val AbbrevDef (_, _, U) = sgnLookup d
      in
        whnfRedex (whnf (U, id), (S, s))
      end
    (* added case to expand nonstrict foreign constants -kw *)
  (*| whnfRoot ((FgnConst (_, AbbrevDef(_, _, U, _, _)), S), s) =
        whnfRedex (whnf (U, id), (S, s))*)
    | whnfRoot ((H, S), s) =
	(Root (H, SClo (S, s)), id)

  (* whnf (U, s) = (U', s')

     Invariant:
     If    G |- s : G'    G' |- U : V
     then  G |- s': G''   G''|- U' : V'
     and   G |- V [s] == V' [s'] == V'' : L  
     and   G |- U [s] == U' [s'] : V'' 
     and   (U', s') whnf
  *)
  (*
     Possible optimization :
       Define whnf of Root as (Root (n , S [s]), id)
       Fails currently because appendSpine does not necessairly return a closure  -cs
       Advantage: in unify, abstract... the spine needn't be treated under id, but under s
  *)
  and 
    (* simple optimization (C@S)[id] = C@S[id] *)
    (* applied in Twelf 1.1 *)
    (* Sat Feb 14 20:53:08 1998 -fp *)
(*    whnf (Us as (Root _, Shift (0))) = Us*)
    (* commented out, because non-strict definitions slip
       Mon May 24 09:50:22 EDT 1999 -cs  *)
      whnf (Root R, s) = whnfRoot (R, s)
    | whnf (Redex (U, S), s) = whnfRedex (whnf (U, s), (S, s))
    | whnf (Us as (Lam _, s)) = Us
    | whnf (EVar (ref (SOME U), _), s) = whnf (U, s)
    | whnf (Us as (EVar _, s)) = Us
    | whnf (EClo (U, s'), s) = whnf (U, comp (s', s))
  (*| whnf (Us as (FgnExp _, Shift (0))) = Us
    | whnf (Us as (FgnExp (cs, ops), s)) =
        (#map(ops) (fn U => EClo (U, s)), id)*)

  (* expandDef (Root (Def (d), S), s) = (U' ,s')
     
     Invariant:
     If    G |- s : G1     G1 |- S : V > W            ((d @ S), s) in whnf
                           .  |- d = U : V'  
     then  G |- s' : G'    G' |- U' : W'
     and   G |- V' == V [s] : L
     and   G |- W' [s'] == W [s] == W'' : L
     and   G |- (U @ S) [s] == U' [s'] : W'
     and   (U', s') in whnf
  *)
  fun expandDef (Root (Def (d), S), s) = 
        whnfRedex (whnf (constDef (d), id), (S, s))

  (* Invariant:
     
     normalizeExp (U, s) = U'
     If   G |- s : G' and G' |- U : V 
     then U [s] = U'
     and  U' in existential normal form

     If (U, s) contain no existential variables,
     then U' in normal formal
  *)
  fun normalize Us = normalizeExpW (whnf Us)

  and normalizeExpW (U as Root (H, S), s) = (* s = id *)
        Root (H, normalizeSpine (S, s))
    | normalizeExpW (Lam (U), s) = 
        Lam (normalize (U, dot1 s))
    | normalizeExpW (Us as (EVar _, s)) = EClo Us
  (*| normalizeExpW (U as FgnExp (cs, ops), s) =
        #map(ops) (fn U => normalizeExp (U, s))*)

  and normalizeSpine (Nil, s) = 
        Nil 
    | normalizeSpine (App (U, S), s) = 
        App (normalize (U, s), normalizeSpine (S, s))
    | normalizeSpine (SClo (S, s'), s) =
        normalizeSpine (S, comp (s', s))

  (* invert s = s'

     Invariant:
     If   G |- s : G'    (and s patsub)
     then G' |- s' : G
     s.t. s o s' = id  
  *)
  fun invert s =
      let 
	fun lookup (n, Shift _, p) = NONE
	  | lookup (n, Dot (Undef, s'), p) = lookup (n+1, s', p)
	  | lookup (n, Dot (Idx k, s'), p) = 
	    if k = p then SOME n 
	    else lookup (n+1, s', p)
	
	fun invert'' (0, si) = si
	  | invert'' (p, si) = 
	    (case (lookup (1, s, p))
	       of SOME k => invert'' (p-1, Dot (Idx k, si))
	        | NONE => invert'' (p-1, Dot (Undef, si)))
	       
	fun invert' (n, Shift p) = invert'' (p, Shift n)
	  | invert' (n, Dot (_, s')) = invert' (n+1, s')
      in
	invert' (0, s)
      end
  
    
  (* isId s = B
     
     Invariant:
     If   G |- s: G', s weakensub
     then B holds 
          iff s = id, G' = G
  *)
  fun isId' (Shift(k), k') = (k = k')
    | isId' (Dot (Idx(n), s'), k') =
        n = k' andalso isId' (s', k'+1)
    | isId' _ = false
  fun isId s = isId' (s, 0)

end
