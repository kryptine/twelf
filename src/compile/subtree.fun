(* Substitution Tree indexing *)
(* Author: Brigitte Pientka *)
functor SubTree (structure IntSyn' : INTSYN
                 structure CompSyn' : COMPSYN
		   sharing CompSyn'.IntSyn = IntSyn'
 	         structure Whnf : WHNF
		   sharing Whnf.IntSyn = IntSyn'
		 structure Unify : UNIFY
		   sharing Unify.IntSyn = IntSyn'
		 structure Print : PRINT
		   sharing Print.IntSyn = IntSyn'
		    (* CPrint currently unused *)
		 structure CPrint : CPRINT 
		   sharing CPrint.IntSyn = IntSyn'
		   sharing CPrint.CompSyn = CompSyn'
		     (* unused *)
		structure Formatter : FORMATTER
		  sharing Print.Formatter = Formatter
		     (* unused *)
		structure Names: NAMES  
		  sharing Names.IntSyn = IntSyn'
		 structure CSManager : CS_MANAGER
		   sharing CSManager.IntSyn = IntSyn'
 	         structure RBSet : RBSET)
  : SUBTREE =
struct
  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'
  structure RBSet = RBSet

  type nvar = int      (* index for normal variables *)
  type bvar = int      (* index for bound variables *)
  type bdepth = int    (* depth of locally bound variables *)

  (* A substitution tree is defined as follows:
     Node := Leaf (ns, G, sgoal) | Node(ns, Set of Nodes)
     normal linear modal substitutions ns := . | R/n, ns

   For each node we have the following invariant:
        S |- ns : S'    i.e. ns substitutes for internal variables
        G'|- as : G     i.e. as substitutes for assignable variables
        G |- qs : G     i.e. qs substitutes for modal variables 
                             occuring in the query term
  *) 
 
  type normalSubsts =  IntSyn.Exp RBSet.ordSet  (* key = int = bvar *) 

  datatype AssSub = Assign of (IntSyn.Dec IntSyn.Ctx * IntSyn.Exp)
  type assSubsts = AssSub RBSet.ordSet          (* key = int = bvar *) 

  type querySubsts = (IntSyn.Dec IntSyn.Ctx * IntSyn.Exp) RBSet.ordSet 

  datatype Cnstr = Eqn of IntSyn.Dec IntSyn.Ctx * IntSyn.Exp * IntSyn.Exp
  type cnstrSubsts = IntSyn.Exp RBSet.ordSet    (* key = int = bvar *)   

  datatype CGoal = CGoals of CompSyn.AuxGoal * IntSyn.cid * CompSyn.Conjunction * int (* cid of clause *)
    
  datatype Tree = 
    Leaf of normalSubsts  * IntSyn.Dec IntSyn.Ctx * CGoal
  | Node of normalSubsts  * Tree RBSet.ordSet

   type candidate = (assSubsts * normalSubsts * cnstrSubsts * Cnstr * IntSyn.Dec IntSyn.Ctx * CGoal)

   (* Initialization of substitutions *)
   val nid         : unit -> normalSubsts = RBSet.new 
   val assignSubId : unit -> assSubsts = RBSet.new 
   val cnstrSubId  : unit -> cnstrSubsts = RBSet.new   
   val querySubId  : unit -> querySubsts = RBSet.new   

   (* Identity substitution *)
   fun isId s = RBSet.isEmpty s

   (* Initialize substitution tree *)
   fun makeTree () = ref (Node (nid (), RBSet.new())) 

   (* Test if node has any children *)
   fun noChildren C = RBSet.isEmpty C


  (* Index array                             
   
   Invariant: 
   For all type families  a  indexArray = [a1,...,an]
   where a1,...,an is a substitution tree consisting of all constants 
   for target family ai

   *)
  val indexArray = Array.tabulate (Global.maxCid, (fn i => (ref 0, makeTree ())));

  local

    structure I = IntSyn
    structure C = CompSyn
    structure S = RBSet

    exception Error of string
    
    exception Assignment of string

    exception Generalization of string   

    (* Auxiliary functions *)
    fun cidFromHead (I.Const c) = c
      | cidFromHead (I.Def c) = c

    fun dotn (0, s) = s
      | dotn (i, s) = dotn (i-1, I.dot1 s)

    fun compose'(IntSyn.Null, G) = G
      | compose'(IntSyn.Decl(G, D), G') = IntSyn.Decl(compose'(G, G'), D)
      
    fun shift (IntSyn.Null, s) = s
      | shift (IntSyn.Decl(G, D), s) = I.dot1 (shift(G, s))

    fun raiseType (I.Null, U) = U
      | raiseType (I.Decl(G, D), U) = I.Lam(D, raiseType (G, U))

   (* 
     Linear normal higher-order patterns
           p ::= n | Root(c, S) | Root(b, S) | Lam (D, p)

	         where n is a linear bound "normalized" variable 	

          SP ::= p ; S | NIL

     Context 
        G : context for bound variables (bvars)
            (type information is stored in the context)
        G ::= . | G, x : A

        S : context for linear normalized bound variables (nvars)
            (no type information is stored in the context)
            (these are the types of the variables definitions)
        S ::= . | S, n 

     Templates: G ; S |- p 
     Substitutions: G ; S |- nsub : S'

    Let s is a substitution for normalized bound variables (nvars)
    and nsub1 o nsub2 o .... o nsubn = s, s.t.  
     G, S_2|- nsub1 : S_1 
     G, S_3|- nsub2 : S_2
      ....
     G |- nsubn : S_n
      . ; G |- s : G, S_1 

    A term U can be decomposed into a term p together with a sequenence of
    substitutions s1, s2, ..., sn such that s1 o s2 o .... o sn = s
    and the following holds:
    
    If    G |- U  

    then 

       G, S |- p   

        G |- s : G, S
 
        G |- p[s]     and p[s] = U

   In addition: 
   all expressions in the index are linear, i.e.
   an expression is first linearized before it is inserted into the index
   (this makes retrieving all axpressions from the index which unify with 
    a given expression simpler, because we can omit the occurs check)
   
   *)


  (* ---------------------------------------------------------------*)   

  (* nctr = |D| =  #normal variables *)
   val nctr = ref 1
    
   fun newNVar () =
     (nctr := !nctr + 1; 
      I.NVar(!nctr))
  
     
   fun eqHeads (I.Const k, I.Const k') =  (k = k')
     | eqHeads (I.BVar k, I.BVar k') = (k = k')
     | eqHeads (I.Def k, I.Def k') = (k = k')
     | eqHeads (_, _) = false

   (* most specific linear common generalization *)

   (* compatible (T, U) = (C, rho_u', rho_t') opt
    if
       U, T are both in normal form
       U and T share at least the top function symbol 
   then 
     C[rho_u'] = U and C[rho_t'] = T 
   *)
   fun compatible (T, U, rho_t, rho_u) = 
     let
       fun genExp (b, T as I.NVar n, U as I.Root(H, S)) =  
	 (S.insert rho_u (n, U); T)
	 | genExp (b, T as I.Root(H1, S1), U as I.Root(H2, S2)) =  
	 if eqHeads(H1, H2) 
	   then
	     I.Root(H1, genSpine(false, S1, S2))
	  else
	    (if b 
	       then 
		 raise Generalization "Top-level function symbol not shared"
	     else 
	       (S.insert rho_t (!nctr+1, T);
		S.insert rho_u (!nctr+1, U);
		newNVar()))
	 | genExp (b, I.Lam(D1 as I.Dec(_,A1), T1), I.Lam(D2 as I.Dec(_, A2), U2)) = 
	   (* by invariant A1 = A2 *)
	     I.Lam(D1, genExp (false, T1,  U2)) 
	
	 (* cases for foreign expressions to be added *)
	 | genExp (b, T, U) =
         if b 
	   then 
	     raise Generalization "Top-level function symbol not shared"
	 else 
	   (* U = EVar, EClo *)
	   (S.insert rho_t (!nctr+1, T);
	    S.insert rho_u (!nctr+1, U);
	    newNVar ())
       and genSpine (b, I.Nil, I.Nil) = I.Nil
	 | genSpine (b, I.App(T, S1), I.App(U, S2)) = 
	 I.App(genExp (false, T, U), genSpine (false, S1, S2))
    in 
      SOME(genExp (true, T, U))
      handle Generalization msg => NONE
    end 

  (* compatibleSub(nsub_t, nsub_e) = (sg, rho_t, rho_e) opt  
   
   if dom(nsub_t) <= dom(nsub_e) 
      codom(nsub_t) : linear hop in normal form (may contain normal vars)
      codom(nsub_e) : linear hop in normal form (does not contain normal vars)
   then      
     nsub_t = [rho_t]sg
     nsub_e = [rho_e]sg

    G_e, Glocal_e |- nsub_e : Sigma
    G_t, Glocal_t |- nsub_t : Sigma'
    Sigma' <= Sigma 
 
    Glocal_e ~ Glocal_t  (have approximately the same type)

   *)
  fun compatibleSub (nsub_t, nsub_e) = 
    let
      val (sg, rho_t, rho_e) = (nid(), nid (), nid ()) 
     (* by invariant rho_t = empty, since nsub_t <= nsub_e *)
      val _ =  S.forall nsub_e
	(fn (nv, E) => 
	 (case (S.lookup nsub_t nv)
	    of SOME (T) =>     (* by invariant Glocal_e ~ Glocal_t, 
				therefore T and E have the same approximate type A *) 
	      (case compatible (T, E, rho_t, rho_e)
		 of NONE => (S.insert rho_t (nv, T);
			     S.insert rho_e (nv, E))
	       | SOME(T') => S.insert sg (nv, T')) 
	  | NONE => S.insert rho_e (nv, E)))
    in 
      if isId(sg)
	then NONE
      else 	
	 SOME(sg, rho_t, rho_e)
    end

  (* mkNode (N, sg, r1, (G, RC), r2) = N'    *)
  fun mkNode (Node(_, Children), sg, rho1, GR as (G, RC), rho2) = 
      let
	val c = S.new()
      in 
	S.insertList c [(1, Node(rho1, Children)), 
				(2, Leaf(rho2, G, RC))];
       Node(sg, c)
      end 
    | mkNode (Leaf(_, G1, RC1), sg, rho1, GR as (G2, RC2), rho2) = 
      let
	val c = S.new()
      in 
	S.insertList c [(1, Leaf(rho1, G1, RC1)), 
			(2, Leaf(rho2, G2, RC2))];
	Node(sg, c)
      end 


  (* Insertion *)
  (* compareChild (children, (n, child), n, n', (G, R)) = ()
    
   *)
  fun compareChild (children, (n, child), nsub_t, nsub_e, GR as (G_clause2, Res_clause2)) = 
    (case compatibleSub (nsub_t, nsub_e) of
       NONE => (S.insert children (n+1, Leaf(nsub_e, G_clause2, Res_clause2)))
     | SOME(sg, rho1, rho2) => 
	 (if isId rho1 then
	   if isId rho2 
	     then (* sg = nsub_t = nsub_e *)
	       (S.insertShadow children (n, mkNode(child, sg, rho1, GR, rho2)))
	   else 
	     (* sg = nsub_t and nsub_e = sg o rho2 *)
	     (S.insertShadow children (n, insert (child, rho2, GR)))
	 else 		   
	   (S.insertShadow children (n, mkNode(child, sg, rho1, GR, rho2)))))

  (* insert (N, nsub_e, (G, R2)) = N'

     if s is the substitution in node N
        G |- nsub_e : S and 
    G, S' |- s : S
    then 
     N' contains a path n_1 .... n_n s.t. 
     [n_n] ...[n_1] s = nsub_e 
  *)
  and insert (N as Leaf (nsub_t, G_clause1, R1), nsub_e, GR as (G_clause2, R2)) = 
    (case compatibleSub(nsub_t, nsub_e) of
       NONE => raise Error "Leaf is not compatible substitution r"
     | SOME(sg, rho1, rho2) => mkNode (N, sg, rho1, GR, rho2))
       
    | insert (N as Node(_, children), nsub_e, GR as (G_clause2, RC)) = 
       if noChildren children 
	 then 
	   (* initial *)
	   (S.insert children (1, (Leaf (nsub_e, G_clause2, RC))); N)
       else 	 
	 (case (S.last children) 
	    of (n, child as Node(nsub_t, children')) => 
	      (compareChild (children, (n, child), nsub_t, nsub_e, GR); N)
          | (n, child as Leaf(nsub_t, G1, RC1)) => 
	      (compareChild (children, (n, child), nsub_t,  nsub_e, GR); N))


  (* retrieval (U,s)
     retrieves all clauses which unify with (U,s)
     
     backtracking implemented via SML failure continuation 

   *)
  fun normalizeNExp (I.NVar n, csub) = 
      let
	val A = I.newAVar ()
      in 
	S.insert csub (n, A); 
	A
      end 
    | normalizeNExp (I.Root (H, S), nsub) = 
	 I.Root(H, normalizeNSpine (S, nsub))
    | normalizeNExp (I.Lam (D, U), nsub) = 
	 I.Lam (D, normalizeNExp (U, nsub))
    | normalizeNExp (I.Pi((D, P), U), nsub) = 
	 (* cannot happen -bp *)
	 I.Pi ((D, P), normalizeNExp (U, nsub))

  and normalizeNSpine (I.Nil, _) = I.Nil
    | normalizeNSpine (I.App (U, S), nsub) = 
    I.App(normalizeNExp (U, nsub), normalizeNSpine (S, nsub))
   
  (* assign (G, Us1, U2, nsub_goal, asub, csub, cnstr) = cnstr 
   if G = local assumptions, G' context of query
      G1 |- U1 : V1 
     G', G  |- s1 : G1
     G', G  |- U1[s1]     and s1 is an explicit substitution
     
      G2 |- U2 : V2
  G', G  |- asub' : G2 and asub is a assignable substitution 

      U2 is eta-expanded
   then 
   G2, N |- cnstr 
      G2 |- csub : N
      G2 |- cnstr[csub]

      G  |- nsub_goal : N      
     *) 

  fun assign (Glocal_u1, Us1, U2, nsub_goal, asub, csub, cnstr) = 
    let 
      val depth = I.ctxLength Glocal_u1
      fun assignHead (depth, Glocal_u1, Us1 as (I.Root (H1, S1), s1), U2 as I.Root (H2, S2), cnstr) = 
	  (case (H1, H2) 
	     of (I.Const(c1), I.Const(c2)) => 
	        if (c1 = c2) 
		  then assignSpine (depth, Glocal_u1, (S1, s1), S2, cnstr)
		else raise Assignment "Constant clash"		 
	     | (I.Skonst(c1), I.Skonst(c2)) => 	  
  	       if (c1 = c2) 
		 then assignSpine (depth, Glocal_u1, (S1, s1), S2, cnstr)
	       else raise Assignment "Skolem constant clash"
	     | (I.Def d1, _) => assignExp (depth, Glocal_u1, Whnf.expandDef Us1, U2, cnstr)
	     | (I.FgnConst (cs1, I.ConDec (n1, _, _, _, _, _)), I.FgnConst (cs2, I.ConDec (n2, _, _, _, _, _))) =>
    	       (* we require unique string representation of external constants *)
	       if (cs1 = cs2) andalso (n1 = n2) then cnstr
	       else raise Assignment "Foreign Constant clash"
	     | (I.FgnConst (cs1, I.ConDef (n1, _, _, W1, _, _)), I.FgnConst (cs2, I.ConDef (n2, _, _, V, W2, _))) =>    
	       (if (cs1 = cs2) andalso (n1 = n2) then cnstr
		else assignExp (depth, Glocal_u1, (W1, s1), W2, cnstr))
	     | (I.FgnConst (_, I.ConDef (_, _, _, W1, _, _)), _) => assignExp (depth, Glocal_u1, (W1, s1), U2, cnstr)
	     | (_, I.FgnConst (_, I.ConDef (_, _, _, W2, _, _))) => assignExp (depth, Glocal_u1, Us1, W2, cnstr)           
	     | (_, _) => (raise Assignment ("Head mismatch ")))

      and assignExpW (depth, Glocal_u1, (I.Uni L1, s1), I.Uni L2, cnstr) = cnstr (* L1 = L2 by invariant *)
	| assignExpW (depth, Glocal_u1, Us1, I.NVar n, cnstr) =  
	  (S.insert nsub_goal (n, (Glocal_u1, I.EClo(Us1)));
	   cnstr)	
	| assignExpW (depth, Glocal_u1, Us1 as (I.Root (H1, S1), s1), U2 as I.Root (H2, S2), cnstr) =
	  (case H2 
	     of I.BVar(k2) => 
	       if (k2 > depth) 
		 then 	    
		   (* BVar(k2) stands for an existential variable *)	
		   (* S2 is an etaSpine by invariant *)
		    (S.insert asub ((k2 - I.ctxLength(Glocal_u1)), Assign(Glocal_u1, I.EClo(Us1))); 
		    cnstr)
	       else 
		 (case H1 
		    of I.BVar(k1) => if (k1 = k2) 
				       then assignSpine (depth, Glocal_u1, (S1, s1), S2, cnstr)
				     else raise Assignment "Bound variable clash"
		  | _ => raise Assignment "Head mismatch")
       	   | _ => assignHead (depth, Glocal_u1, Us1, U2, cnstr))
	    (* here spine associated with k2 might not be Nil ? *)
	| assignExpW (depth, Glocal_u1, Us1, U2 as I.Root(I.BVar k2, S), cnstr) = 
	   if (k2 > depth) 
	     then 
	       (* BVar(k2) stands for an existential variable *)
	       (* I.Root (BVar k2, S) will be fully applied (invariant from compilation) *)
	       (* Glocal_u1 |- Us1 *)	       
	       (S.insert asub ((k2 - depth), Assign(Glocal_u1, I.EClo(Us1))); 
		cnstr)
	   else
	     (* can these cases happen ? *)
	     (case Us1 
		of (I.EVar(r, _, V, Cnstr), s) => 
		  let
		    val U2' = normalizeNExp (U2, csub)
		  in 		 
		    (Eqn(Glocal_u1, I.EClo(Us1), U2')::cnstr)
		  end 
	        | (I.EClo(U,s'), s) => assignExp(depth, Glocal_u1, (U, I.comp(s', s)), U2, cnstr)
	        | (I.FgnExp (_, ops), _) => 	
		  let
		    val U2' = normalizeNExp (U2, csub)
		  in  
		    (Eqn(Glocal_u1, I.EClo(Us1), U2')::cnstr)
		  end)
        (* by invariant Us2 cannot contain any FgnExp *)
	| assignExpW (depth, Glocal_u1, (I.Lam (D1 as I.Dec(_, A1), U1), s1), I.Lam (D2 as I.Dec(_, A2), U2), cnstr) =   
          (* D1[s1] = D2[s2]  by invariant *)
	  assignExp (depth+1, I.Decl (Glocal_u1, I.decSub (D1, s1)), (U1, I.dot1 s1), U2, cnstr) 
	  (* here it does matter what we put in Glocal_u1! since D2 will only be approximately the same as D1 at this point! *)
	  (*	  assignExp (depth+1, I.Decl (Glocal_u1, D2), (U1, I.dot1 s1), U2, cnstr) *)

	| assignExpW (depth, Glocal_u1, Us1 as (I.EVar(r, _, V, Cnstr), s), U2, cnstr) =
	  (* generate cnstr substitution for all nvars occurring in U2 *)
	  let
	    val U2' = normalizeNExp (U2, csub)
	  in 
	    (Eqn(Glocal_u1, I.EClo(Us1), U2')::cnstr)
	  end 

	| assignExpW (depth, Glocal_u1, Us1 as (I.EClo(U,s'), s), U2, cnstr) = 
	  assignExp(depth, Glocal_u1, (U, I.comp(s', s)), U2, cnstr)

	| assignExpW (depth, Glocal_u1, Us1 as (I.FgnExp (_, ops), _), U2, cnstr) =
	  (* by invariant Us2 cannot contain any FgnExp *)
	  let
	    val U2' = normalizeNExp (U2, csub)
	  in 
	    (Eqn(Glocal_u1, I.EClo(Us1), U2')::cnstr)
	  end 
	| assignExpW (depth, Glocal_u1, Us1, U2 as I.FgnExp (_, ops), cnstr) =
	  (Eqn(Glocal_u1, I.EClo(Us1), U2)::cnstr)
      | assignExpW (depth, Glocal_u1, (U1, s1), I.Lam (D2, U2), cnstr) =                     
          (* Cannot occur if expressions are eta expanded *)
	  raise Assignment "Cannot occur if expressions in clause heads are eta-expanded"
      | assignExpW (depth, Glocal_u1, (I.Lam (D1, U1), s1), U2, cnstr) =	                   
      (* ETA: can't occur if eta expanded *)
	    raise Assignment "Cannot occur if expressions in query are eta-expanded"

	   (* same reasoning holds as above *)

	  
      and assignSpine (depth, Glocal_u1, (I.Nil, _), I.Nil, cnstr) = cnstr
	| assignSpine (depth, Glocal_u1, (I.SClo (S1, s1'), s1), S, cnstr) = 
	assignSpine (depth, Glocal_u1, (S1, I.comp (s1', s1)), S, cnstr)
	| assignSpine (depth, Glocal_u1, (I.App (U1, S1), s1), I.App (U2, S2), cnstr) =
	let 
	  val cnstr' = assignExp (depth, Glocal_u1, (U1, s1), U2, cnstr)
	(* nsub_goal, asub may be destructively updated *)
	in 
	  assignSpine (depth, Glocal_u1, (S1, s1), S2, cnstr')
	end 
      (* assignExp (depth, Glocal_u1, Us1, U2, cnstr) =  cnstr' *)  
      and assignExp (depth, Glocal_u1, Us1, U2, cnstr) = 
	  assignExpW (depth, Glocal_u1, Whnf.whnf Us1, U2, cnstr)  
    in 
      assignExp (depth, Glocal_u1, Us1, U2, cnstr)
    end 

  (* assignable (g, nsub, nsub_goal, asub, csub, cnstr) = (nsub_goal', csub, cnstr') option
    
    nsub, nsub_goal, nsub_goal' are  well-formed normal substitutions
    asub is a well-formed assignable substitution  
    csub is maps normal variables to avars

        G  |- nsub_goal     
        G' |- nsub : N
        G  |- asub : G'

    G'     |- csub : N'
    G', N' |- cnstr
    G'     |- cnstr[csub]
    
   *)
  fun assignableLazy (nsub, nsub_query, assignSub, (nsub_left, cnstrSub), cnstr) = 
    let
      val nsub_query' = querySubId ()   
      val cref = ref cnstr
      fun assign' (nsub_query, nsub) = 
	let
	  val (nsub_query_left, nsub_left1) = S.differenceModulo nsub_query nsub
	                        (fn (Glocal_u, U) => fn  T => 
				 cref := assign (Glocal_u, (U, I.id), T, nsub_query', assignSub, cnstrSub, !cref))
	  val nsub_left' = S.update nsub_left1 (fn U => normalizeNExp (U, cnstrSub))
	in 
	  (SOME(S.union nsub_query_left nsub_query', (S.union nsub_left nsub_left', cnstrSub), !cref))
	end 
    in
      assign' (nsub_query, nsub)
      handle Assignment msg => ((* print (msg ^ "\n") *) NONE)
    end 


  fun assignableEager (nsub, nsub_query, assignSub, cnstrSub, cnstr) = 
    let
      val nsub_query' = querySubId ()   
      val cref = ref cnstr
      fun assign' (nsub_query, nsub) = 
	let
	  val (nsub_query_left, nsub_left) = S.differenceModulo nsub_query nsub
	                        (fn (Glocal_u, U) => fn  T => 
				 cref := assign (Glocal_u, (U, I.id), T, nsub_query', assignSub, cnstrSub, !cref))
          (* normalize nsub_left (or require that it is normalized
	     collect all left-over nsubs and later combine it with cnstrsub
           *)
	  val _ = S.forall nsub_left (fn (nv, U) => case (S.lookup cnstrSub nv) 
					                 of NONE =>  raise Error "Left-over nsubstitution" 
						       | SOME(I.AVar A) => A := SOME(normalizeNExp (U, cnstrSub)))
	in (* cnstr[rsub] *)
	  (* nsub_goal1 = rgoal u nsub_goal'  remaining substitutions to be checked *)
	  (SOME(S.union nsub_query_left nsub_query', cnstrSub, !cref))
	end 
    in
      assign' (nsub_query, nsub)
      handle Assignment msg => ((* print (msg ^ "\n") *) NONE)
    end 

  (* Unification *)
  fun unifyW (G, (X as I.AVar(r as ref NONE), I.Shift 0), Us2) =      
      r := SOME(I.EClo(Us2))
    | unifyW (G, (X as I.AVar(r as ref NONE), s), Us2 as (U, s2)) =      
      (print "unifyW -- not s = Id\n";
       print ("Us2 = " ^ Print.expToString (G, I.EClo(Us2)) ^ "\n");
       r := SOME(I.EClo(Us2)))
    | unifyW (G, Xs1, Us2) = 
    (* Xs1 should not contain any uninstantiated AVar anymore *)
      Unify.unifyW(G, Xs1, Us2)
    
  fun unify(G, Xs1, Us2) = unifyW(G, Whnf.whnf Xs1, Whnf.whnf Us2)
    
  fun unifiable (G, Us1, Us2) = 
      (unify(G, Us1, Us2); true)
      handle Unify.Unify msg => false
	   
  (* Convert context G into explicit substitution *)
  (* ctxToEVarSub (i, G, G', asub, s) = s'

  *)

  fun ctxToExplicitSub (i, Gquery, I.Null, asub) = I.id
    | ctxToExplicitSub (i, Gquery, I.Decl(Gclause, I.Dec(_, A)), asub) = 
      let
	val s = ctxToExplicitSub (i+1, Gquery, Gclause, asub) 
	val (U' as I.EVar(X',_,_, _)) = I.newEVar (Gquery, I.EClo(A, s)) 
      in 
	case S.lookup asub i 
	  of NONE => ()
	| SOME(Assign(Glocal_u, U)) =>  
	    X' := SOME(raiseType(Glocal_u, U));
        I.Dot(I.Exp(U'), s)
      end 


    | ctxToExplicitSub (i, Gquery, I.Decl(Gclause, I.ADec(_, d)), asub) = 
      let
	val (U' as (I.AVar X')) = I.newAVar ()
      in 
	(case S.lookup asub i
	   of NONE => ()
	 | SOME(Assign(Glocal_u, U)) => 
	    X' := SOME(U)); 
(*	     if (d = I.ctxLength Glocal_u) then () else print ("Invariant violated AVar: d " ^ Int.toString d ^ 
							 " = ctxLength " ^ Int.toString(I.ctxLength Glocal_u) ^ " \n");  *)
	    I.Dot(I.Exp(I.EClo(U', I.Shift(~d))), ctxToExplicitSub (i+1, Gquery, Gclause, asub))(* d = I.ctxLength Glocal_u *)    
      end 

  fun solveAuxG (C.Trivial, s, Gquery) =  true (* succeed *)
    | solveAuxG (C.UnifyEq(Glocal,e1, N, eqns), s, Gquery) = 
      let
	val G = compose' (Glocal, Gquery)
	val s' = shift (Glocal, s)
      in 
	if unifiable (G, (N, s'), (e1, s'))
	  then solveAuxG (eqns, s, Gquery)
	else false
     end

  fun solveCnstr (Gquery, nil, s) = true
    | solveCnstr (Gquery, Eqn(Glocal, U1, U2)::Cnstr, s) = 
     (Unify.unifiable(compose'(Gquery, Glocal), (U1, I.id), (U2, shift(Glocal, s))) andalso    
      solveCnstr (Gquery, Cnstr, s))

  fun solveResiduals (Gquery, Gclause, CGoals(AuxG, cid, ConjGoals, i), asub, cnstr', sc) =
    let
(*      val _ = print ("Applied clause " ^ Names.qidToString(Names.constQid cid) ^ "\n") *)
      val s = ctxToExplicitSub (1, Gquery, Gclause, asub) 
      val success =  solveAuxG (AuxG, s, Gquery) andalso solveCnstr (Gquery, cnstr', s)	
    in
      if success
	then 
	  (sc ((ConjGoals, s), cid (* B *))) 
      else () 
    end 


  fun ithChild (CGoals(_, _, _, i), n) = (i = n)

  fun retrieveChild (num, Child, nsub_query, assignSub, cnstr, Gquery, sc) = 
    let       
      fun retrieve (Leaf(nsub, Gclause, Residuals), nsub_query, assignSub, cnstrSub, cnstr) = 
         (case assignableEager (nsub, nsub_query, assignSub, cnstrSub, cnstr)
	  (* destructively updates assignSub, might initiate backtracking  *)
	  of NONE => ()
	  | SOME(nsub_query', cnstrSub', cnstr') => 
	    (if (isId nsub_query') (* cnstrSub' = empty? by invariant *)
	       then 
		 (* LCO optimization *)		 
		 if ithChild(Residuals, !num) then 
		    solveResiduals (Gquery, Gclause, Residuals, assignSub, cnstr', sc)
		 else 
		   CSManager.trail (fn () => solveResiduals (Gquery, Gclause, Residuals, assignSub, cnstr', sc))        
	     else 
	      raise Error "Left-over normal substitutions!"))

	| retrieve (Node(nsub, Children), nsub_query, assignSub, cnstrSub, cnstr) =
	 (case assignableEager (nsub, nsub_query, assignSub, cnstrSub, cnstr)
	  (* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
          (* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)
	    of NONE => ()
	     | SOME (nsub_query', cnstrSub', cnstr') => 
	       (S.forall Children 
		(fn (n, Child) => retrieve (Child, nsub_query', S.copy assignSub, S.copy cnstrSub', cnstr'))))
    in 
      retrieve (Child, nsub_query, assignSub, cnstrSubId (), cnstr)
    end 

  fun retrieval (n, STree as Node(s, Children), G, r, sc) =        
    (* s = id *)
    let
      val (nsub_query, assignSub) = (querySubId (), assignSubId ())
    in 
      S.insert nsub_query (1, (I.Null, r));
      S.forall Children (fn (_, C) => retrieveChild (n, C, nsub_query, assignSub, nil, G, sc))
    end 

 (*----------------------------------------------------------------------------*)
 (* Retrieval via set of candidates *)
 fun retrieveAll (num, Child, nsub_query, assignSub, cnstr, candSet) = 
    let       
      val i = ref 0
      fun retrieve (Leaf(nsub, Gclause, Residuals), nsub_query, assignSub, (nsub_left, cnstrSub), cnstr) = 
         (case assignableLazy (nsub, nsub_query, assignSub, (nsub_left, cnstrSub), cnstr)
	  (* destructively updates assignSub, might initiate backtracking  *)
	  of NONE => ()
	  | SOME(nsub_query', (nsub_left', cnstrSub'), cnstr') => 
	    (if (isId nsub_query') 
	       then 
		 (* LCO optimization *)		 
		 (i := !i+1; 
		  S.insert candSet (!i, (assignSub, nsub_left', cnstrSub', cnstr', Gclause, Residuals));())
	     else 
	      raise Error "Left-over normal substitutions!"))

	| retrieve (Node(nsub, Children), nsub_query, assignSub, (nsub_left, cnstrSub), cnstr) =
	 (case assignableLazy (nsub, nsub_query, assignSub, (nsub_left, cnstrSub), cnstr)
	  (* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
          (* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)
	    of NONE => ()
	     | SOME (nsub_query', (nsub_left', cnstrSub'), cnstr') => 
	       (S.forall Children 
		(fn (n, Child) => retrieve (Child, nsub_query', S.copy assignSub, (S.copy nsub_left', S.copy cnstrSub'), cnstr'))))
    in 
      retrieve (Child, nsub_query, assignSub, (nid(), cnstrSubId ()), cnstr)
    end 

 fun retrieveCandidates (n, STree as Node(s, Children), Gquery, r, sc) =        
    (* s = id *)
    let
      val (nsub_query, assignSub) = (querySubId (), assignSubId ())
      val candSet = S.new() 
      fun solveCandidate (i, candSet) = 
	case (S.lookup candSet i) 
	  of NONE => ((* print "No candidate left anymore\n" ;*) () )
	   | SOME(assignSub, nsub_left, cnstrSub, cnstr, Gclause, Residuals 
	         (* CGoals(AuxG, cid, ConjGoals, i) *)) => 
	     (S.forall nsub_left (fn (nv, U) => case (S.lookup cnstrSub nv) 
					                 of NONE =>  raise Error "Left-over nsubstitution" 
						       | SOME(I.AVar A) => A := SOME(U));
	      CSManager.trail (fn () => 
	       (solveResiduals (Gquery, Gclause, Residuals, assignSub, cnstr, sc)));
	        solveCandidate (i+1, candSet (* sc = (fn S => (0::S)) *) ))
    in 
      S.insert nsub_query (1, (I.Null, r));
      S.forall Children (fn (_, C) => retrieveAll (n, C, nsub_query, assignSub, nil, candSet));
      (* execute one by one all candidates : here ! *)
      solveCandidate (1, candSet) 
    end 

 fun matchSig (a, G, ps as (I.Root(Ha,S),s), sc) = 
     let
       val (n, Tree) = Array.sub (indexArray, a)
     in              
       (* retrieval (n, !Tree, G, I.EClo(ps), sc)   *)
       retrieveCandidates (n, !Tree, G, I.EClo(ps), sc)   
     end 

 fun sProgReset () = 
   (nctr := 1; 
     Array.modify (fn (n, Tree) => (n := 0; Tree := !(makeTree ()); 
				   (n, Tree))) indexArray)


 fun sProgInstall (a, C.Head(E, G, Eqs, cid), R) = 
   let 
     val (n, Tree) = Array.sub (indexArray, a)     
     val nsub_goal = S.new()             
   in       
      S.insert nsub_goal (1, E);
      Tree := insert (!Tree, nsub_goal, (G, CGoals(Eqs, cid, R, !n+1)));
      n := !n+1
   end 

    (*   to be added *)
    (*     fun sProgLookup conDec = SubstTree.retrieve (sProgArray, ) *)

  in
    val sProgReset = sProgReset
    val sProgInstall = sProgInstall
    val matchSig = matchSig 
(*    val goalToString = goalToString *)

  end (* local *)
end; (* functor SubTree *)













