(* Linear Substitution Tree indexing *)
(* Linearity: Any variables occurring inside the substitution tree are linear *)
(* Any term we insert into the substitution tree is in normalform ! *)
(* Author: Brigitte Pientka *)

functor MemoTable (structure IntSyn' : INTSYN
		   structure CompSyn' : COMPSYN
		     sharing CompSyn'.IntSyn = IntSyn'
		   structure Conv: CONV
		     sharing Conv.IntSyn = IntSyn'
		   structure TableParam : TABLEPARAM
		     sharing TableParam.IntSyn = IntSyn'
		     sharing TableParam.CompSyn = CompSyn'
	           structure AbstractTabled : ABSTRACTTABLED
		     sharing AbstractTabled.IntSyn = IntSyn'
		   structure Print : PRINT
		     sharing Print.IntSyn = IntSyn'
 	           structure RBSet : RBSET)
  : MEMOTABLE =
struct
  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'
  structure AbstractTabled = AbstractTabled
  structure TableParam = TableParam
    
  (* ---------------------------------------------------------------------- *)
  

  (* Linear substitution tree for linear terms *)

  (* normalSubsts: key = int = nvar *)
  (* property: linear *)
  type normalSubsts =  IntSyn.Exp RBSet.ordSet 

  val nid : unit -> normalSubsts = RBSet.new 

  fun isId s = RBSet.isEmpty s

  (* Substitution Tree *)
  datatype Tree =  
      Leaf of normalSubsts * ((IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * 
			       TableParam.ResEqn * TableParam.answer * int) list) ref
    | Node of normalSubsts * (Tree ref) list

  fun makeTree () = ref (Node (nid (), []))  


  fun noChildren C = (C=[])

  (* Index array                             
   
   All type families have their own substitution tree and all substitution trees
   are stored in an array [a1,...,an]   where ai is a substitution tree for type family ai
   *)

  val indexArray = Array.tabulate (Global.maxCid, (fn i => (ref 0, makeTree ())));
    
  exception Error of string
  
  local

    structure I = IntSyn
    structure C = CompSyn
    structure S = RBSet
    structure A = AbstractTabled
    structure T = TableParam 
      
    exception Assignment of string
    
    exception Generalization of string   


  fun emptyAnswer () = T.emptyAnsw ()

  val answList : (TableParam.answer list) ref = ref []
  val added = ref false; 

  type nvar = int      (* index for normal variables *)
  type bvar = int      (* index for bound variables *)
  type bdepth = int    (* depth of locally bound variables *)

    
    (* ------------------------------------------------------ *)      
    (* Auxiliary functions *)

    fun cidFromHead (I.Const c) = c
      | cidFromHead (I.Def c) = c

    fun dotn (0, s) = s
      | dotn (i, s) = dotn (i-1, I.dot1 s)

    fun compose(IntSyn.Null, G) = G
      | compose(IntSyn.Decl(G, D), G') = IntSyn.Decl(compose(G, G'), D)
      
    fun shift (IntSyn.Null, s) = s
      | shift (IntSyn.Decl(G, D), s) = I.dot1 (shift(G, s))

    fun raiseType (I.Null, U) = U
      | raiseType (I.Decl(G, D), U) = I.Lam(D, raiseType (G, U))

    (* ------------------------------------------------------ *)      
    fun printSub (D, G, nsub_e) = 
      (S.forall nsub_e (fn (k, e) => 
			print (Int.toString k ^ " = " ^ 
			       Print.expToString (I.Null, A.raiseType(D, A.raiseType(G, e))) 
			       ^ ",  ")))

    fun printResEqn (G, T.Trivial) = print "Trivial\n"
      | printResEqn (G, T.Unify(G', U, N, eqn)) = 
        let
	  val (G'') = compose(G', G)
	  val s1 = shift (G', I.id) 
	  val _ = case s1 of I.Shift 0 => () | _ => print "s =/= id\n"
	in 
	  (print "Unify "; print (Print.expToString (I.Null, A.raiseType(G'', I.EClo(U, s1)))); print " = ";
	   print (Print.expToString (G'', I.EClo(N, s1)) ^ "\n");
	   printResEqn (G, eqn))
	  end 

    fun printChildrenSub (D, G, Children) =
      let
	fun printChild (N as Leaf(nsub_t, GList)) = (printSub(D, G, nsub_t) handle _ => print ", unprintable ")
          | printChild (N as Node(nsub_t, _)) = (printSub(D, G, nsub_t) handle _ => print ", unprintable " )
	
      fun forall ([]) = print "\n"
	| forall (Child::CList)  = 
	  (printChild (!Child);
	   forall CList)
    in 
      forall Children
    end 

(*    fun printResEqn (G, D, T.Trivial) = print "Trivial\n"
      | printResEqn (G, D, T.Unify(G', p1, N, eqn)) = 
        (print (Print.expToString (I.Null, A.raiseType(D, A.raiseType(compose(G', G), p1))) ^ " = ");
	 print (Print.expToString (I.Null, A.raiseType(D, A.raiseType(compose(G', G), N))) ^ "\n"); 
	 printResEqn (G, D, eqn))
*)
    fun printResEqnSub (G, D', T.Trivial, s) = print "Trivial\n"
      | printResEqnSub (G, D', T.Unify(G', p1, N, eqn), s) = 
        (print (Print.expToString (I.Null, A.raiseType(D', I.EClo(A.raiseType(compose(G', G), p1), shift(G', s)))) ^ " = ");
	 print (Print.expToString (I.Null, A.raiseType(D', I.EClo(A.raiseType(compose(G', G), N),shift(G', s)))) ^ "\n"); 
	 printResEqnSub (G, D', eqn, s))

    (* ------------------------------------------------------ *)      

    (*  Variable b    : bound variable
        Variable n    : index variable
        linear term  U ::=  Root(c, S) | Lam (D, U) | Root(b, S) 
        linear Spine S ::= p ; S | NIL
	indexed term t ::= Root(n, NIL) |  Root(c, S) | Lam (D, p) | Root(b, S) 
	indexed spines S_i ::= t ; S_i | NIL
        Types   A 
        Context G : context for bound variables (bvars)
                    (type information is stored in the context)
                G ::= . | G, x : A
        Set of all index variables:  N

        linear terms are well-typed in G:     G |- p 
        indexed terms are well-typed in (N ; G) |- t

    Let s is a substitution for index variables (nvar)
    and s1 o s2 o .... o sn = s, s.t.  
    forall nvar in CODOM(sk). 
     exists i . nvar in DOM(si) and i > k.

    IMAGE (s) = the index variables occurring in the CODOM(s)

    Let N1 ... Nn be the path from the root N1 to the leaf Nn,
    and si the substitution associated with node Ni.
 
    IMAGE(sn) = empty 
    s1 o s2 o ... o sn = s and IMAGE(s) = empty
    i.e. index variables are only internally used and no
         index variable is left. 

    A linear term U (and an indexed term t) can be decomposed into a term t' together with 
    a sequenence of substitutions s1, s2, ..., sn such that s1 o s2 o .... o sn = s
    and the following holds:
    
    If    N  ; G |- t
    then  N' ; G |- t'
          N  ; G |- s : N' ; G
          N  ; G |- t'[s]     and t'[s] = t

   if we have a linear term then N will be empty, but the same holds.

   In addition: 
   all expressions in the index are closed and linear, i.e.
   an expression is first linearized before it is inserted into the index
   (this makes retrieving all axpressions from the index which unify with 
    a given expression simpler, because we can omit the occurs check)
   
   *)


  (* ---------------------------------------------------------------*)   

  (* nctr = |D| =  #index variables *)
   val nctr = ref 1
    
   fun newNVar () =
     (nctr := !nctr + 1; 
      I.NVar(!nctr))
     
     
   fun eqHeads (I.Const k, I.Const k') =  (k = k')
     | eqHeads (I.BVar k, I.BVar k') = (k = k')
     | eqHeads (I.Def k, I.Def k') = (k = k')
     | eqHeads (_, _) = false

    (* too restrictive if we require order of both eqn must be the same ? 
     Sun Sep  8 20:37:48 2002 -bp *) 
    (* s = s' = I.id *)
    fun equalCtx (I.Null, s, I.Null, s') = true
      | equalCtx (I.Decl(G, D), s, I.Decl(G', D'), s') = 
        Conv.convDec((D, s), (D', s')) andalso (equalCtx (G, I.dot1 s, G', I.dot1 s'))

    (* in general, we need to carry around and build up a substitution *)
    fun equalEqn (T.Trivial, T.Trivial) = true
      | equalEqn (T.Unify(G, X, N, eqn), (T.Unify(G', X', N', eqn'))) = 
        equalCtx (G, I.id, G', I.id) andalso Conv.conv ((X, I.id), (X', I.id)) 
	andalso Conv.conv ((N, I.id), (N', I.id)) andalso equalEqn(eqn, eqn')
      | equalEqn (_, _) = false

    fun equalSub (I.Shift k, I.Shift k') = (k = k')
      | equalSub (I.Dot(F, S), I.Dot(F', S')) = 
        equalFront (F, F') andalso equalSub (S, S')
      | equalSub (I.Dot(F,S), I.Shift k) = false
      | equalSub (I.Shift k, I.Dot(F,S)) = false

    and equalFront (I.Idx n, I.Idx n') = (n = n')
      | equalFront (I.Exp U, I.Exp V) = Conv.conv ((U, I.id), (V, I.id))
      | equalFront (I.Undef, I.Undef) = true

    fun equalSub1 (I.Dot(ms, s), I.Dot(ms', s')) = 
          equalSub (s, s')

    fun equalCtx' (I.Null, I.Null) = true
      | equalCtx' (I.Decl(Dk, I.Dec(_, A)), I.Decl(D1, I.Dec(_, A1))) = 
        (Conv.conv ((A, I.id), (A1, I.id)) andalso equalCtx'(Dk, D1))
      | equalCtx' (I.Decl(Dk, I.ADec(_, d')), I.Decl(D1, I.ADec(_, d))) = 	
        ((d = d') andalso equalCtx'(Dk, D1))
      | equalCtx' (_, _) = false

   (* ---------------------------------------------------------------*)   
   (* most specific linear common generalization *)

   (* compatible (T, U) = (T', rho_u, rho_t) opt
    if T is an indexed term
       U is a linear term
       U and T share at least the top function symbol 
   then 
       T'[rho_u] = U and T'[rho_t] = T 
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
      handle Generalization msg =>  NONE
    end 

  (* compatibleSub(nsub_t, nsub_u) = (sigma, rho_t, rho_u) opt  
   
   if DOM(nsub_t) <= DOM(nsub_u) 
      CODOM(nsub_t) : index terms
      CODOM(nsub_u) : linear terms
        G_u, Glocal_u |- nsub_u
    N ; G_t, Glocal_t |- nsub_t
   then      
     nsub_t = sigma o rho_t
     nsub_e = sigma o rho_u
 
    Glocal_e ~ Glocal_t  (have "approximately" the same type)

   *)
  fun compatibleSub (nsub_t, nsub_u) = 
    let
      val (sigma, rho_t, rho_u) = (nid(), nid (), nid ()) 
(*      val (sigma, rho_u, rho_t) = S.splitSets nsub_e nsub_t  	
	(fn U => fn T => compatible (T, U, rho_t', rho_u'))
*)
     (* by invariant rho_t = empty, since nsub_t <= nsub_u *)
      val _ =  S.forall nsub_u
	(fn (nv, U) => 
	 (case (S.lookup nsub_t nv)
	    of SOME (T) =>     (* note by invariant Glocal_e ~ Glocal_t *) 
	      (case compatible (T, U, rho_t, rho_u)
		 of NONE => (S.insert rho_t (nv, T);
			     S.insert rho_u (nv, U))
	       | SOME(T') => S.insert sigma (nv, T')) 
	        (* here Glocal_t will be only approximately correct! *)
	  | NONE => S.insert rho_u (nv, U)))
    in 
      if isId(sigma)
	then NONE
      else 	
(*	 SOME(sigma, S.union rho_t rho_t', S.union rho_e rho_e') *)
	 SOME(sigma, rho_t, rho_u)
    end


 (* ---------------------------------------------------------------------- *)

  fun mkLeaf (s, GR, n) = Leaf (s, GR)

  fun mkNode (Node(_, Children), sigma, rho1, GR, rho2) = 
       Node(sigma, [ref (Leaf(rho2, ref [GR])), ref (Node(rho1, Children))])

    | mkNode (Leaf(c, GRlist), sigma, rho1, GR2, rho2) = 
       Node(sigma,[ref(Leaf(rho2, ref [GR2])), ref(Leaf(rho1, GRlist))])


  (* ---------------------------------------------------------------------- *)

  fun compatibleCtx ((DAVars, DEVars, G, eqn), []) = NONE
    | compatibleCtx ((DAVars, DEVars, G, eqn), ((DAVars', DEVars', G', eqn', answRef', _)::GRlist)) = 
       (* we may not need to check that the DAVars are the same *)
      (if (equalCtx'(DAVars, DAVars') andalso equalCtx'(DEVars, DEVars') 
	   andalso equalCtx' (G, G') andalso equalEqn(eqn, eqn'))
	 then SOME(answRef')
       else 
	 compatibleCtx((DAVars, DEVars, G, eqn), GRlist))

  fun compChild (DAVars, DEVars, G, N as Leaf(nsub_t, GList), nsub_e) = 
    ((* print ("\nnsub_e "); printSub(D, G, nsub_e); print "\n";
     (print ("sub at Leaf  : "); printSub(D, G, nsub_t); print "\n") handle _ => print "unprintable\n";*)
     (case compatibleSub (nsub_t, nsub_e) 
       of NONE => NONE
     | SOME(sigma, rho1, rho2) => 
	((*print ("sg "); (printSub(D, G, sigma); print "\n") handle _ => print "unprintable\n";
	 print ("rho1 "); (printSub(D, G, rho1); print "\n") handle _ => print "unprintable\n";
	 print ("rho2 "); (printSub(D, G, rho2); print "\n") handle _ => print "unprintable\n"; *)
	 SOME(sigma, rho1, rho2))))
       
    | compChild (DAVars, DEVars, G, N as Node(nsub_t, Children'), nsub_e) = 
       ((* print ("\nnsub_e "); printSub(D, G, nsub_e); print "\n";
	(print ("sub at node  : "); printSub(D, G, nsub_t); print "\n") handle _ => print "unprintable\n";*)
	(case compatibleSub (nsub_t, nsub_e) 
	  of NONE => NONE
	| SOME(sigma, rho1, rho2) => 
	  ((* print ("sg "); (printSub(D, G, sigma); print "\n") handle _ => print "unprintable\n";
	   print ("rho1 "); (printSub(D, G, rho1); print "\n") handle _ => print "unprintable\n";
	   print ("rho2 "); (printSub(D, G, rho2); print "\n") handle _ => print "unprintable\n";   *)
	   SOME(sigma, rho1, rho2))))


  fun findAllCandidates (DAVars, DEVars, G, nil, sub_u, VList, SList) = (VList, SList)
    | findAllCandidates (DAVars, DEVars, G, (x::L), sub_u, VList, SList) = 
      case compChild (DAVars, DEVars, G, !x, sub_u)
	of NONE => findAllCandidates (DAVars, DEVars, G, L, sub_u, VList, SList)
      | SOME(sigma, rho1, rho2) => 
	  if isId(rho1)
	    then (* rho2 + sub = sub_x *)
	      findAllCandidates (DAVars, DEVars, G, L, sub_u, ((x, rho2)::VList), SList)
	  else 
	    findAllCandidates (DAVars, DEVars, G, L, sub_u, VList, ((x, (sigma, rho1, rho2))::SList))

 (* ---------------------------------------------------------------------- *)	      	       
  fun divergingCtx (stage, D, G, GRlistRef) = 
    let
      val l = I.ctxLength(D) + I.ctxLength(G)
    in 
    List.exists (fn (_, D', G', _, _, stage') => (stage = stage' andalso (l > (I.ctxLength(G')+I.ctxLength(D')))))
    (!GRlistRef)
    end 

 (* eqTerm (t2, (t, rho1)) = bool
    returns true iff t2 = t[rho1] 
  t2 is a linear term which may not contain any nvars! 
  t may contain nvars  
 *)

 fun eqTerm (I.Root(H2, S2), (t as I.Root(H, S), rho1)) = 
     if eqHeads (H2, H) 
       then eqSpine(S2, (S, rho1))
     else 
       false
   | eqTerm (T2, (I.NVar n, rho1)) = 
     (case (S.lookup rho1 n)
	of NONE => false 
      | SOME (T1) => eqTerm (T2, (T1, nid())))
   | eqTerm (I.Lam(D2, T2), (I.Lam(D, T), rho1)) = 
     eqTerm (T2, (T, rho1))
   | eqTerm (_, (_, _)) = false

and eqSpine (I.Nil, (I.Nil, rho1)) = true
  | eqSpine (I.App(T2, S2), (I.App(T, S), rho1)) = 
    eqTerm (T2, (T, rho1)) andalso eqSpine (S2, (S, rho1))

 fun divergingSub (sigma, rho1, rho2) = 
    S.exists rho2 (fn (n2, t2) => S.exists sigma (fn (_,t) => eqTerm (t2, (t, rho1))))

(*
  fun divergingProof (stage, Skel, GRlistRef) = 
    List.exists (fn (Skel') => 
    (!GRlistRef)
    end 
*)

  fun insert (Nref, nsub_u, GR) = 
    let    
      fun insert' (N as Leaf (_, GRlistRef), nsub_u (* = id *), GR as (DAVars, DEVars, G, eqn, answRef, stage)) = 
	(case compatibleCtx ((DAVars, DEVars, G, eqn), (!GRlistRef))
	   of NONE => ((* compatible path -- but different ctx! *)		  
		       if ((!TableParam.divHeuristic) andalso divergingCtx (stage, DEVars, G, GRlistRef))
			 then
			   (print "ctx are diverging --- force suspension \n";
			    (fn () => (GRlistRef := (GR::(!GRlistRef));   
				      answList := (answRef :: (!answList))),   
			    T.DivergingEntry(answRef))) 
		       else 			 
			 (fn () => (GRlistRef := (GR::(!GRlistRef)); 
				    answList := (answRef :: (!answList))), 
			  T.NewEntry(answRef)))
	 | SOME(answRef') => ((* compatible path -- SAME ctx *)
			      ((fn () => ()), T.RepeatedEntry(answRef'))))

       
      | insert' (N as Node(sub, children), nsub_u, GR as (DAVars, DEVars, G, eqn, answRef, stage)) = 
	let
	  val (VCand, SCand) = findAllCandidates (DAVars, DEVars, G, children, nsub_u, nil, nil)
	    
	  fun checkVCandidates (nil, nil) = 
	    ((* no child is compatible with nsub_u *)
	     (* print "no child compatible \n";*)
	     (fn () => (Nref := Node(sub, (ref (Leaf(nsub_u, ref [GR])))::children); 
			answList := (answRef :: (!answList))),
	      T.NewEntry(answRef))) 

	    | checkVCandidates (nil, ((ChildRef, (sigma, rho1, rho2))::_)) = 
	    (* split an existing node *)
	      if ((!TableParam.divHeuristic) andalso divergingSub (sigma, rho1, rho2))
	       then 	       
		 (print "substree divering -- splitting node\n";
		  (fn () => (ChildRef :=  mkNode((!ChildRef), sigma, rho1, GR, rho2); 
			     answList := (answRef :: (!answList))),
		   T.DivergingEntry(answRef)))
	     else 
		((* print "split existing node\n";*)
		 (fn () => (ChildRef :=  mkNode((!ChildRef), sigma, rho1, GR, rho2); 
			    answList := (answRef :: (!answList))),
		 T.NewEntry(answRef)))
	    | checkVCandidates (((ChildRef, rho2)::nil), _) = 
	    (* there is a unique "perfect" candidate *)
	    insert (ChildRef, rho2, GR)
	    | checkVCandidates (((ChildRef, rho2)::L), SList) = 
	    (case (insert (ChildRef, rho2, GR))
	       of (_, T.NewEntry(answRef)) => 
		 checkVCandidates (L, SList)
	     | (f, T.RepeatedEntry(answRef)) => ((f, T.RepeatedEntry(answRef)))
	     | (f, T.DivergingEntry(answRef)) => ((f, T.DivergingEntry(answRef))))
	in 
	  checkVCandidates (VCand, SCand)
	end 
  in 
    insert' (!Nref, nsub_u, GR)
  end 


    (* ---------------------------------------------------------------------- *)
    (* answer check and insert 
      
     Invariant: 
        D |- Pi G.U 
          |- (Pi G.U)[s]
       .  |- s : D
       {{K}} are all the free variables in s
        D_k is the linear context of all free variables in {{K}}
        D_k |- s_k : D  and eqn 
        D_k |- (Pi G.U)[s_k] and eqn
     
      answerCheck (G, s, answRef, 0) = repeated
         if (D_k, s_k, eqn)  already occurs in answRef
      answerCheck (G,s, answRef, O) = new
         if (D_k, s_k, eqn) did not occur in answRef
         Sideeffect: update answer list for U    
     *) 
    fun answCheckVariant (G', U', s', answRef, O) =  
      let 
(*	val {T.solutions = S, T.lookup = i} = !answRef*)

	fun member ((D, sk), []) = false
	  | member ((D, sk), (((D1, s1),_)::S)) = 
	    if equalSub (sk,s1) andalso equalCtx'(D, D1) then   
	      true
	    else 
	      member ((D, sk), S)
	
	val (DEVars, sk) = A.abstractAnswSub (G', s')
	val Dk = compose(G', DEVars)
(*	val _ = print "Abstracted solution : "
	val _ = print (Print.expToString (I.Null, A.raiseType(DAVars, A.raiseType(DEVars, I.EClo(A.raiseType(G', U'), sk)))) ^ "\n")
	val _ = (print "Res. eqn "; printResEqn(Dk, eqnk))*)
      in 	
	if member ((DEVars, sk), T.solutions answRef) then  
	  T.repeated
	else 
	  (T.addSolution (((DEVars, sk), O), answRef);
	  T.new)
      end 

    (* ---------------------------------------------------------------------- *)
    fun reset () = 
      (nctr := 1; 
       Array.modify (fn (n, Tree) => (n := 0; 
				      Tree := !(makeTree ());
				      answList := []; 
				      added := false;
				      (n, Tree))) indexArray)

    fun callCheck (a, DAVars, DEVars, G , U, eqn) = 
      let 
	val (n, Tree) = Array.sub (indexArray, a)     
	val nsub_goal = S.new()             
	val _ = S.insert nsub_goal (1, U) 
	val result = insert (Tree, nsub_goal, (DAVars, DEVars, G, eqn, emptyAnswer(), !TableParam.stageCtr))
      in       
	case result 
	  of (sf, T.NewEntry(answRef)) => (sf(); added := true;  (* print "Add goal \n\n";  *)
					 T.NewEntry(answRef))
	  | (_, T.RepeatedEntry(answRef)) =>  ((* print "Suspend goal";*)
					     T.RepeatedEntry(answRef))
	  | (sf, T.DivergingEntry(answRef)) => (sf(); added := true;  (* print "Add goal -- ";*)
					     T.DivergingEntry(answRef))
      end 

 
    fun answCheck (G', U', s', answRef, O) = 
      case (!TableParam.strategy) of
	TableParam.Variant => 
	  answCheckVariant (G', U', s', answRef, O)
      | TableParam.Subsumption => raise Error "Subsumption is missing currently\n"

(*    fun solutions {T.solutions = S, T.lookup = i} = S
    fun lookup {T.solutions = S, T.lookup = i} = i

*)

    fun updateTable () = 
      let
	fun update [] Flag = Flag
	  | update (answRef::AList) Flag = 
	    (let
(*	      val {T.solutions = S, T.lookup = i} = !answRef*)
	      val l = length(T.solutions(answRef)) 
	    in 
	      if (l = T.lookup(answRef)) then 
		(* no new solutions were added in the previous stage *) 	      
		((* answRef := T.updateAnswLookup (l, !answRef) (* {T.solutions = S, T.lookup = l}*);*)
		 update AList Flag)
	      else 
		(* new solutions were added *)
		(T.updateAnswLookup (l, answRef);
		 update AList true)
	    end) 
	val Flag = update (!answList) false
	val r = (Flag orelse (!added))
      in  
	added := false; 
	r
      end 
  
  in

    val reset = reset
    val callCheck = (fn (Skel, D, G, U, eqn) => callCheck(cidFromHead(I.targetHead U), Skel, D, G, U, eqn))
  
    val answerCheck = answCheck
(*    val solutions = (fn answRef => solutions (!answRef))
    val lookup = (fn answRef => lookup (!answRef))*)
(*    val noAnswers = (fn answRef => noAnswers (!answRef))*)

    val updateTable = updateTable

    val tableSize = (fn () => (length(!answList)))
  end (* local *)
end; (* functor MemoTable *)
