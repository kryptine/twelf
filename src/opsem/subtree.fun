(* Linear Substitution Tree indexing *)
(* Linearity: Any variables occurring inside the substitution tree are linear *)
(* Any term we insert into the substitution tree is in normalform ! *)
(* Instance Checking *)
(* Author: Brigitte Pientka *)

functor MemoTable (structure IntSyn' : INTSYN
		       structure CompSyn' : COMPSYN
		       sharing CompSyn'.IntSyn = IntSyn'
		       structure Conv: CONV
		       sharing Conv.IntSyn = IntSyn'
		       structure Whnf : WHNF
		       sharing Whnf.IntSyn = IntSyn'
		       structure RBSet : RBSET
		       structure TableParam : TABLEPARAM
		       sharing TableParam.IntSyn = IntSyn'
		       sharing TableParam.CompSyn = CompSyn'
		       sharing TableParam.RBSet = RBSet
		       structure AbstractTabled : ABSTRACTTABLED
		       sharing AbstractTabled.IntSyn = IntSyn'			 
		       structure Print : PRINT
		       sharing Print.IntSyn = IntSyn')
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

  type normalSubsts  = IntSyn.Exp RBSet.ordSet 

  type exSubsts  = IntSyn.Exp RBSet.ordSet 

  val nid : unit -> normalSubsts = RBSet.new

  val aid = TableParam.aid

  val existId : unit -> normalSubsts = RBSet.new


  fun isId s = RBSet.isEmpty s

  (* ---------------------------------------------------------------------- *)
  type ctx = ((int * IntSyn.Dec) list) ref

  fun emptyCtx () :  ctx = ref []

  fun copy L : ctx = ref (!L)

  (* destructively updates L *)
  fun delete (x, L : ctx ) = 
      let 		  
	fun del (x, [], L) = NONE
	  | del (x, ((H as (y,E))::L), L') = if x = y then SOME((y,E), (rev L')@ L) else del(x, L, H::L')
      in 
	case del (x, (!L), [])
	  of NONE => NONE
	    | SOME((y,E), L') => (L := L'; SOME((y,E)))
      end 

  fun member (x, L:ctx) = 
    let
      fun memb (x, []) = NONE
	| memb (x, (H as (y,E)::L)) = if x = y then SOME((y,E)) else memb(x, L)
    in 
      memb (x, (!L))
    end 

  fun insertList (E, L) = (L := (E::(!L)); L)

 (* ---------------------------------------------------------------------- *)

  (* Substitution Tree *)
  (* it is only possible to distribute the evar-ctx because
     all evars occur exactly once! -- linear 
     this allows us to maintain invariant, that every occurrence of an evar is 
     defined in its evar-ctx
  *)
  datatype Tree =  
      Leaf of (ctx *  normalSubsts) * 
      (((int (* #EVar *)* int (* #G *)) * IntSyn.dctx (* G *) * 
	TableParam.ResEqn * TableParam.answer * int) list) ref
    | Node of (ctx *  normalSubsts) * (Tree ref) list

  fun makeTree () = ref (Node ((emptyCtx(), nid ()), []))  

  fun noChildren C = (C=[])

  datatype Retrieval = 
      Variant of ((normalSubsts -> unit) * IntSyn.Exp)
    | Instance of ((normalSubsts -> unit) * IntSyn.Exp)
    | NotCompatible 

  datatype CompSub = 
      SplitSub of ((ctx * normalSubsts (* sigma *)) * 
		   (ctx * normalSubsts (* rho1 *)) * 
		   (ctx * normalSubsts (* rho2 *)))
    | InstanceSub of (normalSubsts * (ctx * normalSubsts (* rho2 *)))
    | VariantSub of  (normalSubsts * (ctx * normalSubsts (* rho2 *)))
    | NoCompatibleSub 

  (* Index array                             
   
   All type families have their own substitution tree and all substitution trees
   are stored in an array [a1,...,an]   where ai is a substitution tree for type family ai
   *)

  val indexArray = Array.tabulate (Global.maxCid, (fn i => (ref 0, makeTree ())));
    
  exception Error of string
  
  local

    structure I   = IntSyn
    structure C   = CompSyn
    structure S   = RBSet
    structure A   = AbstractTabled
    structure T   = TableParam 

      
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

   fun equalDec (I.Dec(_, U), I.Dec(_, U')) = Conv.conv ((U, I.id), (U', I.id))
     | equalDec (I.ADec(_, d), I.ADec(_, d')) = (d = d')
     
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

    fun subsumesCtx (G, G') = equalCtx' (G, G')

    (* potential for forward and backward subsumption here ? *)

   (* ---------------------------------------------------------------*)   
    fun compareCtx (G, G') = equalCtx' (G, G')
(*      (case TableParam.Strategy (H1 as I.BVar k, S1)
	 of TableParam.Variant => equalCtx' (G, G')
	   | TableParam.Subsumption => subsumesCtx (G, G')
*)
   (* ---------------------------------------------------------------*)   
   (* most specific linear common generalization *)

   (* compatible (T, U) = (T', rho_u, rho_t) opt
    if T is an indexed term
       U is a linear term
       U and T share at least the top function symbol 
   then 
       T'[rho_u] = U and T'[rho_t] = T 
   *)

    (* lowerEVar' (G, V[s]) = (X', U), see lowerEVar *)
    fun lowerEVar' (X, G, (I.Pi ((D',_), V'), s')) =
        let
	  val D'' = I.decSub (D', s')
	  val (X', U) = lowerEVar' (X, I.Decl (G, D''), Whnf.whnf (V', I.dot1 s'))
	in
	  (X', I.Lam (D'', U))
	end
      | lowerEVar' (X, G, Vs') =
        let
	  val X' = X
	in
	  (X', X')
	end
    (* lowerEVar1 (X, V[s]), V[s] in whnf, see lowerEVar *)
    and (* lowerEVar1 (X, I.EVar (r, G, _, _), (V as I.Pi _, s)) = *)
      lowerEVar1 (X, I.EVar (r, G, _, _), (V as I.Pi _, s)) =
        let 
	  val (X', U) = lowerEVar' (X, G, (V,s))
	in
	  I.EVar(ref (SOME(U)), I.Null, V, ref nil)
	end
      | lowerEVar1 (_, X, _) = X

    (* lowerEVar (X) = X'

       Invariant:
       If   G |- X : {{G'}} P
            X not subject to any constraints
       then G, G' |- X' : P

       Effect: X is instantiated to [[G']] X' if G' is empty
               otherwise X = X' and no effect occurs.
    *)
    and 
      lowerEVar (E, X as I.EVar (r, G, V, ref nil)) = lowerEVar1 (E, X, Whnf.whnf (V, I.id))
      | lowerEVar (E, I.EVar _) =
        (* It is not clear if this case can happen *)
        (* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
        raise Error "abstraction : LowerEVars: Typing ambiguous -- constraint of functional type cannot be simplified"


(* n = #evars , d = index for the next evar*)
  fun convAssSub' (n, idx_k, D, asub, d) =  
    (case (RBSet.lookup asub d)  
       of NONE => (case member (d, D) 
		      of NONE => IntSyn.Shift (n)
		    | SOME(x, Dec) => (I.Dot(I.Idx (idx_k), convAssSub' (n, idx_k + 1, D, asub, d+1))))
       
     | SOME (U) => IntSyn.Dot(IntSyn.Exp(Whnf.normalize(U, I.id)), (* normalization necessary? *)
			      convAssSub'(n, idx_k + 1, D, asub, d+1)))

  fun convAssSub (D, n, asub, d) = convAssSub' (n, 1, D, asub, d)

   fun assign (d, Dec1 as I.Dec(n, V), E1 as I.Root(I.BVar k, S1), U, asub) = 
     (* it is an evar -- (k-d, EVar (SOME(U), V)) *)
     let
       val E as I.EVar(r, _, _ , cnstr) = I.newEVar (I.Null, V)
       val X = lowerEVar1 (E, I.EVar(r, I.Null, V, cnstr), Whnf.whnf(V, I.id))  
       val _ = (r := SOME(U))
     in
       S.insert asub (k - d, X)
(*       S.insert asub (k - d, U)*)
     end
     | assign (d, Dec1 as I.ADec(n, d'), E1 as I.Root(I.BVar k, S1), U, asub) = 
       (* it is an Avar and d = d' (k-d, AVar(SOME(U)) ? *)
       let
	 val A as I.AVar(r) = I.newAVar ()
	 val _ = (r := SOME(U))
       in 
(*	 S.insert asub (k - d, (I.EClo(U, I.Shift(~d'))))*)
	 S.insert asub (k - d, (I.EClo(A, I.Shift(~d'))))
      end 

   fun isExists (d, I.BVar k, D) = member (k-d, D)

   fun compHeads ((D_1, I.Const k), (D_2, I.Const k')) = (k = k')
     | compHeads ((D_1, I.BVar k), (D_2, I.BVar k')) = 
       (case isExists (0, I.BVar k, D_1) 
	  of NONE => (k = k')
	| SOME(x,Dec) => true)
     | compHeads ((D_1, I.BVar k), (D_2, H2)) = 
	(case isExists (0, I.BVar k, D_1) 
	  of NONE => false
	| SOME(x,Dec) => true)
     | compHeads ((D_1, H1), (D_2, H2)) = false
       

   fun compatible' ((D_t, T), (D_u, U), Ds, rho_t, rho_u) = 
   let 	             
     val instance = ref false
     fun genNVar ((rho_t, T), (rho_u, U)) = 
       (S.insert rho_t (!nctr+1, T);
	S.insert rho_u (!nctr+1, U);
	newNVar())
	  

     fun genRoot (depth, T as I.Root(H1 as I.Const k, S1), U as I.Root(I.Const k', S2), f) = 
       if (k = k') then 
	 let
	   val (f', S') = genSpine(depth, S1, S2, f)
	 in 
	   (f', I.Root(H1, S'))
	 end 
       else 
	 (f, genNVar ((rho_t, T), (rho_u, U)))
       | genRoot (d,  T as I.Root(H1 as I.BVar k, S1), U as I.Root(I.BVar k', S2), f) = 
	 if (k > d) andalso (k' > d)
	   then (* globally bound variable *)
	     let
	       val k1 = (k - d)
	       val k2 = (k' - d)
	     in 
	       case (member (k1, D_t), member(k2, D_u))
		 of (NONE, NONE) =>  
		   if (k1 = k2) 
		     then 
		       let 
			 val (f', S') = genSpine(d, S1, S2, f)
		       in 
			 (f', I.Root(H1, S'))
		       end 
		   else 
		     (f, genNVar ((rho_t, T), (rho_u, U)))
	       | (SOME(x, Dec1), SOME(x', Dec2)) => 
		 (* k, k' refer to the existential *)
		 if ((k1 = k2) andalso equalDec(Dec1, Dec2)) 
		   then (* they refer to the same existential variable *)
		     let
		       (* this is unecessary -- since existential variables have the same type
			and need to be fully applied in order, S1 = S2 *)
(*		       val _ = print ("refers to existential " ^ Int.toString (k1) ^ " \n")*)
		       val (f', S') = genSpine(d, S1, S2, f) 
		     in 
		       (delete (x, D_t) ; 
			delete (x', D_u); 
			insertList ((x, Dec1), Ds); 
			((fn asub => (f' asub; assign (d, Dec1, T, U, asub))), I.Root(H1, S')))
		     end 
		 else  
		   (* variant checking only *)
		   (f, genNVar ((rho_t, T), (rho_u, U)))
		   (* instance checking only Sun Oct 27 12:16:10 2002 -bp 
		    instance := true;
		    ((fn asub => (f asub; assign (d, Dec1, T, U, asub))), T)*)
		       
	       (* instance checking only Sun Oct 27 12:18:53 2002 -bp 
	       | (SOME(x, Dec1), NONE) => 
		 (print ("assign X_1 = BV " ^ Int.toString x ^ "\n");
		    instance := true;
		    ((fn asub => (f asub; assign (d, Dec1, T, U, asub))), T)) *)
	       | (_, _) => 
		 (f, genNVar ((rho_t, T), (rho_u, U)))
	     end 
	 else (* locally bound variables *)
	   if (k = k') then 
	     let
	       val (f', S') = genSpine(d, S1, S2, f)
	     in 
	       (f', I.Root(H1, S'))
	     end 
	   else 
	     ( (f, genNVar ((rho_t, T), (rho_u, U))))
       | genRoot (d, T as I.Root (H1 as I.BVar k, S1), U as I.Root(I.Const k', S2), f) = 
	 (f, genNVar ((rho_t, T), (rho_u, U)))
	 (* this case only should happen during instance checking *)
	 (* (case isExists (d, I.BVar k, D_t)
	    of NONE => (f, genNVar ((rho_t, T), (rho_u, U)))
             | SOME(x, Dec1) => (print ("assign X = Const\n"); 
				 instance := true ; 
				 ((fn asub => (f asub; assign (d, Dec1, T, U, asub))), T)))*)
	       
       | genRoot (d, T as I.Root(H1, S1), U as I.Root(H2, S2), f) = (f, genNVar ((rho_t, T), (rho_u, U)))
	       
     and genExp (d, T as I.NVar n, U as I.Root(H, S), f) =  
       (S.insert rho_u (n, U); 
	(f, T))
       | genExp (d, T as I.Root(H1, S1), U as I.Root(H2, S2), f) =  
           genRoot(d, I.Root(H1, S1), I.Root(H2, S2), f)
       | genExp (d, I.Lam(D1 as I.Dec(_,A1), T1), I.Lam(D2 as I.Dec(_, A2), U2), f) = 
       (* by invariant A1 = A2 *) 
       let 
	 val (f', E) = genExp (d+1, T1,  U2, f) 		 
       in 
	 (f', I.Lam(D1, E))
       end 
       | genExp (d, T, U, f) = 
	       (* U = EVar, EClo -- can't happen -- Sun Oct 20 13:41:25 2002 -bp *) 
       (print "genExp -- falls through?\n";
	(f, genNVar ((rho_t, T), (rho_u, U))))
       
     and genSpine (d, I.Nil, I.Nil, f) = (f, I.Nil)
       | genSpine (d, I.App(T, S1), I.App(U, S2), f) = 
       let 
	 val (f', E) = genExp (d, T, U, f)
	 val (f'', S') = genSpine (d, S1, S2, f')
       in 
	 (f'', I.App(E, S'))
       end 
     val (f, E) = genExp (0, T, U, (fn asub => ()))
(*     val _ = print "genExp -- done\n"*)
   in	 
     if (!instance) 
       then Instance(f, E)
     else 
       Variant (f, E)
       
   end 

     
   fun compatible ((D_t, T as I.Root(H1, S1)), (D_u, U as I.Root (H2, S2)), Ds, rho_t, rho_u) = 
     if compHeads ((D_t, H1), (D_u, H2))
       then 
	 compatible' ((D_t, T), (D_u, U), Ds, rho_t, rho_u)
     else NotCompatible
     |compatible ((D_t, T), (D_u, U), Ds, rho_t, rho_u) = 
       compatible' ((D_t, T), (D_u, U), Ds, rho_t, rho_u)

   (* ---------------------------------------------------------------*)   
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
  fun compatibleSub ((D_t, nsub_t), (D_u, nsub_u), asub) = 
    let
      val (sigma, rho_t, rho_u) = (nid(), nid (), nid ()) 
      val Dsigma = emptyCtx ()
      val D_r1 = copy D_t
      val D_r2 = copy D_u
      val choose = ref (fn match : bool => ())
      val inst = ref false
(*      val (sigma, rho_u, rho_t) = S.splitSets nsub_e nsub_t  	
	(fn U => fn T => compatible (T, U, rho_t', rho_u'))
*)
     (* by invariant rho_t = empty, since nsub_t <= nsub_u *)
      val _ =  S.forall nsub_u
	(fn (nv, U) => 
	 (case (S.lookup nsub_t nv)
	    of SOME (T) =>     (* note by invariant Glocal_e ~ Glocal_t *) 
	      (case compatible ((D_r1, T), (D_r2, U), Dsigma, rho_t, rho_u)
		 of NotCompatible => (S.insert rho_t (nv, T);
				      S.insert rho_u (nv, U))
	          | Variant(assign, T') => 
		   let 
		     val restc = (!choose) 
		   in 
		     (S.insert sigma (nv, T');
		     choose := (fn match => (restc match; if match then assign asub else ())))
		     end

(*		     S.insert sigma (nv, T')*)
		  | Instance(assign, T') => (inst := true; 
					     let val restc = (!choose) in 
					       choose := (fn match => 
						  (restc match;
						  if match then (assign asub ; S.insert sigma (nv, T'))
						  else (S.insert rho_t (nv, T);
							S.insert rho_u (nv, U)))) end ))
	  (* here Glocal_t will be only approximately correct! *)
	  | NONE => S.insert rho_u (nv, U)))
    in 
      (* print "compatible Sub done\n";*)
      if isId (rho_t) 
	then 
	  (* perfect match under asub and rho_t = nsub_t 
	   sigma = rho_t and sigma o asub = rho_u *)
	  ((*print "perfect match under asub\n";*)
	   (!choose) true ;
	   if !inst then InstanceSub (asub, (D_r2, rho_u)) else VariantSub(asub, (D_r2, rho_u)))
      else 
	((* print "split -- asub is unchanged\n";*)
	 (!choose) false ; 
	 if isId(sigma) 
	   then NoCompatibleSub
	 else 
	   SplitSub((Dsigma, sigma), (D_r1, rho_t), (D_r2, rho_u)))
    (*	 SOME(sigma, S.union rho_t rho_t', S.union rho_e rho_e') *)
    (* Dsigma |~ sigma, D_r1 |~ rho_t, D_r1 |~ rho_u *)
    end


 (* ---------------------------------------------------------------------- *)

  fun mkLeaf (Ds, GR, n) = Leaf (Ds, GR)

  fun mkNode (Node(_, Children), Dsigma, Drho1, GR, Drho2) = 
       Node(Dsigma, [ref (Leaf(Drho2, ref [GR])), ref (Node(Drho1, Children))])

    | mkNode (Leaf(c, GRlist), Dsigma, Drho1, GR2, Drho2) = 
       Node(Dsigma,[ref(Leaf(Drho2, ref [GR2])), ref(Leaf(Drho1, GRlist))])

  (* ---------------------------------------------------------------------- *)

  fun compatibleCtx ((G, eqn), []) = NONE
    | compatibleCtx ((G, eqn), ((l', G', eqn', answRef', _)::GRlist)) = 
       (* we may not need to check that the DAVars are the same *)
      (if (equalCtx' (G, G') andalso equalEqn(eqn, eqn'))
	 then SOME(l', answRef')
       else 
	 compatibleCtx((G, eqn), GRlist))

  fun compChild (N as Leaf((D_t, nsub_t), GList), (D_e, nsub_e), asub) = 
        compatibleSub ((D_t, nsub_t), (D_e,  nsub_e), asub)
    | compChild (N as Node((D_t, nsub_t), Children'), (D_e, nsub_e), asub) = 
	compatibleSub ((D_t, nsub_t), (D_e, nsub_e), asub)

  fun findAllCandidates (G_r, children, Ds, asub) = 
    let
      fun findAllCands (G_r, nil, (D_u, sub_u), asub, VList, IList, SList) = (VList, IList, SList)
	| findAllCands (G_r, (x::L), (D_u, sub_u), asub, VList, IList, SList) = 
	let
	  val k = S.size asub
	  val asub' = S.copy asub
	in 
	  case compChild (!x, (D_u, sub_u), asub')
	    of NoCompatibleSub => ((* print "Not compatible\n" ; *)
				   findAllCands (G_r, L, (D_u, sub_u), asub, VList, IList, SList))
	    | SplitSub (Dsigma, Drho1, Drho2) =>
	      ((* print "Split \n";*)
	      findAllCands (G_r, L, (D_u, sub_u), asub, VList, IList, 
			    ((x, (Dsigma, Drho1, Drho2))::SList)))
	    | InstanceSub (asub'', Drho2 as (D_r2, rho2)) => 
	      (* real instance *)
	      ((* print "instance \n";*)
		   findAllCands (G_r, L, (D_u, sub_u), asub', VList, ((x, Drho2, asub'')::IList), SList))
	    | VariantSub (asub'', Drho2 as (D_r2, rho2)) => 
 	     ((* print "variant \n";*)
	      findAllCands (G_r, L, (D_u, sub_u), asub', ((x, Drho2, asub')::VList), IList, SList))

	end 
    in 
      findAllCands (G_r, children, Ds, asub, nil, nil, nil)
    end 
 (* ---------------------------------------------------------------------- *)	      	       
  fun divergingCtx (stage, G, GRlistRef) = 
    let
      val l = I.ctxLength(G)
    in 
    List.exists (fn ((evar, l), G', _, _, stage') => (stage = stage' andalso (l > (I.ctxLength(G')))))
    (!GRlistRef)
    end 

  fun eqHeads (I.Const k, I.Const k') =  (k = k')
    | eqHeads (I.BVar k, I.BVar k') =  (k = k') 
	 | eqHeads (I.Def k, I.Def k') = (k = k')
	 | eqHeads (_, _) = false

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

 fun divergingSub ((Ds, sigma), (Dr1, rho1), (Dr2, rho2)) = 
    S.exists rho2 (fn (n2, t2) => S.exists sigma (fn (_,t) => eqTerm (t2, (t, rho1))))

  (* ---------------------------------------------------------------------- *)
  (* Insert via variant checking *)

  fun insert (Nref, (D_u, nsub_u), asub, GR) = 
    let    
      fun insert' (N as Leaf ((D,  _), GRlistRef), (D_u, nsub_u), asub, GR as ((evarl,l), G_r, eqn, answRef, stage)) = 
	(* need to compare D and D_u *)
	(case compatibleCtx ((G_r, eqn), (!GRlistRef))
	   of NONE => ((* compatible path -- but different ctx! *)		  
		       if ((!TableParam.divHeuristic) andalso divergingCtx (stage, G_r, GRlistRef))
			 then
			   (print "ctx are diverging --- force suspension \n";
			    (fn () => (GRlistRef := (GR::(!GRlistRef));   
				      answList := (answRef :: (!answList))),   
			    T.DivergingEntry(answRef))) 
		       else 			 
			 ((* print "compatible path -- ctx are different\n";*)
			  (fn () => (GRlistRef := (GR::(!GRlistRef)); 
				    answList := (answRef :: (!answList))), 
			  T.NewEntry(answRef))))
	 | SOME((evarl', Glength), answRef') => ((* compatible path -- SAME ctx *)
						 (* print "compatible path --- same ctx\n";*)
				((fn () => ()), T.RepeatedEntry(convAssSub(D_u, evarl', asub, Glength), answRef'))
				))

       
      | insert' (N as Node((D, sub), children), (D_u, nsub_u), asub, GR as (l, G_r, eqn, answRef, stage)) = 
	let
	  val (VariantCand, InstCand, SplitCand) = findAllCandidates (G_r, children, (D_u, nsub_u), asub)
	    
	  fun checkCandidates (nil, nil, nil) = 
	    ((* no child is compatible with nsub_u *)
	     (fn () => (Nref := Node((D, sub), (ref (Leaf((D_u, nsub_u), ref [GR])))::children); 
			answList := (answRef :: (!answList))),
	      T.NewEntry(answRef)))

	    | checkCandidates (nil, nil, ((ChildRef, (Dsigma, Drho1, Drho2))::_)) = 
	      (* split an existing node *)
	      if ((!TableParam.divHeuristic) andalso 
		  divergingSub (Dsigma, Drho1, Drho2))
	       then 	       
		 ((* substree divering -- splitting node *)
		  (fn () => (ChildRef :=  mkNode((!ChildRef), Dsigma, Drho1, GR, Drho2); 
			     answList := (answRef :: (!answList))),
		   T.DivergingEntry(answRef)))
	     else 
		((* split existing node *)
		 (fn () => (ChildRef :=  mkNode((!ChildRef), Dsigma, Drho1, GR, Drho2); 
			    answList := (answRef :: (!answList))),
		 T.NewEntry(answRef)))

	    | checkCandidates (((ChildRef, Drho2, asub)::nil), nil, _) = 
	      (* unique "perfect" candidate (left) *)		
		insert (ChildRef, Drho2, asub, GR)


	    | checkCandidates (((ChildRef, Drho2, asub)::L), nil, SCands) = 
	      (* there are several "perfect" candidates *)
	      (case (insert (ChildRef, Drho2, asub, GR))
		 of (_, T.NewEntry(answRef)) =>  checkCandidates (L, nil, SCands)
	       | (f, T.RepeatedEntry(asub, answRef)) => ((f, T.RepeatedEntry(asub, answRef)))
	       | (f, T.DivergingEntry(answRef)) => ((f, T.DivergingEntry(answRef))))

 	    | checkCandidates (VarCands, ((ChildRef, Drho2, asub)::ICands), SCands) = 
	      (* there are some "quite perfect" one *)
	      (case insert (ChildRef, Drho2, asub, GR)
		 of (_, T.NewEntry (answRef)) => checkCandidates (VarCands, ICands, SCands)
	       | (f, T.RepeatedEntry(asub, answRef)) => ((f, T.RepeatedEntry(asub, answRef)))
	       | (f, T.DivergingEntry(answRef)) => ((f, T.DivergingEntry(answRef))))
	in 
	  checkCandidates (VariantCand, InstCand, SplitCand)
	end 
  in 
    insert' (!Nref, (D_u, nsub_u), asub, GR)
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
	fun member ((D, sk), []) = false
	  | member ((D, sk), (((D1, s1),_)::S)) = 
	    if equalSub (sk,s1) andalso equalCtx'(D, D1) then   
	      true
	    else 
	      member ((D, sk), S)
	
	val (DEVars, sk) = A.abstractAnswSub (G', s')
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

    fun makeCtx (n, I.Null, DEVars : ctx) = n
      | makeCtx (n, I.Decl(G, D), DEVars : ctx) = 
        (insertList ((n, D), DEVars); 
	 makeCtx (n+1, G, DEVars))
      
    fun callCheck (a, DAVars, DEVars, G , U, eqn) = 
      let 
	val (n, Tree) = Array.sub (indexArray, a)     
	val nsub_goal = S.new()             
	val DAEVars = compose (DEVars, DAVars)
	val D = emptyCtx()
	val n = I.ctxLength(G)
	val _ = makeCtx (n+1, DAEVars, D:ctx)
	val l = I.ctxLength(DAEVars)
	val _ = S.insert nsub_goal (1, U) 
	val result =  insert (Tree, (D, nsub_goal), nid() (* assignable subst *), 
			      ((l, n+1), G, eqn, emptyAnswer(), !TableParam.stageCtr))
      in       
	case result 
	  of (sf, T.NewEntry(answRef)) => (sf(); added := true; (* print "Add goal \n"; *) 
					   T.NewEntry(answRef))
	  | (_, T.RepeatedEntry(asub, answRef)) =>  ((* print "Suspend goal\n";*)
						     T.RepeatedEntry(asub, answRef))
	  | (sf, T.DivergingEntry(answRef)) => (sf(); added := true;  print "Add diverging goal\n";
					     T.DivergingEntry(answRef))
      end 


    fun answCheck (G', U', s', answRef, O) = answCheckVariant (G', U', s', answRef, O)
(*      case (!TableParam.strategy) of
	TableParam.Variant => answCheckVariant (G', U', s', answRef, O)

      | TableParam.Subsumption => answCheckVariant (G', U', s', answRef, O) 
	                          (* no answer subsumption currently *)
*)


    fun updateTable () = 
      let
	fun update [] Flag = Flag
	  | update (answRef::AList) Flag = 
	    (let
	       val l = length(T.solutions(answRef)) 
	     in 
	       if (l = T.lookup(answRef)) then 
		 (* no new solutions were added in the previous stage *) 	      
		 update AList Flag
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
    val callCheck = (fn (DAVars, DEVars, G, U, eqn) => 
		        callCheck(cidFromHead(I.targetHead U), DAVars, DEVars, G, U, eqn))

(*
    val findAll (DAVars, DEVars, G, U, eqn) = 
    returns (asub * answRef) list which contains all possible entries in the tree 
    open question: do we need all entries?

*)
  
    val answerCheck = answCheck
    val updateTable = updateTable

    val tableSize = (fn () => (length(!answList)))
  end (* local *)
end; (* functor MemoTable *)
