(* Filling *)
(* Author: Carsten Schuermann *)

functor Filling (structure MetaSyn' : METASYN
		 structure MetaAbstract : METAABSTRACT
		 sharing MetaAbstract.MetaSyn = MetaSyn'
		 structure Search   : SEARCH
		 sharing Search.MetaSyn = MetaSyn'
 		 structure Whnf : WHNF
		 sharing Whnf.IntSyn = MetaSyn'.IntSyn
		 structure Print : PRINT
		 sharing Print.IntSyn = MetaSyn'.IntSyn)
  : FILLING =
struct
  structure MetaSyn = MetaSyn'

  exception Error of string

  type operator = (MetaSyn.State * int) * (unit -> MetaSyn.State list)

  local
    structure M = MetaSyn
    structure I = MetaSyn.IntSyn

    fun delay (search, Params) () = 
      (search Params
       handle Search.Error s => raise Error s)
     
    fun makeAddressInit S k = (S, k) 
    fun makeAddressCont makeAddress k = makeAddress (k+1)

    (* operators (G, GE, (V, s), abstract, makeAddress) = (OE', OL')
	
       Invariant: 
       If   G |- s : G1   G1 |- V : type
       and  abstract is an abstraction continuation
       and  makeAddress is continuation which calculates the correct 
	 debruijn index of the variable being filled 
       and V = {V1}...{Vn} V'
       then OE' is an operator list, OL' is a list with one operator
	 where the ith O' in OE' corresponds to a function which generates ALL possible
	                              successor states instantiating - non-index variables
				      with terms (if possible) in Vi
        and OL' is a list containing one operator which instantiates all - non-index variables
	  in V' with the smallest possible terms.
    *)
    fun operators (G, GE, Vs, abstract, makeAddress) =
          operatorsW (G, GE, Whnf.whnf Vs, abstract, makeAddress)
    and operatorsW (G, GE, Vs as (I.Root (C, S), _), abstract, makeAddress) =
          (nil, 
	   (makeAddress 0, delay (Search.searchEx, (G, GE, Vs, abstract))))
      | operatorsW (G, GE, (I.Pi ((D as I.Dec (_, V1), P), V2), s), 
		    abstract, makeAddress) = 
	let 
	  val (GO', O) = operators (I.Decl (G, I.decSub (D, s)), GE, (V2, I.dot1 s), 
				    abstract, 
				    makeAddressCont makeAddress)
	in
	  ((makeAddress 0, delay (Search.searchAll, 
				  (G, GE, (V1, s), abstract))) :: GO', O)
	end


    (* createEVars (G, M) = ((G', M'), s', GE')
      
       Invariant:
       If   |- G ctx
       and  G |- M mtx
       then |- G' ctx
       and  G' |- M' mtx
       and  G' |- s' : G
       and  GE a list (G, X) of EVars and their contexts in s'
    *)
    fun createEVars (M.Prefix (I.Null, I.Null, I.Null)) = 
          (M.Prefix (I.Null, I.Null, I.Null), I.id, nil)
      | createEVars (M.Prefix (I.Decl (G, D), I.Decl (M, M.Top), I.Decl (B, b))) =
	let 
	  val (M.Prefix (G', M', B'), s', GE') = createEVars (M.Prefix (G, M, B))
	in 
	  (M.Prefix (I.Decl (G', I.decSub (D, s')), I.Decl (M', M.Top), I.Decl (B', b)),
	   I.dot1 s', GE')
	end
      | createEVars (M.Prefix (I.Decl (G, I.Dec (_, V)), I.Decl (M, M.Bot), I.Decl (B, _))) =
	let 
	  val (M.Prefix (G', M', B'), s', GE') = createEVars (M.Prefix (G, M, B))
	  val X  = I.newEVar (I.EClo (V, s'))
	in
	  (M.Prefix (G', M', B'), I.Dot (I.Exp (X, V), s'), (G', X) :: GE')
	end


    (* expand' ((G, M), V) = (OE', OL')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  G |- V type
       and  V = {V1}...{Vn} V'
       then OE' is an operator list, OL' is a list with one operator
	 where the ith O' in OE' corresponds to a function which generates ALL possible
	                              successor states instantiating - non-index variables
				      with terms (if possible) in Vi
        and OL' is a list containing one operator which instantiates all - non-index variables
	  in V' with the smallest possible terms.
    *)
    fun expand (S as M.State (name, M.Prefix (G, M, B), V)) = 
	let 
	  val (M.Prefix (G', M', B'), s', GE') = createEVars (M.Prefix (G, M, B))
	  fun abstract () = (MetaAbstract.abstract (M.State (name, M.Prefix (G', M', B'),
							     I.EClo (V, s')))
			     handle MetaAbstract.Error s => raise Error s)
	in
	  operators (G', GE', (V, s'), abstract, makeAddressInit S) 
	end
    

    (* apply (S, f) = S'

       Invariant: 
       S is state and f is a function constructing the successor state S'
    *)
    fun apply (_, f) = f ()

    fun menu ((M.State (name, M.Prefix (G, M, B), V), k), Sl) =
	let
	  fun toString (G, I.Pi ((I.Dec (_, V), _), _), 0) = Print.expToString (G, V)
	    | toString (G, V as  I.Root _, 0) = Print.expToString (G, V)
	    | toString (G, I.Pi ((D, _), V), k) =
		toString (I.Decl (G, D), V, k-1)
	    (* no cases for 
	      toSTring (G, I.Root _, k) for k <> 0
	    *)
	in
	  "Filling   : " ^ toString (G, V, k)
	end
      
  in
    val expand = expand
    val apply = apply
    val menu = menu
  end (* local *)
end; (* functor Filling *)
