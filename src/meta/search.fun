(* Search (based on abstract machine ) : Version 1.3 *)
(* Author: Carsten Schuermann *)

functor MTPSearch (structure Global : GLOBAL
		   structure IntSyn' : INTSYN
		   structure Abstract : ABSTRACT
		     sharing Abstract.IntSyn = IntSyn'
                   structure TypeCheck : TYPECHECK
                     sharing TypeCheck.IntSyn = IntSyn'
		   structure MTPGlobal : MTPGLOBAL
                   structure FunSyn' : FUNSYN
                     sharing FunSyn'.IntSyn = IntSyn'
		   structure StateSyn' : STATESYN
		     sharing StateSyn'.FunSyn = FunSyn'
		   structure CompSyn' : COMPSYN
		     sharing CompSyn'.IntSyn = IntSyn'
		   structure Whnf : WHNF
		     sharing Whnf.IntSyn = IntSyn'
		   structure Unify : UNIFY
		     sharing Unify.IntSyn = IntSyn'
		   structure Index : INDEX
		     sharing Index.IntSyn = IntSyn'
                   structure PTCompile : PTCOMPILE
                     sharing PTCompile.IntSyn = IntSyn'
                     sharing PTCompile.CompSyn = CompSyn'
		   structure Compile1 : COMPILE
		     sharing Compile1.IntSyn = IntSyn'
		     sharing Compile1.CompSyn = CompSyn'
                   structure AbsMachine1 : ABSMACHINE
                     sharing AbsMachine1.Compile = Compile1
		   structure Compile2 : COMPILE
		     sharing Compile2.IntSyn = IntSyn'
		     sharing Compile2.CompSyn = CompSyn'
                   structure AbsMachine2 : ABSMACHINE
                     sharing AbsMachine2.Compile = Compile2
                   (*
		   structure CPrint : CPRINT
		     sharing CPrint.IntSyn = IntSyn'
		     sharing CPrint.CompSyn = CompSyn'
                     sharing CPrint.FullComp = Compile1
		   structure Print : PRINT
		     sharing Print.IntSyn = IntSyn'
		   structure Names : NAMES 
		     sharing Names.IntSyn = IntSyn'
                   *)
                   structure CSManager : CS_MANAGER
                     sharing CSManager.IntSyn = IntSyn')
  : MTPSEARCH =
struct

  structure IntSyn = IntSyn'
  structure FunSyn = FunSyn'
  structure StateSyn = StateSyn'
  structure CompSyn = CompSyn'

  exception Error of string

  local
    structure I = IntSyn
    structure C = CompSyn
    structure F = FunSyn
      
    (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
    fun exists P K =
        let fun exists' (I.Null) = false
	      | exists' (I.Decl(K',Y)) = P(Y) orelse exists' (K')
	in
	  exists' K
	end


    (* occursInExp (r, (U, s)) = B, 

       Invariant:
       If    G |- s : G1   G1 |- U : V 
       then  B holds iff r occurs in (the normal form of) U
    *)
    fun occursInExp (r, Vs) = occursInExpW (r, Whnf.whnf Vs)

    and occursInExpW (r, (I.Uni _, _)) = false
      | occursInExpW (r, (I.Pi ((D, _), V), s)) = 
          occursInDec (r, (D, s)) orelse occursInExp (r, (V, I.dot1 s))
      | occursInExpW (r, (I.Root (_, S), s)) = occursInSpine (r, (S, s))
      | occursInExpW (r, (I.Lam (D, V), s)) = 
	  occursInDec (r, (D, s)) orelse occursInExp (r, (V, I.dot1 s))
      | occursInExpW (r, (I.EVar (r' , _, V', _), s)) = 
          (r = r') orelse occursInExp (r, (V', s))
      | occursInExpW (r, (I.FgnExp (cs, ops), s)) =
          occursInExp (r, (#toInternal(ops)(), s))
          (* hack - should consult cs  -rv *)

    and occursInSpine (_, (I.Nil, _)) = false
      | occursInSpine (r, (I.SClo (S, s'), s)) = 
          occursInSpine (r, (S, I.comp (s', s)))
      | occursInSpine (r, (I.App (U, S), s)) = 
	  occursInExp (r, (U, s)) orelse occursInSpine (r, (S, s))

    and occursInDec (r, (I.Dec (_, V), s)) = occursInExp (r, (V, s))

    (* nonIndex (r, GE) = B
     
       Invariant: 
       B hold iff
        r does not occur in any type of EVars in GE
    *)
    fun nonIndex (_, nil) = true
      | nonIndex (r, I.EVar (_, _, V, _) :: GE) = 
          (not (occursInExp (r, (V, I.id)))) andalso nonIndex (r, GE)

    (* select (GE, (V, s), acc) = acc'

       Invariant:
    *)
    (* Efficiency: repeated whnf for every subterm in Vs!!! *)
    fun selectEVar (nil) = nil
      | selectEVar ((X as I.EVar (r, _, _, ref nil)) :: GE) = 
        let 
	  val Xs = selectEVar (GE)
	in
	  if nonIndex (r, Xs) then Xs @ [X]
	  else Xs
	end
      | selectEVar ((X as I.EVar (r, _, _, cnstrs)) :: GE) =  (* Constraint case *)
        let 
	  val Xs = selectEVar (GE)
	in
	  if nonIndex (r, Xs) then X :: Xs
	  else Xs
	end

    (* searchEx' max (GE, sc) = acc'

       Invariant: 
       If   GE is a list of EVars to be instantiated
       and  max is the maximal number of constructors
       then if an instantiation of EVars in GE is found Success is raised
            otherwise searchEx' terminates with []
    *)
    (* contexts of EVars are recompiled for each search depth *)
    fun searchEx' max (metaLen, nil, sc) = sc ()
        (* Possible optimization: 
	   Check if there are still variables left over
	*)
      | searchEx' max (metaLen, (X as I.EVar (r, G, V, _)) :: GE, sc) =
          AbsMachine2.gBoundedSolve
          (max, PTCompile.compileGoal false V, I.ctxLength(G) - metaLen,
           Compile2.compileCtx false G,
           fn U' => (Unify.unify (G, (X, I.id), (U', I.id));
                     searchEx' max (metaLen, GE, sc))
                    handle Unify.Unify _ => ())

    (* deepen (f, P) = R'

       Invariant:
       If   f function expecting parameters P
         checking the variable MTPGlobal.maxLevel
       then R' is the result of applying f to P and 
	 traversing all possible numbers up to MTPGlobal.maxLevel
    *)
    fun deepen depth trail f =
	let 
	  fun deepen' level = 
	    if level > depth then ()
	    else (if !Global.chatter > 5 then print "#" else (); 
		    (trail (fn () => f level);
		     deepen' (level+1)))
	in
	  deepen' 1
	end

    (* searchEx (G, GE, (V, s), sc) = acc'
       Invariant:
       If   G |- s : G'   G' |- V : level
       and  GE is a list of EVars contained in V[s]
	 where G |- X : VX
       and  sc is a function to be executed after all non-index variables have
	 been instantiated
       then acc' is a list containing the one result from executing the success continuation 
	 All EVar's got instantiated with the smallest possible terms.
    *)    

    fun searchMore (metaLen, it, depth) (nil, sc) = sc ()
      | searchMore (metaLen, 0, depth) (GE, sc) = ()
      | searchMore (metaLen, it, depth) (GE, sc) =
        (if !Global.chatter > 5 then print "[Search: " else ();
         deepen depth AbsMachine2.trail
         (fn max =>
          searchEx' max
          (metaLen,
           selectEVar (GE),
           fn () =>
           (if !Global.chatter > 5 then print "OK]\n" else ();
            let
              val GE' = foldr (fn (X as I.EVar (_, G, _, _), L) =>
                               Abstract.collectEVars (G, (X, I.id), L))
                              nil GE
              val gE' = List.length GE'
            in
              searchMore (metaLen, it-1, depth) (GE', sc)
            end)));
         if !Global.chatter > 5 then print "FAIL]\n" else ())

    fun collectSpine (G, I.Nil, L) = L
      | collectSpine (G, I.App(U, S), L) =
          collectSpine (G, S, Abstract.collectEVars (G, (U, I.id), L))

    fun occursInFor (k, F.True) = false
      | occursInFor (k, F.Ex (I.Dec (_, V), F)) =
        (case Abstract.occursInExp (k, Whnf.normalize(V, I.id))
           of I.No => occursInFor (k+1, F)
            | _ => true)

    (* compileEx (G, F) = (Xs', P')
      
       Invariant:
       If   |- G ctx
       and  G |- F = [[x1:A1]] .. [[xn::An]] formula
       then Xs' = (X1', .., Xn') a list of EVars
       and  G |- Xi' : A1 [X1'/x1..X(i-1)'/x(i-1)]          for all i <= n
       and  G; D |- P' = <X1', <.... <Xn', <>> ..> in F     for some D
    *)
    fun compileEx (F.True) = C.True
      | compileEx (F.Ex (D as I.Dec (_, V), F)) =
        if occursInFor (1, F)
          then C.Exists (D, compileEx F)
        else C.And (compileEx F, V, PTCompile.compileGoal false V)

    fun uncompileSpine (I.Nil) = F.Unit
      | uncompileSpine (I.App (U, S)) = F.Inx (U, uncompileSpine S)

    fun checkSpine (G, _ (* (F.True,_) *), I.Nil) = ()
      | checkSpine (G, (F.Ex (I.Dec (_, V), F), s), I.App (U, S)) =
        (TypeCheck.typeCheck (G, (U, Whnf.normalize (V, s)));
         checkSpine (G, (F, I.Dot (I.Exp (U), s)), S))

    (* search (GE, sc) = ()

       Invariant:
       GE is a list of uninstantiated EVars
       and sc is a success continuation : int -> unit
     
       Side effect:
       success continuation will raise exception 
    *)
    (* Shared contexts of EVars in GE may recompiled many times *)
    fun searchEx (maxFill, G, F, sc) =
        let
          val r = compileEx F
          val G' = Compile1.compileCtx false G
          val metaLen = I.ctxLength G
          (*
          val Gn = Names.ctxLUName G
          val _ = print (CPrint.sProgToString ())
          val _ = print (CPrint.dProgToString G')
          val _ = print (CPrint.clauseToString "" (Gn, r))
          *)
        in
          if !Global.chatter > 5 then print "[Search: " else ();
          deepen maxFill AbsMachine1.trail
          (fn max =>
           AbsMachine1.rBoundedSolve
           (max, r, 0, G',
            fn S =>
            (if !Global.chatter > 5 then print "OK]\n" else ();
             searchMore (metaLen, 1, 1)
               (collectSpine (G, S, nil),
                fn () =>
                (if !Global.doubleCheck then checkSpine (G, (F, I.id), S) else ();
                 sc (max, uncompileSpine S))))));
          if !Global.chatter > 5 then print "FAIL]\n" else ()          
        end

  in 
    val searchEx = searchEx
  end (* local ... *)

end; (* functor Search *)
 
