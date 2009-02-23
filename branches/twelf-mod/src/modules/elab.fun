structure Elab : ELAB =
struct
  structure I = IntSyn
  structure M = ModSyn
  
  (* the following methods are all that the module system needs about the semantics of the non-modular syntax *)
  
  (*
     N: Normalized: no Redex, no EVar (SOME _)
     A: Abstracted: no EVar, no FVar, implicit arguments Pi-bound
     E: Abbrevs expanded: no NSDef
  *)

  (* check whether n = U : V can be a strict definition
     (only needed as an optimization to return ConDefs if possible) *)
  fun checkStrict(U : I.Exp, V : I.Exp) : bool = (Strict.check((U,V), NONE); true) handle Strict.Error _ => false
  (* check whether U has type/kind V *)
  (* pre: NAE *)
  fun checkType(U : I.Exp, V : I.Exp) : bool = (TypeCheck.check(U,V); true) handle TypeCheck.Error _ => false
  (* check whether U has type/kind V *)
  (* pre: NAE *)  
  fun checkEqual(U : I.Exp, U' : I.Exp) : bool = Conv.conv((U, I.id), (U', I.id))
  (* normalizes an expression *)
  (* pre: true; post: NE *)
  fun normalize(U : I.Exp) : I.Exp = Whnf.normalize(U, I.id)
  (* abstracts away free variables left over after type reconstruction *)
  (* pre: true; post: NAE, #1 is number of implicit arguments *) 
  fun abstract(U : I.Exp) : I.Exp = #2 (Abstract.abstractDecImp U)
  
  exception Error of string                       (* raised on type-checking errors *)
  exception UndefinedMorph of IDs.mid * IDs.cid   (* raised if partially defined view cannot be applied *)
  exception FixMe                                 (* raised for unimplemented cases *)


  (********************** Module level type checking **********************)
  
  (* reconstructs the type, i.e., domain and codomain of a morphism and checks whether it is well-formed *)
  fun reconMorph(M.MorComp(mor1,mor2)) =
        let
           val (d1,c1) = reconMorph mor1
           val (d2,c2) = reconMorph mor2
        in
           if (c1 = d2)
           then (d1,c2)
           else raise Error("morphisms not composable")
        end
    | reconMorph(M.MorStr(s)) = ((M.strDecDom (M.structLookup s), IDs.midOf(s))
                              handle M.UndefinedCid _ => raise Error("non-structure symbol reference in morphism"))
    | reconMorph(M.MorView(m)) =
        let
           val M.ViewDec(_,dom, cod) = M.modLookup m
                                        handle M.UndefinedMid _ => raise Error("non-view module reference in morphism")
        in
           (dom, cod)
        end
  (* checks the judgment |- mor : dom -> cod *)
  fun checkMorph(mor, dom, cod) =
     if reconMorph mor = (dom, cod)
     then ()
     else raise Error("morphism does not have expected type")
  
  (* auxiliary function of findClash
     if s is in forbiddenPrefixes, instantiations of s.c are forbidden
     if c is in forbiddenCids, instantiations of c are forbidden
  *)
  fun findClash'(nil, _, _) = NONE
    | findClash'(inst :: insts, forbiddenPrefixes, forbiddenCids) =
        let
           val c = M.symInstCid inst
        in
           (* check whether c is in the list of cids of forbidden cids *)
           if List.exists (fn x => x = c) forbiddenCids
           then SOME(c)
           else
              let
              	 (* get the list of proper prefixes of c *)
                 val prefixes = List.map #1 (M.symQid c)
              in
                 (* check whether a prefix of c is in the list of forbidden prefixes *)
                 if List.exists (fn p => List.exists (fn x => x = p) forbiddenPrefixes) prefixes
            	 then SOME(c)
            	 (* forbid futher instantiations of
            	    - anything that has c as a prefix
            	    - c and any prefix of c *)
                 else findClash'(insts, c :: forbiddenPrefixes, c :: prefixes @ forbiddenCids)
              end
        end
  (* checks whether two instantiations in insts clash
     - return NONE if no clash
     - returns SOME c if an instantation for c is the first one leading to a clash
     a clash arises if there are instantiations for both
     - c and c, or
     - s and s.c
  *)
  fun findClash(insts) = findClash'(insts, nil, nil)

  (* auxiliary functions of checkStrDec and checkSigIncl, checks whether the intended domain is permitted *)
  fun checkDomain(dom : IDs.mid) =
      let
      	 (* no ancestors may be instantiated *)
      	 val scope = M.getScope()
         val _ = if List.exists (fn x => x = dom) scope
                 then raise Error("signature attempts to instantiate or include own ancestor")
                 else ()
         (* only children of ancestors may be instantiated *)
         val par = valOf (M.modParent dom) (* NONE only if dom is toplevel, which is caught above *)
         val _ = if not (List.exists (fn x => x = par) scope)
                 then raise Error("signature attempts to instantiate or include unreachable signature")
                 else ()
      in
         ()
      end  
  fun checkIncludes(dom : IDs.mid, cod : IDs.mid) =
      let
         (* all includes of the domain must also be included in the codomain *)
         val domincl = M.modInclLookup dom
         val _ = case List.find (fn x => not(M.modInclCheck(x,cod))) domincl
              of NONE => ()
               | SOME x => raise Error("signature " ^ M.modFoldName x ^ " included into " ^ M.modFoldName dom ^
                                       " but not into " ^ M.modFoldName cod)
      in
         ()
      end
  
  (* checks well-typedness condition for includes *)
  fun checkModIncl(M.SigIncl (m,_)) = checkDomain m

  (* checks simple well-typedness conditions for structure declarations
     does not check:
     - all instantiations instantiate domain symbols with codomain expressions
       already checked during parsing/reconstruction
     - all instantiations are well-typed and preserve equalities
       will be checked during flattening
     postcondition: getInst yields all information that is needed to check the latter during flattening
  *)
  fun checkStrDec(M.StrDec(_,_, dom, insts, _)) = (
        checkDomain(dom);
        checkIncludes(dom, M.currentMod());
        case findClash insts
          of SOME c => raise Error("multiple (possibly induced) instantiations for " ^
                                    M.symFoldName c ^ " in structure declaration")
           | NONE => ()
        )
    | checkStrDec(M.StrDef(_,_, dom, mor)) = (
        checkDomain(dom);
        checkMorph(mor, dom, M.currentMod())
      )

  fun checkModDec(M.ViewDec(_, dom, cod)) = checkIncludes(dom, cod)
    | checkModDec(M.SigDec _) = ()

 (********************** Semantics of the module system **********************)
  (* auxiliary methods to get Exps from cids *)
  fun headToExp h = I.Root(h, I.Nil)
  fun cidToExp c = (case (M.sgnLookup c)
		      of (I.ConDec _) => headToExp(I.Const c)
		       | (I.ConDef _) => headToExp (I.Def c)
		       | (I.AbbrevDef _) => headToExp (I.NSDef c))
		      
  fun applyMorph(U, mor) =
     let
     	val (dom, cod) = reconMorph mor
     	fun A(I.Uni L) = I.Uni L
     	  | A(I.Pi((D, P), V)) = I.Pi((ADec D, P), A V)
     	  | A(I.Root(H, S)) = I.Redex(AHead H, ASpine S)  (* return Redex because AHead H need not be a Head again *)
     	  | A(I.Redex(U, S)) = I.Redex(A U, ASpine S)
     	  | A(I.Lam(D, U)) = I.Lam(ADec D, A U)
(*     	  | A(I.EVar(E, C, U, Constr)) = impossible by precondition *)
          | A(I.EClo(U,s)) = I.EClo(A U, ASub s)
(*          | A(I.AVar(I)) = impossible by precondition *)
          | A(I.FgnExp(cs, F)) = raise FixMe
          | A(I.NVar n) = I.NVar n
        and AHead(I.BVar k) = headToExp(I.BVar k)
          | AHead(I.Const c) = ACid c            (* apply morphism to constant *)
          | AHead(I.Proj(b,k)) = headToExp(I.Proj (ABlock b, k))
          | AHead(I.Skonst c) = ACid c           (* apply morphism to constant *)
          | AHead(I.Def d) = A (M.constDef d)    (* expand definition *)
          | AHead(I.NSDef d) = A (M.constDef d)  (* expand definition *)
          | AHead(I.FVar(x, U, s)) = headToExp(I.FVar(x, A U, ASub s))
          | AHead(I.FgnConst(cs, condec)) = raise FixMe
        and ASpine(I.Nil) = I.Nil
          | ASpine(I.App(U,S)) = I.App(A U, ASpine S)
          | ASpine(I.SClo(S,s)) = I.SClo(ASpine S, ASub s)
        and ASub(I.Shift n) = I.Shift n
          | ASub(I.Dot(Ft,s)) = I.Dot(AFront Ft, ASub s)
        and AFront(I.Idx k) = I.Idx k
          | AFront(I.Exp U) = I.Exp (A U)
          | AFront(I.Axp U) = I.Axp (A U)
          | AFront(I.Block b) = I.Block (ABlock b)
          | AFront(I.Undef) = I.Undef
        and ADec(I.Dec(x,V)) = I.Dec(x, A V)
(*          | ADec(I.BDec(v,(l,s))) = impossible by precondition *)
          | ADec(I.ADec(v,d)) = I.ADec(v,d)
          | ADec(I.NDec v) = I.NDec v
        and ABlock(I.Bidx i) = I.Bidx i
(*          | ABlock(I.LVar(b,s,(c,s'))) = impossible by precondition  *)
          | ABlock(I.Inst l) = I.Inst (List.map A l)
(*      and AConstr(_) = impossible by precondition  *)
        (* apply morphism to constant *)
        and ACid(c) =
           if not(IDs.midOf c = dom)
           then cidToExp c   (* included constants are mapped to themselves *)
           else case mor
             of M.MorStr(s) => cidToExp(valOf(M.structMapLookup (s,c)))    (* get the cid to which s maps c *)
              | M.MorView(m) => (
                  let val ModSyn.ConInst(_, exp) = ModSyn.conInstLookup(m, IDs.lidOf(c))
                  in exp
                  end
                  handle ModSyn.UndefinedCid _ => raise UndefinedMorph(m,c)
                )
              | M.MorComp(mor1, mor2) => applyMorph(applyMorph(cidToExp(c), mor1), mor2)
     in
     	A U
     end
  
  (* auxiliary function of getInst, its first argument is a list of instantiations *)
  fun getInst'(nil, c, q) = NONE
    | getInst'(inst :: insts, c, q) = (
        case inst
           (* if c is instantiated directly, return its instantiation *)
           of M.ConInst(c', e) =>
              if c' = c
              then SOME e
              else getInst'(insts, c, q)
           (* if c can be addressed as c' imported via s, and if s is instantiated with mor,
              return the application of mor to c' *)
            | M.StrInst(s, mor) => (
                case IDs.preimageFromQid(s, q)
                  of SOME c' => SOME (applyMorph(cidToExp c', mor))
                   (* otherwise, try next instantiation *)
                   | NONE => getInst'(insts, c, q)
                )
      )
  (* finds an instantiation for cid c having qids q in a structure declaration
     this finds both explicit instantiations (c := e) and induced instantiations (s := mor in case c = s.c')
     in StrDefs, the instantiation is obtained by applying the definition of the structure to c
  *)
  fun getInst(M.StrDec(_,_,_,insts, _), c, q) = getInst'(insts, c, q)
    | getInst(M.StrDef(_,_,_,mor), c, _) = SOME (applyMorph(cidToExp c, mor))
  
  (* flattens a structure by computing all generated declarations (the order is depth first declaration order)
     - S: cid of the structure to be flattened
     - installConDec(c', condec): called for every generated constant declaration
       - c': the cid of the declaration in the domain
       - condec the generated declaration in the codomain
       - returns: the cid of the generated declaration
     - installStrDec: as installConDec, but for generated structure declarations
  *)
  (* variable naming convention:
     - flattened structure: upper case
     - declaration in domain: primed lower case
     - induced declaration in codomain: unprimed lower case
  *)
  fun flattenDec(S : IDs.cid, installConDec : IDs.cid * I.ConDec -> IDs.cid, installStrDec : IDs.cid * M.StrDec -> IDs.cid) =
     let
     	val Str = M.structLookup S
     	val Name = M.strDecName Str
     	val Q = M.strDecQid Str
     	val Dom = M.strDecDom Str
     	(* holds the list of pairs (s',s) of original and induced structure ids *)
     	val structMap : (IDs.cid * IDs.cid) list ref = ref nil
     	(* applies structMap to the first components of the pairs in q *)
     	fun applyStructMap(q: IDs.qid) = List.map (fn (x,y) => (#2 (valOf (List.find (fn z => #1 z = x) (!structMap))), 
     	                                                y)
     	                                          ) q
     	(* auxiliary function used in translated ConDec to unify the cases of ConDef and AbbrevDef *)
     	fun translateDefOrAbbrev(c', name', q', imp', def', typ', uni', anc'Opt) =
              let
                 val typ = normalize (applyMorph(typ', M.MorStr(S)))
                 val defold = applyMorph(def', M.MorStr(S))
                 val defnew = case getInst(Str, c', q')  
                    of SOME def =>  
                       (* if existing definitions are overridden, equality must be checked *)
                       if checkEqual(defold, def)
                       then normalize def
                       else raise Error("clash between instantiation and translation of existing definiton for constant " ^
                                         M.symFoldName c')
                    | NONE => normalize defold
                 val _ = if checkType(defnew, typ)
                         then ()
                         else raise Error("instantiation of " ^ M.symFoldName c' ^ " ill-typed")
                 val q = (S, c') :: (applyStructMap q')
              in 
                 if false (* not (anc'Opt = NONE) andalso uni' = I.Type andalso checkStrict(defnew, typ) *)
                 (* return a ConDef if the input was a term-level ConDef and strictness is preserved *)
                 then I.ConDef(Name @ name', q, imp', defnew, typ, uni', valOf anc'Opt) (* @CS: ancestor wrong *)
                 (* otherwise return AbbrevDef *)
                 else I.AbbrevDef(Name @ name', q, imp', defnew, typ, uni')
              end
     	   
     	(* translates a constant declaration (with id c') along S *)
        (* This function must be changed if this code is reused for a different internal syntax.
           It would be nicer to put it on toplevel, but that would be less efficient. *)
        fun translateConDec(c', I.ConDec(name', q', imp', stat', typ', uni')) =
              let
                 val typ = normalize (applyMorph(typ', M.MorStr(S)))
                 val q = (S, c') :: (applyStructMap q')
              in
                 case getInst(Str, c', q')
                   of SOME def =>
                       let val defn = normalize def
                       in if checkType(defn, typ)
                          then I.AbbrevDef(Name @ name', q, imp', defn, typ, uni') (* @FR: can this be a ConDef? *)
                          else raise Error("instantiation of " ^ M.symFoldName c' ^ " ill-typed")
                       end
                    | NONE =>
                      I.ConDec(Name @ name', q, imp', stat', typ, uni')
              end
           | translateConDec(c', I.ConDef(name', q', imp', def', typ', uni', anc')) =
               translateDefOrAbbrev(c', name', q', imp', def', typ', uni', SOME anc')
           | translateConDec(c', I.AbbrevDef(name', q', imp', def', typ', uni')) =
               translateDefOrAbbrev(c', name', q', imp', def', typ', uni', NONE)
           | translateConDec(_, I.BlockDec(_, _, _, _)) = raise FixMe
           | translateConDec(_, I.SkoDec(_, _, _, _, _)) = raise FixMe
        (* takes the declaration c' from the instantiated signature and computes and installs the translated declaration *)
     	fun flatten1(c' : IDs.cid) =
     	   case M.symLookup c'
              of M.SymCon(con') => (
                   installConDec (c', translateConDec(c', con'));
                   ()
                 )
               | M.SymStr(str') =>
                (* translates a structure declaration (with id s') along S and adds an entry to structMap *)
                let
                   val s' = c'
                   val name' = M.strDecName str'
                   val q' = M.strDecQid str'
                   val dom' = M.strDecDom str'
                   val q = (S, s') :: (applyStructMap q')
                   val s = installStrDec (s', M.StrDef(Name @ name', q, dom', M.MorComp(M.MorStr(s'), M.MorStr(S))))
                   val _ = structMap := (s',s) :: (! structMap)
                in
                   ()
                end
     in
     	(* calls flatten1 on all declarations of the instantiated signature (including generated ones) *)
     	M.sgnApp(Dom, flatten1)
     end

  fun flattenInst(instID : IDs.cid, installInst : M.SymInst -> IDs.cid) =
     let
        val viewID = IDs.midOf instID
        val M.SymStrInst(M.StrInst(s, mor)) = M.symLookup instID
        val (dom, _) = reconMorph mor
        fun flatten1(c' : IDs.cid) =
           let 
              val c = valOf (M.structMapLookup(s,c'))
              val _ = case M.symLookup c'
                 of M.SymCon _ =>
                   let
                      val defCod = normalize (applyMorph(cidToExp c', mor))
                      val typDomTrans = normalize(applyMorph(M.constType c, M.MorView viewID))
                      val _ = if checkType(defCod, typDomTrans)
                              then ()
                              else raise Error("type mismatch in induced instantiation of " ^ M.symFoldName c)
                      val _ = case M.constDefOpt c
                                of NONE => ()
                                 | SOME defDom =>
                                   if checkEqual(applyMorph(defDom, M.MorView viewID), defCod)
                                   then ()
                                   else raise Error("clash between induced instantiation and translation of existing definition of " ^ M.symFoldName c)
                   in
                      installInst(M.ConInst(c, defCod))
                   end
                  | M.SymStr _ => installInst(M.StrInst(c, M.MorComp(M.MorStr c', mor)))
           in
              () 
           end
     in
        M.sgnApp(dom, flatten1)
     end

(********************** another type checking method **********************)
  fun checkSymInst(M.ConInst(con, term)) =
     let
     	val v = M.currentMod()
     	val typ = M.constType con
     	val expTyp = applyMorph(typ, M.MorView v)
     in
     	if checkType(term, expTyp)
     	then ()
        else raise Error("type mismatch")
     end
    | checkSymInst(M.StrInst(str, mor)) =
     let
     	val expDom = M.strDecDom (M.structLookup str)
     in
     	checkMorph(mor, expDom, M.currentTargetSig())
     end
end