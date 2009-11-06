(* Syntax and semantics of the module system, also encapsulation of the state of modular LF *)
(* Author: Florian Rabe *)

(* The datatypes and interface methods are well-documented in the declaration of MODSYN. *)
functor ModSyn (structure IntSyn : INTSYN)
  : MODSYN =
struct
  structure CH = CidHashTable
  structure CCH = HashTable (type key' = IDs.cid * IDs.cid
             val hash = fn (x,y) => 100 * (IDs.cidhash x) + (IDs.cidhash y)
             val eq = (op =));
  structure MH = MidHashTable
  structure I = IntSyn

  exception Error of string
  exception UndefinedCid of IDs.cid
  exception UndefinedMid of IDs.mid

  datatype OpenDec = OpenDec of (IDs.Qid * string) list | OpenAll
  datatype Morph = MorStr of IDs.cid | MorView of IDs.mid | MorComp of Morph * Morph
  datatype SymInst = ConInst of IDs.cid * (IDs.cid option) * I.Exp | StrInst of IDs.cid * (IDs.cid option) * Morph
  datatype ModIncl = SigIncl of IDs.mid * OpenDec | ViewIncl of Morph
  datatype StrDec = StrDec of string list * IDs.qid * IDs.mid * (ModIncl list) * (SymInst list) * OpenDec * bool
                  | StrDef of string list * IDs.qid * IDs.mid * Morph * bool
  datatype ModDec = SigDec of string * string list | ViewDec of string * string list * IDs.mid * IDs.mid * bool
  datatype Read = ReadFile of string

  (* unifies constant and structure declarations and instantiations *)
  datatype SymLevelData = SymCon of I.ConDec | SymStr of StrDec | SymConInst of SymInst | SymStrInst of SymInst

  fun modDecBase (SigDec(b,_)) = b
    | modDecBase (ViewDec(b,_,_,_,_)) = b
  fun modDecName (SigDec(_,n)) = n
    | modDecName (ViewDec(_,n,_,_,_)) = n
  fun strDecName (StrDec(n, _, _, _, _, _, _)) = n
    | strDecName (StrDef(n, _, _, _, _)) = n
  fun strDecFoldName s =  IDs.mkString(strDecName s,"",".","")
  fun strDecQid (StrDec(_, q, _, _, _, _, _)) = q
    | strDecQid (StrDef(_, q, _, _, _)) = q
  fun strDecDom (StrDec(_, _, m, _, _, _, _)) = m
    | strDecDom (StrDef(_, _, m, _, _)) = m
  fun strDecImpl (StrDec(_, _, _, _, _, _, i)) = i
    | strDecImpl (StrDef(_, _, _, _, i)) = i

  fun symInstCid(ConInst(c, _, _)) = c
    | symInstCid(StrInst(c, _, _)) = c
  fun symInstOrg(ConInst(_, O, _)) = O
    | symInstOrg(StrInst(_, O, _)) = O

  (********************** Stateful data structures **********************)

  (* Invariants:
   Defined lookups
   - modLookup m is defined for all 0 <= m < ! nextMid (defined for 0 only after initialization)
   - if modLookup m = SigDec _, then symLookup(m,l) is defined for all 0 <= l < modSize(m)
   - if modLookup m = ViewDec(_,d,_), then symLookup(m,l) yields the instantiation for (d,l)
   
   Stored declarations
   - if modLookup m = SigDec _, then symLookup(m,l) = SymCon _ or = SymStr _
   - if modLookup m = ViewDec _, then symLookup(m,l) = SymConInst _ or = _ SymStrInst
   - if symLookup c = SymCon d, then d is valid and in normal form
   - if symLookup c = SymCon (ConDef _), then the definition is strict in all its arguments
   - I.Const(c) is valid iff symLookup c = SymCon (ConDec _)
   - I.Def(c) is valid   iff symLookup c = SymCon (ConDef _)
   - I.NSDef(c) is valid iff symLookup c = SymCon (AbrevDef _)
   
   Qids
	Qids are redundant and maintained for efficiency only. That enables fast lookup of deep instantiations of qualified identifiers.
   Every declaration for s_1. ... .s_n.c generated by elaborating a structure can be seen as the result of applying
   - s_1. ... .s_n to c,
   - s_1. ... .s_{n-1} to s_n.c,
   - ..., or
   - s_1 to s_2. ... .s_n.c.
   If symTable contains (cid, condec) and cid represents the constant s_1. ... .s_n.c, then
   - (conDecQid condec) is [(CID(s_1. ... .s_n), CID(c)), ... ,(CID(s_1), CID(s_2. ... .s_n.c))],
   - (conDecName condec) is [s_1, ..., s_n, c].
   Here n = 0 iff a declaration is not generated elaborating a structure.
   For structures, the corresponding invariant holds.
   For structures, also the inverse of this mapping cid -> qid is maintained:
   structMapTable contains for pairs (S,s') of structure ids, the id of the structure arising from applying S to s'.
  *)

  (* modTable maps a mid m to a tuple of
     - a module declaration (modLookup m)
     - its size (-1 if the module is still open) (modSize m)
     - the parent modules, i.e., the value of ! scope immediately before the start of the module (modParent m)
     - the list of includes (modInclLookup m)
  *)
  (* A signature M may validly refer to a symbol newcid(m,l) iff that symbol exists and one of the following holds
     - m = M
     - m is included into M (inclusion is transitive)
     - (m,l') is in modParent M and l < l'
  *)
  val modTable : (ModDec * int * ((IDs.mid * IDs.lid) list) * (ModIncl list)) MH.Table = MH.new(499)
  (* symTable maps cids to constant and structure declarations and instantiations *)
  val symTable : SymLevelData CH.Table = CH.new(19999)
  (* structMapTable maps pairs of (CID(S), CID(c')) of structure and structure/constant ids to the structure/constant id CID(S.c') *)
  val structMapTable : IDs.cid CCH.Table = CCH.new(1999)
    
  (* scope holds a list of the currently opened modules and their next available lid (in inverse declaration order) *)
  val scope : (IDs.mid * IDs.lid) list ref = ref nil
  (* the next available module id *)
  val nextMid : IDs.mid ref = ref 0
  
  (* implicit coercions: (T,m) in implicitOut(S) iff (S,m) in implicitIn(T) iff T can be coerced to S via m:S->T
     chained coercions are precomputed *)
  val implicitOut : (IDs.mid * Morph) list MH.Table = MH.new(50)
  val implicitIn  : (IDs.mid * Morph) list MH.Table = MH.new(50)

  (********************** Effect-free (lookup) methods **********************)
  fun modLookup(m : IDs.mid) = #1 (valOf (MH.lookup modTable m))
                               handle Option => raise UndefinedMid(m)
  fun modSize(m : IDs.mid) =
     case List.find (fn (x,_) => x = m) (! scope)
        of SOME (_,l) => l                             (* size of open module stored in scope *)
         | NONE => #2 (valOf (MH.lookup modTable m))   (* size of closed module stored in modTable *)
                   handle Option => raise UndefinedMid(m)
  fun modParent(m : IDs.mid) = #3 (valOf (MH.lookup modTable m))
                               handle Option => raise UndefinedMid(m)
  fun modInclLookup(m : IDs.mid) = #4 (valOf (MH.lookup modTable m))
                               handle Option => raise UndefinedMid(m)
  fun sigInclLookupTrans(m : IDs.mid) =
  let
     val found : IDs.mid list ref = ref nil
     fun aux(n : IDs.mid) =
     let
     	val new = List.mapPartial
     	         (fn SigIncl(x,_) => if List.exists (fn y => x = y) (! found) then NONE else SOME x)
     	         (modInclLookup n)
     in
        found := new @ (! found);
        List.map aux new;
        ! found
     end
  in
     aux(m)
  end

  fun currentMod() = #1 (hd (! scope))
  fun currentTargetSig() =
     let val m = currentMod()
     in case modLookup m
       of SigDec _ => m
        | ViewDec(_,_,_,cod,_) => cod
     end

  fun getScope () = ! scope
  fun onToplevel() = List.length (! scope) = 1
  fun inCurrent(l : IDs.lid) = IDs.newcid(currentMod(), l)

  (* true: currentMod() is SigDec, false: currentMod() is ViewDec *)
  fun inSignature() = case modLookup (currentMod())
                          of SigDec _ => true
                           | ViewDec _ => false

  fun symLookup(c : IDs.cid) = valOf (CH.lookup(symTable)(c))
                               handle Option => raise (UndefinedCid c)

  fun sgnLookup (c : IDs.cid) = case symLookup c
    of SymCon d => d
     | _ => raise (UndefinedCid c)
  val sgnLookupC = sgnLookup o inCurrent

  fun structLookup(c : IDs.cid) = case symLookup c
    of SymStr d => d
  | _ => raise (UndefinedCid c)
  val structLookupC = structLookup o inCurrent

  fun structMapLookup (S,s') = CCH.lookup structMapTable (S,s')

  fun symQid(c : IDs.cid) = case symLookup c
       of SymCon condec => I.conDecQid condec
        | SymStr strdec => strDecQid strdec

  fun conInstLookup(c : IDs.cid) = case symLookup c
    of SymConInst exp => exp
     | _ => raise (UndefinedCid c)

  fun strInstLookup(c : IDs.cid) = case symLookup c
    of SymStrInst mor => mor
     | _ => raise (UndefinedCid c)

  (* reflexive-transitive closure of include relation
     no caching because presumably no efficiency bottleneck *)
  fun sigInclCheck(from, to) =
     let
     	val mids = List.map (fn SigIncl(m,_) => m) (modInclLookup to)
     in
     	from = to (* reflexivity *)
     	orelse
     	List.exists (fn m => m = from) mids (* base cases *)
     	orelse
        List.exists (fn m => sigInclCheck(from, m)) mids (* transitivity *)
     end
  fun implicitLookupOut(d) = case MH.lookup implicitOut d of SOME l => l | NONE => nil
  fun implicitLookupIn(c)  = case MH.lookup implicitIn  c of SOME l => l | NONE => nil
  fun implicitLookup(d,c)   =
     let val outs = implicitLookupOut(d)
     in case List.find (fn (m, _) => m = c) outs
        of SOME(_, mor) => SOME mor
        | NONE => NONE
     end
  
  (********************** Convenience methods **********************)
  fun constDefOpt (d) =
      (case sgnLookup (d)
	 of I.ConDef(_, _, _, U,_, _, _) => SOME U
	  | I.AbbrevDef (_, _, _, U,_, _) => SOME U
	  | _ => NONE)
  val constDef = valOf o constDefOpt
  fun constType (c) = I.conDecType (sgnLookup c)
  fun constImp (c) = I.conDecImp (sgnLookup c)
  fun constUni (c) = I.conDecUni (sgnLookup c)
  fun constBlock (c) = I.conDecBlock (sgnLookup c)
  fun constStatus (c) =
      (case sgnLookup (c)
	 of I.ConDec (_, _, _, status, _, _) => status
          | _ => I.Normal)
  fun symName(c) =
     case symLookup(c)
       of SymCon condec => IntSyn.conDecName condec
        | SymStr strdec => strDecName strdec
  val sep = "."
  val Sep = ".."
  fun symFoldName(c) = IDs.mkString(symName c ,"",sep,"") 
  fun modName m = modDecName (modLookup m)
  fun modFoldName m = IDs.mkString(modName m ,"",sep,"")
  fun fullFoldName(c) = (if (IDs.midOf c) = 0
                        then ""                                (* toplevel module has no name *)
                        else modFoldName(IDs.midOf c) ^ Sep
                        ) ^ (symFoldName c)
 
  fun modApp(f : IDs.mid -> unit) =
    let
      val length = ! nextMid
      fun doRest(m) = 
	if m = length then () else ((f m); doRest(m+1))
    in
      doRest(0)
    end
  
  (* changes state if f does *)
  fun sgnApp(m : IDs.mid, f : IDs.cid -> unit) =
    let
      val length = case modLookup m
        of SigDec _ => modSize m
         | ViewDec(_,_,dom,_,_) => modSize dom
      fun doRest(l) =
	if l = length then () else (f(m,l); doRest(l+1))
    in
      doRest(0)
    end
  fun sgnAppC (f) = sgnApp(currentMod(), f)
  
  (* changes state if f does *)
  fun sgnAppI'(m : IDs.mid, f : IDs.cid -> unit, done : IDs.mid list) =
     let
     	fun isNotDone m' = not(List.exists (fn x => x = m') done)
     	val incl = List.filter isNotDone (List.map (fn SigIncl(x,_) => x) (modInclLookup m))
     in
        List.map (fn m' => sgnAppI'(m', f, m :: done)) incl;
        sgnApp(m,f)
     end
  fun sgnAppI(m : IDs.mid, f : IDs.cid -> unit) = sgnAppI'(m,f,nil)
  
  (********************** Effectful methods **********************)
  fun implicitAddOne(dom, cod, mor) =
  let
     val _ = if (sigInclCheck(dom, cod)) then
     	raise Error("coercion from included signature not allowed") else ()
     val outs = implicitLookupOut dom
     val ins = implicitLookupIn cod
     val _ = if (List.exists (fn (c,_) => c = cod) outs) then
     	raise Error("multiple coercions from " ^ modFoldName dom ^ " to " ^ modFoldName cod) else ()
     (* no check needed due to invariant *)
   in (  
     MH.insert implicitOut (dom, (cod, mor) :: outs);
     MH.insert implicitIn  (cod, (dom, mor) :: ins)
   ) end

  fun implicitAdd(dom, cod, mor) =
  let
     val ins  = implicitLookupIn dom
     val outs = implicitLookupOut cod
  in (
     (* add mor *)
     implicitAddOne(dom, cod, mor);
     (* prepend mor to coercions out of cod *)
     List.map (fn (d, m) => implicitAddOne(d, cod, MorComp(m, mor))) ins;
     (* append mor to coercions into dom *)
     List.map (fn (c, m) => implicitAddOne(dom, c, MorComp(mor, m))) outs;
     (* connect coercions into dom and out of cod via mor *)
     List.map (fn (d, m) =>
       List.map (fn (c, n) => implicitAddOne(d, c, MorComp(m, MorComp(mor, n)))) outs
     ) ins;
     ()
  ) end
  
  fun modOpen(dec) =
     let
     	val _ = case (inSignature(), dec)
     	          of (false, _) => raise Error("modules may not occur inside views")
     	           | (true, ViewDec _) => if onToplevel() then () else raise Error("views may not occur inside signatures")
     	           | (true, SigDec _) => ()
        val m = ! nextMid
        val _ = nextMid := ! nextMid + 1
        val _ = MH.insert modTable (m, (dec, ~1, ! scope, nil))
        val _ = scope := (m,0) :: (! scope)
     in
     	m
     end

  fun modClose() =
     let
     	val _ = if onToplevel() then raise Error("no open module to close") else ()
        val (m,l) = hd (! scope)
        val _ = scope := tl (! scope)
        val SOME (a,_,b,c) = MH.lookup modTable m
        val _ = MH.insert modTable (m, (a, l, b, c))
        val _ = case a of ViewDec(_,_,dom,cod,true) => implicitAdd(dom, cod, MorView m)
                        | _ => ()
      in
         ()
      end

  fun inclAddC(incl) =
     let
        val to = currentMod()
        val _ = if modSize to = 0 then () else raise Error("include must occur at beginning of module")
        val SOME (a,b,c,incls) = MH.lookup modTable to
        val _ = MH.insert modTable (to, (a,b,c, incls @ [incl]))
      in
         ()
      end
  
  fun sgnAddC (conDec : I.ConDec) =
    let
      val _ = if inSignature() then () else raise Error("constant declarations only allowed in signature")
      val (c as (m,l)) :: scopetail = ! scope
      val q = I.conDecQid conDec
    in
      CH.insert(symTable)(c, SymCon conDec);
      scope := (m, l+1) :: scopetail;
      (* q = [(s_1,c_1),...,(s_n,c_n)] where every s_i maps c_i to c *)
      List.map (fn sc => CCH.insert structMapTable (sc, c)) q;
      c
    end
      
  fun structAddC(strDec : StrDec) =
    let
      val _ = if inSignature() then () else raise Error("structure declarations only allowed in signature")
      val (c as (m,l)) :: scopetail = ! scope
      val _ = scope := (m, l+1) :: scopetail
      val _ = CH.insert(symTable)(c, SymStr strDec)
      (* q = [(s_1,c_1),...,(s_n,c_n)] where every s_i maps c_i to c *)
      val q = strDecQid strDec
      val _ = List.map (fn sc => CCH.insert structMapTable (sc, c)) q
      val _ = if (strDecImpl strDec) then implicitAdd(strDecDom strDec, m, MorStr c) else ()
    in
      c
    end

  fun instAddC(inst : SymInst) =
    let
      val _ = if inSignature() then raise Error("instantiations only allowed in view") else ()
      val (m,l) :: scopetail = ! scope
      val c' = symInstCid inst
      val c = (m, IDs.lidOf c')
    in
      (case inst
        of ConInst _ => CH.insert(symTable)(c, SymConInst inst)
         | StrInst _ => CH.insert(symTable)(c, SymStrInst inst)
      );
      scope := (m, l+1) :: scopetail;
      c 
    end
   
  (* first file determines base of toplevel *)
  fun newFile(s) = case modLookup 0 of SigDec("", _) => MH.insert modTable (0, (SigDec(s, nil), ~1, nil, nil)) | _ => ()

  fun reset () = (
    CH.clear symTable;               (* clear tables *)
    MH.clear modTable;
    CCH.clear structMapTable;
    MH.clear implicitOut;
    MH.clear implicitIn;
    nextMid := 1;                    (* initial mid and scope *)
    scope := [(0,0)];
    MH.insert modTable (0, (SigDec("", nil), ~1, nil, nil))  (* open toplevel signature *)
  )
 
  (********************** Convenience methods **********************)
  fun ancestor' (NONE) = I.Anc(NONE, 0, NONE)
    | ancestor' (SOME(I.Const(c))) = I.Anc(SOME(c), 1, SOME(c))
    | ancestor' (SOME(I.Def(d))) =
      (case sgnLookup(d)
	 of I.ConDef(_, _, _, _, _, _, I.Anc(_, height, cOpt))
            => I.Anc(SOME(d), height+1, cOpt))
    | ancestor' (SOME _) = (* FgnConst possible, BVar impossible by strictness *)
      I.Anc(NONE, 0, NONE)
  (* ancestor(U) = ancestor info for d = U *)
  fun ancestor (U) = ancestor' (I.headOpt U)

  (* defAncestor(d) = ancestor of d, d must be defined *)
  fun defAncestor (d) =
      (case sgnLookup(d)
	 of I.ConDef(_, _, _, _, _, _, anc) => anc)

  (* targetFamOpt (V) = SOME(cid) or NONE
     where cid is the type family of the atomic target type of V,
     NONE if V is a kind or object or have variable type.
     Does expand type definitions.
  *)
  fun targetFamOpt (I.Root (I.Const(c), _)) = SOME(c)
    | targetFamOpt (I.Pi(_, V)) = targetFamOpt V
    | targetFamOpt (I.Root (I.Def(c), _)) = targetFamOpt (constDef c)
    | targetFamOpt (I.Redex (V, S)) = targetFamOpt V
    | targetFamOpt (I.Lam (_, V)) = targetFamOpt V
    | targetFamOpt (I.EVar (ref (SOME(V)),_,_,_)) = targetFamOpt V
    | targetFamOpt (I.EClo (V, s)) = targetFamOpt V
    | targetFamOpt _ = NONE
      (* Root(Bvar _, _), Root(FVar _, _), Root(FgnConst _, _),
         EVar(ref NONE,..), Uni, FgnExp _
      *)
      (* Root(Skonst _, _) can't occur *)
  (* targetFam (A) = a
     as in targetFamOpt, except V must be a valid type
  *)
  fun targetFam (A) = valOf (targetFamOpt A)

  (* was used only by Flit, probably violates invariants
  fun rename (c, conDec : I.ConDec) =
    CH.insert(symTable)(c, conDec)
   *)
end (* functor ModSyn *)


(* ModSyn is instantiated with IntSyn right away. Both are visible globally. *)
structure ModSyn =
  ModSyn (structure IntSyn = IntSyn);

