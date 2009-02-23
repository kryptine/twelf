(* Reconstruction for modular expressions *)
(* Author: Florian Rabe *)

functor ReconModule
  (structure Global : GLOBAL
   structure Names : NAMES
   structure ReconTerm' : RECON_TERM
   structure ModSyn' : MODSYN
  )
  : RECON_MODULE =
struct

(* implementing the signature MODEXTSYN *)
  structure ExtSyn = ReconTerm'

  type id = string list * Paths.region
  type openids = id list
  
  type morph = id list
  datatype syminst =
     coninst of id * (ExtSyn.term * Paths.region)
   | strinst of id * (morph       * Paths.region)

  datatype strdec = strdec of string * id * (syminst list) * openids
                  | strdef of string * (morph * Paths.region)

  datatype modbegin = sigbegin of string
                    | viewbegin of string * id * id
  
  datatype modincl = sigincl of id * openids
  
(* end MODEXTSYN *)

(* implementing the remaining declarations of RECON_MODULE *)
  exception Error of string

  (* local functions to handle errors *)
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))
  
  datatype Expected = SIG | VIEW | CON | STRUC
  fun expToString SIG = "signature"
    | expToString VIEW = "view"
    | expToString CON = "constant"
    | expToString STRUC = "structure"
        
  fun nameLookupWithError expected (m : IDs.mid, l : IDs.Qid, r : Paths.region) =
     case Names.nameLookup (m,l)
       of SOME c => (
           case (expected, ModSyn.symLookup c)
             of (CON, ModSyn.SymCon _ ) => c
              | (STRUC, ModSyn.SymStr _) => c
              | _ => error(r, "concept mismatch, expected " ^ expToString expected ^ ": " ^ Names.foldQualifiedName l)
          )
        | NONE => error(r, "undeclared identifier: " ^ Names.foldQualifiedName l)

  fun modnameLookupWithError expected (l : IDs.Qid, r : Paths.region) =
     case Names.modnameLookup l
       of SOME m => (
           case (expected, ModSyn.modLookup m)
             of (SIG, ModSyn.SigDec _ ) => m
              | (VIEW, ModSyn.ViewDec _) => m
              | _ => error(r, "concept mismatch, expected " ^ expToString expected ^ ": " ^ Names.foldQualifiedName l)
          )
        | NONE => error(r, "undeclared identifier: " ^ Names.foldQualifiedName l)

  fun morphToMorph(cod : IDs.mid, (mor, r0)) =
     let
     	val (names, r) = List.last mor
     	val init = List.take (mor, (List.length mor) - 1)
     	val (link, nextCod) = let val s = nameLookupWithError STRUC (cod, names, r)
     	                      in (ModSyn.MorStr s, ModSyn.strDecDom (ModSyn.structLookup s))
     	                      end
            handle Error _ => let val m = modnameLookupWithError VIEW (names, r)
                                  val ModSyn.ViewDec(_,dom,_) = ModSyn.modLookup m
                              in (ModSyn.MorView m, dom)
                              end
     in
     	if (init = nil)
     	then link
        else ModSyn.MorComp(morphToMorph(nextCod, (init, r0)), link)
     end

  fun syminstToSymInst(dom : IDs.mid, cod : IDs.mid, inst : syminst, l) =
     case inst
        of coninst((names, r), (term, r')) =>
             let
             	val rr = Paths.join(r,r')
             	val Con = nameLookupWithError CON (dom, names, r)
             	val _ = if (IDs.midOf Con = dom) then () else error(r, "instantiation of included symbol not allowed")
             	(* if inferrable, expType holds the expected type to guide the term reconstruction *)
             	val expType =
             	  if ModSyn.inSignature()
             	  then NONE                                                            (* instantiation in a structure *)
             	  else SOME (Elab.applyMorph(ModSyn.constType Con,
             	                             ModSyn.MorView(ModSyn.currentMod())))     (* instantiation in a view *)
             	       handle Elab.UndefinedMorph(_,c) =>
             	          error(rr, "instantiation for " ^ ModSyn.symFoldName Con ^
             	          " must occur after (possibly induced) instantiation for " ^ ModSyn.symFoldName c)
             	val job = case expType
             	  of NONE => ExtSyn.jterm term
             	   | SOME V => ExtSyn.jof'(term, V)
		val ExtSyn.JTerm((U, _), _, _) = ExtSyn.recon job
                val _ = ExtSyn.checkErrors(rr)
		val (impl, Term) = Abstract.abstractDecImp U
		val _ = if impl > 0 then error(r', "implicit arguments not allowed in instantiation") else ()
		(* val expImpl = ModSyn.constImp Con *)
             in
		ModSyn.ConInst(Con, Term)
		(* error(rr, "mismatch in number of implicit arguments: instantiation " ^ Int.toString impl ^
		                                                                         ", declaration " ^ Int.toString expImpl) *)
             end
        
         | strinst((names, r), mor) =>
             let
             	val Str = nameLookupWithError STRUC (dom, names, r)
             	val Mor = morphToMorph (cod, mor)
             in
             	ModSyn.StrInst(Str, Mor)
             end
  
  fun strdecToStrDec(strdec(name : string, (dom : string list, r1 : Paths.region), insts : syminst list, ids : openids), l) = 
    let
    	val Dom : IDs.mid = modnameLookupWithError SIG (dom, r1)
    	val Cod = ModSyn.currentTargetSig()
    	val Insts = List.map (fn x => syminstToSymInst(Dom, Cod, x,l)) insts
	val Ids = List.map (fn (cname,_) => cname) ids
    in
    	ModSyn.StrDec([name], nil, Dom, Insts, Ids)
    end
    | strdecToStrDec(strdef(name : string, morr), l) =
       let
       	  val Mor = morphToMorph(ModSyn.currentTargetSig(), morr)
       	  val (Dom, _) = Elab.reconMorph Mor (* @FR: taking domain of first link is enough here *)
       in
       	  ModSyn.StrDef([name], nil, Dom, Mor)
       end
    
   fun modbeginToModDec(sigbegin name) = ModSyn.SigDec [name]
     | modbeginToModDec(viewbegin(name, dom, cod)) =
         let
            val Dom = modnameLookupWithError SIG dom
            val Cod = modnameLookupWithError SIG cod
         in
            ModSyn.ViewDec ([name], Dom, Cod)
         end

   fun modinclToModIncl(sigincl (sigid, openids)) =
      let
      	 val m = modnameLookupWithError SIG sigid
	 val Openids = List.map (fn (cname,_) => cname) openids
      in
      	 ModSyn.SigIncl (m, Openids)
      end
end (* end RECON_MODULE *)