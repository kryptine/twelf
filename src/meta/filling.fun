(* Filling  Version 1.3*)
(* Author: Carsten Schuermann *)

functor MTPFilling (structure IntSyn : INTSYN
                    structure FunSyn' : FUNSYN
		      sharing FunSyn'.IntSyn = IntSyn
                    structure StateSyn' : STATESYN
		      sharing StateSyn'.FunSyn = FunSyn'
		    structure Abstract : ABSTRACT
		      sharing Abstract.IntSyn = IntSyn
                    structure TypeCheck : TYPECHECK
                      sharing TypeCheck.IntSyn = IntSyn
		    structure MTPData : MTPDATA
		    structure Search   : MTPSEARCH
  		      sharing Search.StateSyn = StateSyn'
		    structure Whnf : WHNF
		      sharing Whnf.IntSyn = IntSyn)
  : MTPFILLING =
struct
  structure FunSyn = FunSyn'
  structure StateSyn = StateSyn'

  exception Error of string

  type operator = (unit -> int * FunSyn'.Pro)

  local
    structure S = StateSyn
    structure I = IntSyn

    exception Success of int * FunSyn'.Pro

    (* Checking for constraints: Used to be in abstract, now must be done explicitly! --cs*)

(*    fun checkConstraints nil = raise Success
      | checkConstraints (X :: L) = 
        if Abstract.closedExp (I.Null, (Whnf.normalize (X, I.id), I.id)) then checkConstraints L
	else ()
*)

    (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
    fun expand (S as S.State (n, (G, B), (IH, OH), d, O, H, F)) = 
	let 
	  val _ = if (!Global.doubleCheck) then TypeCheck.typeCheckCtx (G) else ()
	in
	  fn () => ((Search.searchEx (!MTPGlobal.maxFill, G, F,
                                     fn s => raise Success s);
                     raise Error "Filling unsuccessful")
                    handle Success (s as (max, _)) =>
                      (MTPData.maxFill := Int.max (!MTPData.maxFill, max);
                       s))
	end
    

    (* apply op = B' 

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)
    fun apply f = f ()

    (* menu op = s'
       
       Invariant: 
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
    fun menu _ =  "Filling   (tries to close this subgoal)" 
      
  in
    val expand = expand
    val apply = apply
    val menu = menu
  end (* local *)
end; (* functor Filling *)
