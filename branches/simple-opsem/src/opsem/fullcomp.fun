(* Full compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Carsten Schuermann, Larry Greenfield, Roberto Virga *)
(* Modified: Kevin Watkins *)

functor FullComp (structure Global : GLOBAL
                  structure IntSyn' : INTSYN
                  structure CompSyn' : COMPSYN
                    sharing CompSyn'.IntSyn = IntSyn'
                  structure PTCompile : PTCOMPILE
                    sharing PTCompile.IntSyn = IntSyn'
                    sharing PTCompile.CompSyn = CompSyn') : FULLCOMP =
struct

  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'
  structure I = IntSyn

  type DProg = CompSyn.DProg

  (* Static programs --- compiled version of the signature *)
  datatype ConDec =			(* Compiled constant declaration *)
    SClause of CompSyn.ResGoal	        (* c : A                      *)
  | Void 		                (* Other declarations are ignored  *)

  local
    val maxCid = Global.maxCid
    val sProgArray = Array.array (maxCid+1, Void) : ConDec Array.array
  in
    (* Invariants *)
    (* 0 <= cid < I.sgnSize () *)

    fun sProgInstall (cid, conDec) = Array.update (sProgArray, cid, conDec)
    fun sProgLookup (cid) = Array.sub (sProgArray, cid)
    fun sProgReset () = Array.modify (fn _ => Void) sProgArray
  end

  (* compileCtx G = (G, dPool)

     Invariants:
     If |- G ctx,
     then |- G ~> dPool  (context G compile to clause pool dPool)
     and  |- dPool  dpool
  *)
  fun compileCtx fromCS (G) =
      let 
	fun compileCtx' (I.Null) = I.Null
	  | compileCtx' (I.Decl (G, D as I.Dec (_, A))) =
	    let 
	      val a = I.targetFam A
	    in
	      I.Decl (compileCtx' (G), SOME (PTCompile.compileClause fromCS A, I.id, a))
	    end
      in
	CompSyn.DProg (G, compileCtx' (G))
      end

  fun compileGoal V = PTCompile.compileGoal false V

  fun installResGoal (cid, r) = sProgInstall (cid, SClause r)
  fun install fromCS cid =
      (case PTCompile.compileConDec fromCS (I.sgnLookup cid)
         of SOME(r) => installResGoal (cid, r)
          | NONE => ())

  val reset = sProgReset

end
