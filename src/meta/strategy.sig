(* MTPStrategy : Version 1.3 *)
(* Author: Carsten Schuermann *)

signature MTPSTRATEGY = 
sig
  structure StateSyn : STATESYN

  val run : StateSyn.State list -> StateSyn.State list * StateSyn.State list 
              (* open cases -> remaining cases * solved cases *)

(*  val runTabled : StateSyn.State list -> StateSyn.State list * StateSyn.State list *)

  val tableReset : unit -> unit
end;  (* signature MTPSTRATEGY *)
