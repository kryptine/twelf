(* Filling: Version 1.3 *)
(* Author: Carsten Schuermann *)

signature MTPFILLING = 
sig
  structure FunSyn : FUNSYN
  structure StateSyn : STATESYN

  exception Error of string

  type operator

  val expand : StateSyn.State -> operator 
  val expandItDeep : StateSyn.State -> operator 
  val expandTabled : StateSyn.State -> operator 
  val apply : operator -> (int * FunSyn.Pro)
  val menu : operator -> string
  val tableReset : unit -> unit
end; (* signature MTPFILLING *)


