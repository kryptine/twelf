(* Global parameters *)
(* Author: Carsten Schuermann *)

signature MTPGLOBAL =
sig

  structure MetaGlobal : METAGLOBAL 

  datatype ProverType = datatype MetaGlobal.ProverType 

  val prover : ProverType ref

  val maxFill : int ref
  val maxSplit : int ref
  val maxRecurse : int ref
end;  (* signature MTPGLOBAL *)
