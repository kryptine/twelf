(* Meta Global parameters *)
(* Author: Carsten Schuermann *)

functor MTPGlobal 
  (structure MetaGlobal : METAGLOBAL): MTPGLOBAL =
struct

  structure MetaGlobal = MetaGlobal

  datatype ProverType = datatype MetaGlobal.ProverType   

  val prover = MetaGlobal.prover

  val maxFill = MetaGlobal.maxFill
  val maxSplit = MetaGlobal.maxSplit
  val maxRecurse = MetaGlobal.maxRecurse
end; (* structure MTPGlobal *)
