(* Operational Semantics for Delphin *)
(* Author: Carsten Schuermann *)

signature OPSEM = 
sig
  structure Tomega : TOMEGA

  val evalPrg : Tomega.Prg -> Tomega.Prg
end
