(* Operational Semantics for Delphin *)
(* Author: Carsten Schuermann *)

signature OPSEM = 
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)

  val evalPrg : Tomega.Prg -> Tomega.Prg
end
