(* Operational Semantics for Delphin *)
(* Author: Carsten Schuermann *)

signature OPSEM = 
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)

  exception NoMatch

  val evalPrg : Tomega.Prg -> Tomega.Prg
  val createVarSub : Tomega.Dec IntSyn.Ctx * Tomega.Dec IntSyn.Ctx -> Tomega.Sub
  val matchSub : Tomega.Dec IntSyn.Ctx * Tomega.Sub * Tomega.Sub -> unit
end
