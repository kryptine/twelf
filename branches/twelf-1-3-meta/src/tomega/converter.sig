(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)

signature CONVERTER = 
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)

  exception Error of string
  exception Error' of Tomega.Sub

  val convertFor : IntSyn.cid list -> Tomega.For
(*  val installFor : IntSyn.cid list -> unit *)
  val convertPrg : IntSyn.cid list -> Tomega.Prg 
  val installPrg : IntSyn.cid list -> IntSyn.cid * Tomega.lemma list   (* projections *)* Tomega.lemma list   (* selections *)

  val raisePrg : IntSyn.Dec IntSyn.Ctx * Tomega.Prg * Tomega.For -> Tomega.Prg

  val convertGoal : Tomega.Dec IntSyn.Ctx * IntSyn.Exp -> Tomega.Prg
end (* Signature CONVERTER *)       


