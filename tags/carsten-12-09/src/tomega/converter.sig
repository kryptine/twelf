(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)

signature CONVERTER = 
sig
  structure IntSyn : INTSYN
  structure Tomega : TOMEGA

  exception Error of string
  exception Error' of Tomega.Sub

  val convertFor : IntSyn.cid list -> Tomega.For
(*  val installFor : IntSyn.cid list -> unit *)
  val convertPrg : IntSyn.cid list -> Tomega.Prg
  val installPrg : IntSyn.cid list -> IntSyn.cid
end (* Signature CONVERTER *)       


