(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)

signature CONVERTER = 
sig
  structure IntSyn : INTSYN
  structure Tomega : TOMEGA

  exception Error of string
  exception Error' of Tomega.For

  val convertFor : IntSyn.cid list -> Tomega.For
  val convertPrg : IntSyn.cid list -> Tomega.Prg
end (* Signature CONVERTER *)       


