(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)
(* Modified: Yu Liao *)

signature TOMEGATYPECHECK = 
sig
  structure IntSyn : INTSYN
  structure Tomega : TOMEGA

  exception Error of string

  val isFor : Tomega.Dec IntSyn.Ctx * Tomega.For -> unit
  val check : Tomega.Prg * Tomega.For -> unit    
end (* Signature TOMEGATYPECHECK *)       

