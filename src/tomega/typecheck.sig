(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)

signature TOTYPECHECK = 
sig
  structure Tomega : TOMEGA

  exception Error of string

  val isFor : Tomega.Dec Tomega.IntSyn.Ctx * Tomega.For -> unit (* -- Yu Liao *) (*Tomega.IntSyn.dctx * Tomega.For -> unit*)
  val check : Tomega.Prg * Tomega.For -> unit    

end (* Signature FUNTYPECHECK *)       

