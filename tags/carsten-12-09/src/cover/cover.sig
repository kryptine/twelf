(* Coverage Checking *)
(* Author: Frank Pfenning *)

signature COVER =
sig

  structure IntSyn : INTSYN
  structure Tomega : TOMEGA
  structure ModeSyn : MODESYN
    sharing ModeSyn.IntSyn = IntSyn

  exception Error of string

  val checkOut : (IntSyn.dctx * IntSyn.eclo) -> unit

  val checkCovers : (IntSyn.cid * ModeSyn.ModeSpine) -> unit

  val coverageCheckCases : Tomega.Worlds * (IntSyn.dctx * IntSyn.Sub) list  * IntSyn.dctx -> unit

end;  (* signature COVER *)