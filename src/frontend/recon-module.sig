(* External syntax for module expressions *)
(* Author: Florian Rabe *)

signature MODEXTSYN =
sig
  structure ExtSyn : EXTSYN

  (* morphisms *)
  type morph
  val morstr : string list * string * Paths.region -> morph
 
  (* symbol (= constant or structure) instantiations *)
  type syminst
  val coninst : (string list * string * Paths.region) * (ExtSyn.term * Paths.region) -> syminst
  val strinst : (string list * string * Paths.region) * (morph       * Paths.region) -> syminst

  (* structure declarations *)
  type strdec
  val strdec : string * (string * Paths.region) * (syminst list) -> strdec

  (* begin and end of a module *)
  type modbegin
  val sigbegin : string -> modbegin
  type modend
  val sigend : modend
end;

signature RECON_MODULE =
sig
  include MODEXTSYN
  exception Error of string
  val morphToMorph : morph * Paths.location -> IntSyn.Morph
  val syminstToSymInst : syminst * Paths.location -> IntSyn.SymInst
  val strdecToStrDec : strdec * Paths.location -> IntSyn.StrDec
end