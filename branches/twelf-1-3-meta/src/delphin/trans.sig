(* Translator from Delphin external syntax to Delphin internal syntax *)
(* Author: Richard Fontana, Carsten Schuermann *)
 
signature TRANS = 
sig
  structure DextSyn : DEXTSYN

  exception Error of string

(*  val transFor : DextSyn.Form -> Tomega.For
  val transPro : DextSyn.Prog -> Tomega.Prg *)
  val transDecs: DextSyn.Decs -> Tomega.Prg
 end
