(* Translator from Delphin external syntax to Delphin internal syntax *)
(* Author: Richard Fontana, Carsten Schuermann *)
 (* 
signature TRANS = 
sig
  structure DextSyn : DEXTSYN
  structure TpRecon : TP_RECON

  exception Error of string

  val transFor : DextSyn.Form -> Tomega.For
  val transPro : DextSyn.Prog -> Tomega.Prg
  val transDecs: DextSyn.Decs -> Tomega.Prg
 end
*)