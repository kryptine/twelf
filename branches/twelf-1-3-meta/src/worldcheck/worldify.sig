(* Worldify *) 
(* Author: Carsten Schuermann *)


signature WORLDIFY = 
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)

  exception Error of string 

  val worldify :  IntSyn.cid -> IntSyn.ConDec list

end; (* signature WORLDIFY *)
