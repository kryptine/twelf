(* Introduce: Version 1.4 *)
(* Author: Carsten Schuermann *)

signature INTRODUCE = 
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  structure State : STATE

  exception Error of string

  type operator

  val expand : State.State -> operator option
  val apply : operator -> State.State
  val menu : operator -> string
end; (* signature INTRODUCE *)


