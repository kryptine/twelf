(* Compiler (signature common to all compilers) *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)
(* Modified: Frank Pfenning *)
(* Modified: Kevin Watkins *)

signature COMPILE =
sig

  structure IntSyn: INTSYN
  structure CompSyn: COMPSYN

  val installResGoal : IntSyn.cid * CompSyn.ResGoal -> unit
  val install : bool -> IntSyn.cid -> unit
  val reset : unit -> unit

end; (* signature COMPILE *)
