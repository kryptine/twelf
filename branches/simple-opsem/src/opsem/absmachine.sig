(* Abstract Machine (signature common to all abstract machines) *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)
(* Modified: Kevin Watkins *)

signature ABSMACHINE =
sig

  structure IntSyn  : INTSYN
  structure CompSyn : COMPSYN
  structure Compile : COMPILE
  sharing Compile.IntSyn = IntSyn
  sharing Compile.CompSyn = CompSyn

  val solve : CompSyn.Query * (IntSyn.Exp -> unit) -> unit
  val reset : unit -> unit

end;  (* signature ABSMACHINE *)
