(* Simple unifier *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)
(* Modified: Kevin Watkins *)

signature SIMPUNIFY =
sig

  structure SimpSyn : SIMPSYN

  (* trailing of variable instantiation *)

  val reset  : unit -> unit
  val mark   : unit -> unit
  val unwind : unit -> unit

  (* unification *)

  exception Unify of string

  val unify : SimpSyn.eclo * SimpSyn.eclo -> unit	(* raises Unify *)
  val unifyW : SimpSyn.eclo * SimpSyn.eclo -> unit (* raises Unify *)
  (* unifiable (Us,Us') will instantiate EVars as an effect *)
  val unifiable : SimpSyn.eclo * SimpSyn.eclo -> bool

end
