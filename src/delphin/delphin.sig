(* Delphin Frontend *)
(* Author: Carsten Schuermann *)

signature  DELPHIN =
sig
  val version : string
  val loadFile : string * string -> unit
  val top : unit -> unit
end
