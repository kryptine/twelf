(* Delphin Frontend *)
(* Author: Carsten Schuermann *)

signature  DELPHIN =
sig
  val version : string
  val loadFile : string * string -> unit
  val test : string * string -> (Tomega.Dec IntSyn.Ctx * Tomega.Prg)
    
  val top : unit -> unit

  val runSimpleTest : string -> (string list) -> string list -> unit
  val eval : Tomega.Prg -> Tomega.Prg
end
