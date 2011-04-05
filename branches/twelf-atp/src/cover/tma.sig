(* Truthful monadic abstractions *)
(* Taus Brock-Nannestad, Carsten Schuermann *)

signature TMA = 
  sig
    val resolve : (IntSyn.Exp * int) list * ModeSyn.ModeSpine -> unit
  end 