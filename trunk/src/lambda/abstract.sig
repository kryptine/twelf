(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature ABSTRACT =
sig
  structure IntSyn : INTSYN

  exception Error of string

  val piDepend  : (IntSyn.Dec * IntSyn.Depend) * IntSyn.Exp -> IntSyn.Exp
  val closedDec : IntSyn.Dec IntSyn.Ctx * (IntSyn.Dec * IntSyn.Sub) -> bool
  val closedSub : IntSyn.Dec IntSyn.Ctx * IntSyn.Sub -> bool
  val closedExp : IntSyn.Dec IntSyn.Ctx * (IntSyn.Exp * IntSyn.Sub) -> bool

  val abstractDecImp : IntSyn.Exp  -> (IntSyn.imp * IntSyn.Exp)
  val abstractDef : (IntSyn.Exp * IntSyn.Exp) -> 
                       (IntSyn.imp * (IntSyn.Exp * IntSyn.Exp))
end;  (* signature ABSTRACT *)
