(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Kevin Watkins *)

signature ABSTRACT =
sig
  structure IntSyn : INTSYN

  exception Error of string

  val piDepend  : (IntSyn.Dec * IntSyn.Depend) * IntSyn.Exp -> IntSyn.Exp
  val closedDec : IntSyn.Dec IntSyn.Ctx * (IntSyn.Dec * IntSyn.Sub) -> bool
  val closedSub : IntSyn.Dec IntSyn.Ctx * IntSyn.Sub -> bool
  val closedExp : IntSyn.Dec IntSyn.Ctx * (IntSyn.Exp * IntSyn.Sub) -> bool
  val closedCtx : IntSyn.Dec IntSyn.Ctx -> bool

  val abstractDecImp : IntSyn.Exp  -> (int * IntSyn.Exp)
  val abstractDef : (IntSyn.Exp * IntSyn.Exp) -> 
                       (int * (IntSyn.Exp * IntSyn.Exp))

  val collectEVars : IntSyn.dctx * IntSyn.eclo * IntSyn.Exp list -> IntSyn.Exp list

  val abstractQuery : IntSyn.Exp -> (IntSyn.Dec IntSyn.Ctx * IntSyn.eclo)

end;  (* signature ABSTRACT *)
