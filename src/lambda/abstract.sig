(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature ABSTRACT =
sig
  structure IntSyn : INTSYN
  structure Tomega : TOMEGA

  exception Error of string

  val piDepend  : (IntSyn.Dec * IntSyn.Depend) * IntSyn.Exp -> IntSyn.Exp
  val closedDec : IntSyn.Dec IntSyn.Ctx * (IntSyn.Dec * IntSyn.Sub) -> bool
  val closedSub : IntSyn.Dec IntSyn.Ctx * IntSyn.Sub -> bool
  val closedExp : IntSyn.Dec IntSyn.Ctx * (IntSyn.Exp * IntSyn.Sub) -> bool
  val closedCtx : IntSyn.Dec IntSyn.Ctx -> bool

  val abstractDecImp : IntSyn.Exp  -> (int * IntSyn.Exp)
  val abstractDef : (IntSyn.Exp * IntSyn.Exp)
                     -> (int * (IntSyn.Exp * IntSyn.Exp))
  val abstractCtxs : (IntSyn.Dec IntSyn.Ctx) list
                     -> (IntSyn.Dec IntSyn.Ctx) * (IntSyn.Dec IntSyn.Ctx) list
  val abstractTomegaSub : Tomega.Sub -> (Tomega.Dec IntSyn.Ctx * Tomega.Sub)

  val collectEVars : IntSyn.dctx * IntSyn.eclo * IntSyn.Exp list -> IntSyn.Exp list

  val raiseTerm    : IntSyn.dctx * IntSyn.Exp -> IntSyn.Exp
  val raiseType    : IntSyn.dctx * IntSyn.Exp -> IntSyn.Exp

end;  (* signature ABSTRACT *)