(* Syntax for simple solver *)
(* Author: Kevin Watkins *)

signature SIMPSYN =
sig

  structure IntSyn : INTSYN

  datatype Exp =
    Root   of Head * Spine
  | Redex  of Exp * Spine
  | Lam    of Exp
  | EVar   of Exp option ref * (Cnstr ref) list ref
  | EClo   of Exp * Sub

  and Head =
    BVar   of int
  | Const  of IntSyn.cid
  | Skonst of IntSyn.cid
  | Def    of IntSyn.cid
  | NSDef  of IntSyn.cid

  and Spine =
    Nil
  | App    of Exp * Spine
  | SClo   of Spine * Sub

  and Sub =
    Shift  of int
  | Dot    of Front * Sub

  and Front =
    Idx    of int
  | Exp    of Exp
  | Undef

  and Cnstr =
    Solved
  | Eqn    of Exp * Exp

  and Status = Normal

  and ConDec =
    ConDec of string * int * Status
  | ConDef of string * int * Exp
  | AbbrevDef of string * int * Exp
  | SkoDec of string * int

  type eclo = Exp * Sub
  type cnstr = Cnstr ref

  val conDecName   : ConDec -> string
  val conDecImp    : ConDec -> int
  val conDecStatus : ConDec -> Status

  val sgnInstall   : IntSyn.cid * ConDec -> unit
  val sgnLookup    : IntSyn.cid -> ConDec
  val sgnReset     : unit -> unit

  val constDef    : IntSyn.cid -> Exp
  val constImp    : IntSyn.cid -> int
  val constStatus : IntSyn.cid -> Status

  datatype Goal =
    Atom   of Exp
  | Impl   of ResGoal * IntSyn.cid * Goal
  | All    of Goal

  and ResGoal =
    True
  | Eq         of Exp
  | And        of ResGoal * Goal
  | AndMeta    of ResGoal * Goal
  | Exists     of int * ResGoal  (* EVars are pre-lowered -- the int
                                    is a count of the number of abstractions
                                    in the type of the variable *)
  | ExistsMeta of int * ResGoal

  and Query =
    QueryGoal of Goal
  | QueryVar  of Exp * Query

  val id        : Sub			(* id                         *)
  val shift     : Sub			(* ^                          *)

  val bvarSub   : int * Sub -> Front    (* k[s]                       *)
  val frontSub  : Front * Sub -> Front	(* H[s]                       *)

  val comp      : Sub * Sub -> Sub	(* s o s'                     *)
  val dot1      : Sub -> Sub		(* 1 . (s o ^)                *)

  val defined   : Sub -> bool

  val newEVar   : unit -> Exp   	(* creates X:G|-V, []         *) 

  val rawExp : string * Exp -> string
  val rawHead : string * Head -> string
  val rawSpine : string * Spine -> string
  val rawSub : string * Sub -> string
  val rawFront : string * Front -> string
  val rawEClo : string * (Exp * Sub) -> string

end
