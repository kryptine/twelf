(* Syntax for simple solver *)
(* Author: Kevin Watkins *)

functor SimpSyn (structure IntSyn : INTSYN) : SIMPSYN =
struct

  structure IntSyn = IntSyn

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

  fun conDecName (ConDec (name, _, _)) = name
    | conDecName (ConDef (name, _, _)) = name
    | conDecName (AbbrevDef (name, _, _)) = name
    | conDecName (SkoDec (name, _)) = name

  fun conDecImp (ConDec (_, i, _)) = i
    | conDecImp (ConDef (_, i, _)) = i
    | conDecImp (AbbrevDef (_, i, _)) = i
    | conDecImp (SkoDec (_, i)) = i

  fun conDecStatus (ConDec (_, _, status)) = status
    | conDecStatus _ = Normal

  local
    val maxCid = Global.maxCid
    val sgnArray = Array.array (maxCid+1, ConDec("", 0, Normal))
      : ConDec Array.array
  in
    (* Invariants *)
    (* Constant declarations are all well-typed *)
    (* Constant declarations are stored in beta-normal form *)
    (* All definitions are strict in all their arguments *)
    (* If Const(cid) is valid, then sgnArray(cid) = ConDec _ *)
    (* If Def(cid) is valid, then sgnArray(cid) = ConDef _ *)

    (* Invariant: cid <= maxCid *)
    fun sgnInstall (cid, conDec) = Array.update (sgnArray, cid, conDec)
    fun sgnLookup (cid) = Array.sub (sgnArray, cid)
    fun sgnReset () = Array.modify (fn _ => ConDec("", 0, Normal)) sgnArray

  end

  fun constDef (d) =
      (case sgnLookup (d)
	 of ConDef(_, _, U) => U
	  | AbbrevDef (_, _, U) => U)

  fun constImp (c) =
      (case sgnLookup(c)
	 of ConDec (_,i,_) => i
          | ConDef (_,i,_) => i
          | AbbrevDef (_,i,_) => i
	  | SkoDec (_,i) => i)

  fun constStatus (c) =
      (case sgnLookup (c)
	 of ConDec (_, _, status) => status
          | _ => Normal)

  datatype Goal =
    Atom   of Exp
  | Impl   of ResGoal * IntSyn.cid * Goal
  | All    of Goal

  and ResGoal =
    Eq     of Exp
  | And    of ResGoal * Goal
  | Exists of int * ResGoal  (* EVars are pre-lowered -- the int
                                is a count of the number of abstractions
                                in the type of the variable *)

  and Query =
    QueryGoal of Goal
  | QueryVar  of Exp * Query

  val id = Shift(0)
  val shift = Shift(1)

  fun bvarSub (1, Dot(Ft, s)) = Ft
    | bvarSub (n, Dot(Ft, s)) = bvarSub (n-1, s)
    | bvarSub (n, Shift(k))  = Idx (n+k)

  and frontSub (Idx (n), s) = bvarSub (n, s)
    | frontSub (Exp (U), s) = Exp (EClo (U, s))
    | frontSub (Undef, s) = Undef

  fun comp (Shift (0), s) = s
    (* next line is an optimization *)
    (* roughly 15% on standard suite for Twelf 1.1 *)
    (* Sat Feb 14 10:15:16 1998 -fp *)
    | comp (s, Shift (0)) = s
    | comp (Shift (n), Dot (Ft, s)) = comp (Shift (n-1), s)
    | comp (Shift (n), Shift (m)) = Shift (n+m)
    | comp (Dot (Ft, s), s') = Dot (frontSub (Ft, s'), comp (s, s'))

  fun dot1 (s as Shift (0)) = s
    | dot1 s = Dot (Idx(1), comp(s, shift))

  (* defined(ss) = b

     Invariant:
     If ss is a strsub, b = true iff s is defined everywhere
  *)
  fun defined (Dot (Undef, _)) = false
    | defined (Dot (_, s)) = defined(s)
    | defined _ = true

  fun newEVar () = EVar(ref NONE, ref nil)

  fun rawExp (t, Root(H, S)) = "Root(" ^ rawHead(t, H) ^ ",\n" ^ t
                             ^ rawSpine(t, S) ^ ")"
    | rawExp (t, Redex(U, S)) = "Redex(" ^ rawExp(t^"      ", U) ^ ",\n" ^ t
                              ^ rawSpine(t, S) ^ ")"
    | rawExp (t, Lam(U)) = "Lam(" ^ rawExp(t^"    ", U) ^ ")"
    | rawExp (t, EVar(ref(NONE), _)) = "EVar(NONE)"
    | rawExp (t, EVar(ref(SOME(U)), _)) = "EVar(SOME(" ^ rawExp(t^"          ", U) ^ "))"
    | rawExp (t, EClo(U, s)) = "EClo(" ^ rawExp(t^"     ", U) ^ ",\n" ^ t
                             ^ rawSub(t, s) ^ ")"

  and rawHead (t, BVar(n)) = "BVar(" ^ Int.toString n ^ ")"
    | rawHead (t, Const(c)) = "Const(" ^ IntSyn.conDecName(IntSyn.sgnLookup(c)) ^ ")"
    | rawHead (t, Skonst(c)) = "Skonst(" ^ IntSyn.conDecName(IntSyn.sgnLookup(c)) ^ ")"
    | rawHead (t, Def(d)) = "Def(" ^ IntSyn.conDecName(IntSyn.sgnLookup(d)) ^ ")"
    | rawHead (t, NSDef(d)) = "NSDef(" ^ IntSyn.conDecName(IntSyn.sgnLookup(d)) ^ ")"

  and rawSpine (t, Nil) = "Nil"
    | rawSpine (t, App(U, S)) = "App(" ^ rawExp(t^"    ", U) ^ ",\n" ^ t
                              ^ rawSpine(t, S) ^ ")"
    | rawSpine (t, SClo(S, s)) = "SClo(" ^ rawSpine(t^"     ", S) ^ ",\n" ^ t
                               ^ rawSub(t, s) ^ ")"

  and rawSub (t, Shift(k)) = "Shift(" ^ Int.toString(k) ^ ")"
    | rawSub (t, Dot(Ft, s)) = "Dot(" ^ rawFront(t^"    ", Ft) ^ ",\n" ^ t
                             ^ rawSub(t, s) ^ ")"

  and rawFront (t, Idx(n)) = "Idx(" ^ Int.toString(n) ^ ")"
    | rawFront (t, Exp(U)) = "Exp(" ^ rawExp(t^"    ", U) ^ ")"
    | rawFront (t, Undef) = "Undef"

end
