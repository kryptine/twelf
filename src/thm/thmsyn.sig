(* Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

signature THMSYN =
sig
  structure IntSyn : INTSYN
  structure ModeSyn : MODESYN
    sharing ModeSyn.IntSyn = IntSyn
  structure Paths : PATHS

  exception Error of string

  type Param = string option

  datatype Order =
    Varg of string list
  | Lex of Order list
  | Simul of Order list

  (* -bp *)
  datatype Predicate = Less | Leq | Eq

  datatype RedOrder = 
      RedOrder of Predicate * Order * Order
  
  datatype Callpats =
    Callpats of (IntSyn.cid * Param list) list 

  (* Termination declaration *)
  datatype TDecl = 
    TDecl of Order * Callpats

  (* -bp *)
  (* Reduction declaration *)
  datatype RDecl = 
    RDecl of (RedOrder * Callpats)

  (* Theorem declaration  *)
  datatype ThDecl =
    ThDecl of (IntSyn.Dec IntSyn.Ctx * IntSyn.Dec IntSyn.Ctx) list
              * IntSyn.Dec IntSyn.Ctx * ModeSyn.Mode IntSyn.Ctx * int

  (* Proof declaration *)
  datatype PDecl = 
    PDecl of int * TDecl

  (* World declaration *)
  datatype WDecl = 
    WDecl of (IntSyn.Dec IntSyn.Ctx * 
	      IntSyn.Dec IntSyn.Ctx) list * Callpats


  val theoremDecToConDec : ((string * ThDecl) * Paths.region) -> 
                           (IntSyn.Dec IntSyn.Ctx * IntSyn.Dec IntSyn.Ctx) list * IntSyn.ConDec
  val theoremDecToModeSpine : ((string * ThDecl) * Paths.region) -> ModeSyn.ModeSpine
end;  (* signature THMSYN *)
