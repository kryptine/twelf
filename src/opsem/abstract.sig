(* Abstraction *)
(* Author: Brigitte Pientka *)

signature ABSTRACTTABLED =
sig
  structure IntSyn : INTSYN

  exception Error of string

  val strengthen : bool ref

  datatype ResEqn =
    Trivial				  (* trivially done *)
  | Unify of IntSyn.dctx * IntSyn.Exp     (* call unify *)
             * IntSyn.Exp * ResEqn

  val abstractEVarCtx : (IntSyn.dctx * IntSyn.Exp * IntSyn.Sub) ->  
                        (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.Exp * ResEqn * IntSyn.Sub)

(*  val abstractEVarCtx : (IntSyn.dctx * IntSyn.Exp * IntSyn.Sub) ->  
                        (IntSyn.dctx * IntSyn.dctx * IntSyn.Exp * ResEqn * IntSyn.Sub)
*)

(*  val abstractAnswSub : IntSyn.Sub -> IntSyn.dctx * IntSyn.Sub * ResEqn*)
(*  val abstractAnswSub : (IntSyn.dctx * IntSyn.Sub ) -> IntSyn.dctx * IntSyn.Sub * ResEqn*)
  val abstractAnswSub : (IntSyn.dctx * IntSyn.Sub ) -> IntSyn.dctx * IntSyn.dctx * IntSyn.Sub * ResEqn
(*  val abstractAnsw : IntSyn.dctx * IntSyn.Sub -> IntSyn.dctx * IntSyn.Sub * ResEqn*)

  val raiseType : IntSyn.dctx * IntSyn.Exp -> IntSyn.Exp   
(*  val collectEVars : IntSyn.dctx * IntSyn.eclo * IntSyn.Exp list -> IntSyn.Exp list *)

end;  (* signature ABSTRACTTABLED *)
