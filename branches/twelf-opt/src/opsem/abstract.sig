(* Abstraction *)
(* Author: Brigitte Pientka *)

signature ABSTRACTTABLED =
sig
  structure IntSyn : INTSYN
  structure TableParam : TABLEPARAM
    
  exception Error of string

(*  datatype ResEqn =
    Trivial				  (* trivially done *)
  | Unify of IntSyn.dctx * IntSyn.Exp     (* call unify *)
             * IntSyn.Exp * ResEqn
*)
  val abstractEVarCtx : (IntSyn.dctx * IntSyn.Exp * IntSyn.Sub) ->  
                        (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.Exp * TableParam.ResEqn * IntSyn.Sub)


  val abstractAnswSub :  (IntSyn.dctx * IntSyn.Sub) -> IntSyn.dctx * IntSyn.Sub

  val raiseType : IntSyn.dctx * IntSyn.Exp -> IntSyn.Exp   

end;  (* signature ABSTRACTTABLED *)
