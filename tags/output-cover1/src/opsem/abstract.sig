(* Abstraction *)
(* Author: Brigitte Pientka *)

signature ABSTRACTTABLED =
sig
  structure IntSyn : INTSYN

  exception Error of string

  val strengthen : bool ref

  val abstractECloCtx : (IntSyn.dctx * IntSyn.Exp) -> 
                        (IntSyn.dctx * IntSyn.dctx * IntSyn.Exp * IntSyn.Exp)  


  val abstractEVarCtx : (IntSyn.dctx * (IntSyn.Exp * IntSyn.Exp) * IntSyn.Sub) ->  
                        (IntSyn.dctx * IntSyn.dctx * IntSyn.Exp * IntSyn.Exp * IntSyn.Sub)


  val abstractAnswSub : IntSyn.Sub -> IntSyn.dctx * IntSyn.Sub

  val abstractAnsw : IntSyn.dctx * IntSyn.Sub -> IntSyn.dctx * IntSyn.Sub 

  val raiseType : IntSyn.dctx * IntSyn.Exp -> IntSyn.Exp   


end;  (* signature ABSTRACTTABLED *)
