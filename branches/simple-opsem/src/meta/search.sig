(* Basic search engine: Version 1.3*)
(* Author: Carsten Schuermann *)

signature MTPSEARCH = 
sig
  structure StateSyn : STATESYN

  exception Error of string

  val searchEx : int * StateSyn.FunSyn.IntSyn.dctx * StateSyn.FunSyn.For
(*      * (StateSyn.FunSyn.IntSyn.Exp * StateSyn.FunSyn.IntSyn.Sub) *)
      * (int * StateSyn.FunSyn.Pro -> unit) -> unit
end;  (* signature SEARCH *)
