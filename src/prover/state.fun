(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

functor State 
  (structure IntSyn' : INTSYN
   structure Tomega' : TOMEGA
     sharing Tomega'.IntSyn = IntSyn'
   structure Normalize : NORMALIZE
     sharing Normalize.Tomega = Tomega') : STATE =
struct
  structure IntSyn = IntSyn'
  structure Tomega = Tomega'
  structure T = Tomega'
  structure I = IntSyn'

  datatype State
    = State of (T.Dec I.Ctx * T.For) * T.Worlds

  exception Error of string

  local 
       (* init F = S

       Invariant:
       S = (. |> F) is the initial state
    *)
    fun init (F, W) = State ((I.Null, F), W)

    (* close S = B

       Invariant:
       If   S = (Psi |> F) state 
       and  F == F'
       then B = true 
       else B = false
    *)
    fun close (State ((_, F), _)) = 
         T.convFor ((Normalize.normalizeFor (F, T.id), T.id), (T.True, T.id))

      
  in
    val close = close
    val init = init
  end
end