(* structure Tomega : TOMEGA =
   Tomega (structure IntSyn' = IntSyn
	   structure Whnf = Whnf
	   structure WorldSyn' = WorldSyn
	   structure Conv = Conv)
structure Normalize : NORMALIZE = 
  Normalize (structure IntSyn' = IntSyn
             structure Tomega' = Tomega
             structure Whnf = Whnf)
*)

structure TomegaPrint = TomegaPrint
  (structure IntSyn' = IntSyn
   structure Tomega' = Tomega
   structure Normalize = Normalize
   structure Formatter = Formatter
   structure Names = Names
   structure Print = Print)
     


