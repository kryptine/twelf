structure Converter = Converter
  (structure Global = Global
   structure IntSyn' = IntSyn
   structure Tomega' = Tomega
   structure ModeSyn = ModeSyn
   structure Names = Names
   structure TypeCheck = TypeCheck
   structure Trail = Trail
   structure Unify = UnifyTrail
   structure Whnf = Whnf
   structure WorldSyn = WorldSyn
   structure Worldify = Worldify
   structure Print = Print
   structure Weaken = Weaken);


structure TomegaPrint = TomegaPrint
  (structure IntSyn' = IntSyn
   structure Tomega' = Tomega
   structure Normalize = Normalize
   structure Formatter = Formatter
   structure Names = Names
   structure Print = Print)


     


 