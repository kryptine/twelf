structure TomegaPrint = TomegaPrint
  (structure IntSyn' = IntSyn
   structure Tomega' = Tomega
   structure Normalize = Normalize
   structure Formatter = Formatter
   structure Names = Names
   structure Print = Print)

structure TomegaTypeCheck = TomegaTypeCheck
  (structure Global = Global
   structure IntSyn' = IntSyn
   structure Abstract = Abstract
   structure Tomega' = Tomega
   structure TypeCheck = TypeCheck
   structure Normalize = Normalize
   structure Conv = Conv
   structure Whnf = Whnf
   structure Subordinate = Subordinate
   structure TomegaPrint = TomegaPrint
   structure Print = Print
   structure Weaken = Weaken);

structure TomegaUnify = TomegaUnify
  (structure Global = Global
   structure IntSyn' = IntSyn
   structure Abstract = Abstract
   structure Tomega' = Tomega
   structure TypeCheck = TypeCheck
   structure Normalize = Normalize
   structure Conv = Conv
   structure Whnf = Whnf
   structure Subordinate = Subordinate
   structure TomegaPrint = TomegaPrint
   structure Print = Print
   structure Weaken = Weaken);


structure Converter = Converter
  (structure Global = Global
   structure IntSyn' = IntSyn
   structure Abstract = Abstract
   structure Tomega' = Tomega
   structure ModeSyn = ModeSyn
   structure Names = Names
   structure TypeCheck = TypeCheck
   structure TomegaTypeCheck = TomegaTypeCheck
   structure Trail = Trail
   structure Unify = UnifyTrail
   structure Normalize = Normalize
   structure TomegaPrint = TomegaPrint
   structure Whnf = Whnf
   structure WorldSyn = WorldSyn
   structure Worldify = Worldify
   structure Subordinate = Subordinate
   structure Print = Print
   structure Weaken = Weaken);



structure Opsem = Opsem
  (structure Global = Global
   structure IntSyn' = IntSyn
   structure Abstract = Abstract
   structure Tomega' = Tomega
   structure TypeCheck = TypeCheck
   structure Normalize = Normalize
   structure Unify = UnifyTrail
   structure Conv = Conv
   structure Whnf = Whnf
   structure Subordinate = Subordinate
   structure TomegaPrint = TomegaPrint
   structure Print = Print
   structure Weaken = Weaken);

structure TomegaCoverage = TomegaCoverage
  (structure Global = Global
   structure IntSyn' = IntSyn
   structure Tomega' = Tomega
   structure Cover = Cover);

