structure Cover =
  Cover (structure Global = Global
	 structure IntSyn' = IntSyn
	 (*! structure IntSyn' = IntSyn !*)
	 (*! structure Tomega' = Tomega !*)
	 structure Whnf = Whnf
	 structure Abstract = Abstract
	 structure Unify = UnifyTrail
	 structure Constraints = Constraints
	 structure ModeSyn' = ModeSyn
	 structure Index = Index
         structure Subordinate = Subordinate
         structure WorldSyn = WorldSyn
         structure Names = Names
	 (*! structure Paths = Paths !*)
	 structure Print = Print
         structure TypeCheck = TypeCheck
	 (*! structure CSManager = CSManager !*)
         structure Timers = Timers);

structure Total =
  Total (structure Global = Global
	 structure Table = IntRedBlackTree
	 (*! structure IntSyn' = IntSyn !*)
	 structure Whnf = Whnf
	 structure Names = Names
         structure ModeSyn = ModeSyn
         structure ModeCheck = ModeCheck
	 structure Index = Index
         structure Subordinate = Subordinate
	 structure Order = Order
	 structure Reduces = Reduces
	 structure Cover = Cover
	 (*! structure Paths = Paths !*)
	 structure Origins = Origins
         structure Timers = Timers);

