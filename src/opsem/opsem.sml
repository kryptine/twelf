structure CompSyn =
  CompSyn (structure IntSyn' = IntSyn);

structure PTCompile =
  PTCompile (structure IntSyn' = IntSyn
             structure CompSyn' = CompSyn
             structure Whnf = Whnf
             structure Abstract = Abstract);

structure FullComp =
  FullComp (structure Global = Global
            structure IntSyn' = IntSyn
	    structure CompSyn' = CompSyn
            structure PTCompile = PTCompile);

structure CPrint =
  CPrint (structure IntSyn' = IntSyn
	  structure CompSyn' = CompSyn
          structure FullComp = FullComp
	  structure Print = Print
	  structure Formatter = Formatter
	  structure Names = Names);

structure ElabSolution =
  ElabSolution (structure IntSyn = IntSyn
                structure CompSyn = CompSyn
                structure FullComp = FullComp
                structure Whnf = Whnf
                structure Unify = UnifyTrail
                structure Print = Print
                structure CPrint = CPrint);

structure FullMachine = 
  FullMachine (structure IntSyn' = IntSyn
               structure CompSyn' = CompSyn
               structure Whnf = Whnf
               structure Unify = UnifyTrail
               structure FullComp = FullComp
	       structure Index = Index
               structure IndexSkolem = IndexSkolem
               structure CPrint = CPrint
               structure CSManager = CSManager);

structure Trace =
  Trace (structure IntSyn' = IntSyn
	 structure Names = Names
	 structure Whnf = Whnf
	 structure Abstract = Abstract
	 structure Print = Print);

structure TMachine =
  TMachine (structure IntSyn' = IntSyn
	    structure CompSyn' = CompSyn
	    structure Unify = UnifyTrail
            structure FullComp = FullComp
	    structure Index = Index
	    structure CPrint = CPrint
            structure Names = Names
	    structure Trace = Trace
            structure CSManager = CSManager);
