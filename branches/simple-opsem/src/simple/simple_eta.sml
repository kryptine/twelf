structure SimpSyn =
  SimpSyn (structure IntSyn = IntSyn)

structure SimpWhnf =
  SimpWhnfEta (structure SimpSyn = SimpSyn)

structure SimpUnify =
  SimpUnifyEta (structure SimpSyn = SimpSyn
             structure SimpWhnf = SimpWhnf
             structure Trail = Trail)

structure SimpComp =
  SimpCompEta (structure Global = Global
            structure IntSyn = IntSyn
            structure Whnf = Whnf
            structure Abstract = Abstract
            structure Print = Print
            structure CompSyn = CompSyn
            structure PTCompile = PTCompile
            structure FullComp = FullComp
            structure SimpSyn = SimpSyn)

structure SimpMachine =
  SimpMachine (structure IntSyn = IntSyn
               structure CompSyn = CompSyn
               structure CPrint = CPrint
               structure ElabSolution = ElabSolution
               structure SimpSyn = SimpSyn
	       structure SimpWhnf = SimpWhnf
               structure SimpUnify = SimpUnify
               structure SimpComp = SimpComp
               structure Index = Index
               structure IndexSkolem = IndexSkolem
               structure CSManager = CSManager)
