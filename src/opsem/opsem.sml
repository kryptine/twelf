structure AbsMachine = 
  AbsMachine (structure IntSyn' = IntSyn
              structure CompSyn' = CompSyn
              structure Unify = UnifyTrail
	      structure Assign = Assign 
	      structure Index = Index
              structure CPrint = CPrint
              structure Print = Print
              structure Names = Names
              structure CSManager = CSManager); 

structure PtRecon = 
  PtRecon (structure IntSyn' = IntSyn
	  structure CompSyn' = CompSyn
	  structure Unify = UnifyTrail
	  structure Assign = Assign 
	  structure Index = Index
	  structure CPrint = CPrint
	  structure Names = Names
	  structure CSManager = CSManager); 

structure TableParam =
 TableParam (structure IntSyn' = IntSyn
	    structure CompSyn' = CompSyn)

structure AbstractTabled =
  AbstractTabled (structure IntSyn' = IntSyn
		  structure Whnf = Whnf
		  structure Subordinate = Subordinate
		  structure TableParam = TableParam
		  structure Conv = Conv
		  structure Unify = UnifyTrail
		  structure Print = Print);

structure MemoTable =
 MemoTable (structure IntSyn' = IntSyn
	    structure Conv = Conv
	    structure CompSyn' = CompSyn
	    structure Print = Print
	    structure TableParam = TableParam
	    structure AbstractTabled = AbstractTabled
	    structure Table = IntRedBlackTree
	    structure RBSet = RBSet)


structure MemoTableInst =
 MemoTableInst (structure IntSyn' = IntSyn
	    structure Conv = Conv
	    structure CompSyn' = CompSyn
	    structure Print = Print
	    structure TableParam = TableParam
	    structure AbstractTabled = AbstractTabled
	    structure Table = IntRedBlackTree
	    structure RBSet = RBSet)


structure SwMemoTable =
 SwMemoTable (structure TableParam = TableParam
	      structure MemoTable = MemoTable
	      structure MemoTableInst = MemoTableInst)

structure Tabled = 
  Tabled (structure IntSyn' = IntSyn
	  structure CompSyn' = CompSyn
	  structure Unify = UnifyTrail 
	  structure TabledSyn = TabledSyn
	  structure Assign = Assign 
	  structure Index = Index
	  structure Queue = Queue
	  structure TableParam = TableParam
(*	  structure MemoTable = MemoTable    *)
	  structure MemoTable = SwMemoTable    
	  structure AbstractTabled = AbstractTabled
	  structure CPrint = CPrint
	  structure Print = Print
	  structure Names = Names
	  structure CSManager = CSManager
	  structure Subordinate = Subordinate); 

structure Trace =
  Trace (structure IntSyn' = IntSyn
	 structure Names = Names
	 structure Whnf = Whnf
	 structure Abstract = Abstract
	 structure Print = Print);


structure AbsMachineSbt = 
  AbsMachineSbt (structure IntSyn' = IntSyn
              structure CompSyn' = CompSyn
	      structure SubTree = SubTree
              structure Unify = UnifyTrail
	      structure Assign = Assign 
	      structure Index = Index
              structure CPrint = CPrint
              structure Print = Print
              structure Names = Names
              structure CSManager = CSManager); 

structure TMachine =
  TMachine (structure IntSyn' = IntSyn
	    structure CompSyn' = CompSyn
	    structure Unify = UnifyTrail
	    structure Index = Index
	    structure Assign = Assign 
	    structure CPrint = CPrint
            structure Names = Names
	    structure Trace = Trace
              structure CSManager = CSManager);

structure SwMachine =
  SwMachine (structure Trace = Trace
	     structure AbsMachine = AbsMachine
             structure TMachine = TMachine);
