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

 structure AbstractTabled =
  AbstractTabled (structure IntSyn' = IntSyn
		  structure Whnf = Whnf
		  structure Subordinate = Subordinate
		  structure Conv = Conv
		  structure Unify = UnifyTrail
		  structure Print = Print);


structure MemoTable =
 MemoTable (structure IntSyn' = IntSyn
	    structure Conv = Conv
	    structure CompSyn' = CompSyn
	    structure Print = Print
	    structure AbstractTabled = AbstractTabled
	    structure Table = IntRedBlackTree
	    structure RBSet = RBSet)

(* structure TableIndex = 
  TableIndex (structure Global = Global
	      structure Queue = Queue
	      structure IntSyn' = IntSyn
	      structure Subordinate = Subordinate
	      structure CompSyn' = CompSyn
	      structure Conv = Conv
	      structure Unify = UnifyTrail 
	      structure AbstractTabled = AbstractTabled
	      structure Whnf = Whnf
	      structure Print = Print
	      structure CPrint = CPrint
	      structure TypeCheck = TypeCheck);
*)
structure Tabled = 
  Tabled (structure IntSyn' = IntSyn
	  structure CompSyn' = CompSyn
	  structure Unify = UnifyTrail 
	  structure TabledSyn = TabledSyn
	  structure Assign = Assign 
	  structure Index = Index
	  structure Queue = Queue
	  structure MemoTable = MemoTable    
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
