structure CompSyn =
  CompSyn (structure Global = Global
           structure IntSyn' = IntSyn
	   structure Names = Names
           structure Table = IntRedBlackTree);

structure CPrint =
  CPrint (structure IntSyn' = IntSyn
	  structure CompSyn' = CompSyn
	  structure Print = Print
	  structure Formatter = Formatter
	  structure Names = Names);


structure SubTree =
 SubTree (structure IntSyn' = IntSyn
	  structure Whnf = Whnf
	  structure Unify = UnifyTrail
          structure CompSyn' = CompSyn
	  structure Print = Print
	  structure CPrint = CPrint
          structure Names = Names 
	  structure Formatter = Formatter
	  structure CSManager = CSManager
	  structure Table = IntRedBlackTree
	  structure RBSet = RBSet)

(* old compile structure Mon Jun 17 09:43:18 2002 -bp 
structure Compile =
  Compile (structure IntSyn' = IntSyn
	   structure CompSyn' = CompSyn
	   structure Whnf = Whnf
	   structure TypeCheck = TypeCheck
	   structure CPrint = CPrint
	   structure Print = Print
	   structure Names = Names);
*)
structure Compile =
  Compile (structure IntSyn' = IntSyn
	   structure CompSyn' = CompSyn
	   structure Whnf = Whnf
	   structure TypeCheck = TypeCheck
	   structure SubTree = SubTree 
	   structure CPrint = CPrint
	   structure Print = Print
	   structure Names = Names);

structure Assign =
  Assign (structure IntSyn' = IntSyn
	  structure Whnf = Whnf
	  structure Unify = UnifyTrail
	  structure Print = Print);

