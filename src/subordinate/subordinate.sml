structure MemoTable =
  HashTable (type key' = int * int
	     val hash = (fn (n,m) => 7 * n + m)
             val eq = (op =));

structure Subordinate = 
  Subordinate (structure Global = Global
	       (*! structure IntSyn' = IntSyn !*)
	       structure Whnf = Whnf
	       structure Names = Names
	       structure Table = IntRedBlackTree
	       structure MemoTable = MemoTable
	       structure IntSet = IntSet);

structure Precedence = 
  Subordinate (structure Global = Global
	       (*! structure IntSyn' = IntSyn !*)
	       structure Whnf = Whnf
	       structure Names = Names
	       structure Table = IntRedBlackTree
	       structure MemoTable = MemoTable
	       structure IntSet = IntSet);     (* Wed Jul 23 14:15:40 2008 --cs *)



