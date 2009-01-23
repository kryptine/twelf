structure SymbolAscii = SymbolAscii ();

structure SymbolTeX = SymbolTeX ();

structure Print =
  Print ((*! structure IntSyn' = IntSyn !*)
	 structure Whnf = Whnf
	 structure Abstract = Abstract
	 structure Constraints = Constraints
	 structure Names = Names
	 structure Formatter' = Formatter
	 structure Symbol = SymbolAscii);

structure ClausePrint =
  ClausePrint ((*! structure IntSyn' = IntSyn !*)
	       structure Whnf = Whnf
	       structure Names = Names
	       structure Formatter' = Formatter
	       structure Print = Print
	       structure Symbol = SymbolAscii);

structure PrintTeX = Print
structure ClausePrintTeX = ClausePrint
structure PrintTwega = Print
structure PrintXML = Print
structure PrintOMDoc = Print

(* I'm commenting out the rest because adapting the printers is so tedious and should be done last anyway -fr
structure PrintTeX =
  Print ((*! structure IntSyn' = IntSyn !*)
	 structure Whnf = Whnf
	 structure Abstract = Abstract
	 structure Constraints = Constraints
	 structure Names = Names
	 structure Formatter' = Formatter
	 structure Symbol = SymbolTeX);

structure ClausePrintTeX =
  ClausePrint((*! structure IntSyn' = IntSyn !*)
	      structure Whnf = Whnf
	      structure Constraints = Constraints
	      structure Names = Names
	      structure Formatter' = Formatter
	      structure Print = PrintTeX
	      structure Symbol = SymbolTeX);

structure PrintTwega =
  PrintTwega ((*! structure IntSyn' = IntSyn !*)
	      structure Whnf = Whnf
	      structure Abstract = Abstract
	      structure Constraints = Constraints
	      structure Names = Names
	      structure Formatter' = Formatter);

structure PrintXML =
  PrintXML ((*! structure IntSyn' = IntSyn !*)
	      structure Whnf = Whnf
	      structure Abstract = Abstract
	      structure Constraints = Constraints
	      structure Names = Names
	      structure Formatter' = Formatter);

structure PrintOMDoc =
  PrintOMDoc ((*! structure IntSyn' = IntSyn !*)
	      structure Whnf = Whnf
	      structure Abstract = Abstract
	      structure Constraints = Constraints
	      structure Names = Names
	      structure Formatter' = Formatter);
*)