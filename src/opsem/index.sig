(* Indexing *)
(* Author: Brigitte Pientka *)

signature TABLEINDEX =
sig

  structure IntSyn : INTSYN
  structure CompSyn : COMPSYN
  structure AbstractTabled : ABSTRACTTABLED
    
  type answer = {solutions : ((IntSyn.dctx  * IntSyn.Sub * AbstractTabled.ResEqn) * CompSyn.pskeleton) list,
		 lookup: int} ref

  datatype Strategy = Variant | Subsumption
  exception Error of string

  val strategy  : Strategy ref 

  val termDepth  : int option ref
  val ctxDepth   : int option ref
  val ctxLength  : int option ref 
  val strengthen : bool ref

  datatype answState = new | repeated

  datatype callCheckResult = 
    NewEntry of answer 
  | RepeatedEntry of answer

  (* table: G, Gdprog |- goal , 
            (answ list (ith stage) , answ list (1 to i-1 th stage))
   *) 
  val table : ((int ref * IntSyn.dctx * IntSyn.dctx * IntSyn.Exp * AbstractTabled.ResEqn) * answer) list ref 

  val noAnswers : answer -> bool

  val tableSize : unit -> int
  (* call check/insert *)

  (* callCheck (G, D, U, eqn)
   *
   * if D, G |- U & eqn     in table  then RepeatedEntry (entries)
   * if D, G |- U & eqn not in table  then NewEntry (ptrAnswer)
   * SIDE EFFECT: D, G |- U added to table
   *)

  val callCheck : IntSyn.dctx * IntSyn.dctx * IntSyn.Exp * AbstractTabled.ResEqn -> callCheckResult
  

  (* answer check/insert *)
  (* answerCheck (G, D, (U,s))
   * 
   * Assumption: D, G |- U is in table
   *             and A represents the corresponding solutions
   * 
   * G |- s : D, G
   * Dk, G |- sk : D, G
   *
   * If  (Dk, sk) in A then repeated
   *  else new
   *)

  val answerCheck : IntSyn.dctx * IntSyn.dctx * IntSyn.Exp * AbstractTabled.ResEqn *IntSyn.Sub * answer * CompSyn.pskeleton -> answState

  (* reset table *)
  val reset: unit -> unit
  
  val printTable : unit -> unit
  val printTableEntries : unit -> unit

  (* updateTable 
   *
   * SIDE EFFECT: 
   *   for each table entry: 
   *       advance lookup pointer
   *
   * if Table did not change during last stage 
   *    then updateTable () =  false
   * else updateTable () = true
   *)
   
  val updateTable : unit -> bool

  val solutions : answer -> ((IntSyn.dctx * IntSyn.Sub * AbstractTabled.ResEqn) * CompSyn.pskeleton) list
  val lookup : answer -> int

end;  (* signature TABLEINDEX *)

