(* Indexing for table *)
(* Author: Brigitte Pientka *)

functor TableIndex (structure Global : GLOBAL
		    structure Queue : QUEUE
		    structure IntSyn': INTSYN
		    structure CompSyn': COMPSYN
		      sharing CompSyn'.IntSyn = IntSyn'
		    structure Subordinate : SUBORDINATE
		      sharing Subordinate.IntSyn = IntSyn'		      
		    structure Conv: CONV
		      sharing Conv.IntSyn = IntSyn'
		    structure Unify : UNIFY
		      sharing Unify.IntSyn = IntSyn'
		    structure AbstractTabled : ABSTRACTTABLED
		      sharing AbstractTabled.IntSyn = IntSyn'
		    structure Whnf : WHNF
		      sharing Whnf.IntSyn = IntSyn'
		    structure Print : PRINT 
 		      sharing Print.IntSyn = IntSyn'
		    structure CPrint : CPRINT 
                      sharing CPrint.IntSyn = IntSyn'
                      sharing CPrint.CompSyn = CompSyn'
		    structure TypeCheck : TYPECHECK
		      sharing TypeCheck.IntSyn = IntSyn')
  : TABLEINDEX =
struct
  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'
  structure AbstractTabled = AbstractTabled

  (* TABLE 

   table entry : D, G  |- u 

   Answer substitution: 

                 Dk, G  |- sk : D, G

   Answer : 
                 Dk, G |- u[sk]
   *)
 
  (* solution: (Dk, sk) 

   * lookup  : pointer to the i-th element in solution list
   *)

  type answer = {solutions : ((IntSyn.dctx * IntSyn.Sub * AbstractTabled.ResEqn) * CompSyn.pskeleton) list,
		 lookup: int} ref

  (* entry = (((i, G, D, U), A)) where i is the access counter     
   *)
  type entry = (((int ref * IntSyn.dctx * IntSyn.dctx * IntSyn.Exp * AbstractTabled.ResEqn) * answer))

  type entries = entry list 

  type index = entry list

  datatype answState = new | repeated

  datatype callCheckResult = NewEntry of answer | RepeatedEntry of answer

  datatype Strategy = Variant | Subsumption
  (* took out all subsumption code *)

  exception Error of string

  val added = ref false;

  (* ---------------------------------------------------------------------- *)
  (* global search parameters *)

  val strategy  = ref Variant (* Subsumption *) (* Variant *)

  (* term abstraction after term depth is greater than 5 *) 
  val termDepth = ref NONE : int option ref;
  val ctxDepth = ref NONE : int option ref;
  val ctxLength = ref NONE : int option ref;

(*   val termDepth = ref (!globalTermDepth); *)
(*   val ctxDepth = ref (!globalCtxDepth);   *)
(*   val ctxLength = ref (!globalCtxLength); *)

  (* apply strengthening during abstraction *)
  val strengthen = AbstractTabled.strengthen ;

  fun makeEmptyAnswer () = ref {solutions = [], lookup = 0} 

  val answList : (answer list) ref = ref []

  (* ---------------------------------------------------------------------- *)

  local
    structure I = IntSyn
    structure C = CompSyn
    structure A = AbstractTabled

    (* Global Table *)

    val table : index ref = ref []

    (* concat(Gdp, G) = G'' 
     *
     * if Gdp = ym...y1 
     *    G   = xn...x1
     * then 
     *    Gdp, G = G'' 
     *    ym...y1, xn...x1
     *
     *)
    fun concat (I.Null, G') = G'
      | concat (I.Decl(G, D), G') = I.Decl(concat(G,G'), D)

    fun shift (IntSyn.Null, s) = s
      | shift (IntSyn.Decl(G, D), s) = I.dot1 (shift(G, s))


   fun reverse (I.Null, G') = G'
     | reverse (I.Decl(G, D), G') = 
         reverse (G, I.Decl(G', D))

    (* ---------------------------------------------------------------------- *)

    (* printTable () = () *)

    fun printResEqn (G, D, A.Trivial) = print "Trivial\n"
      | printResEqn (G, D, A.Unify(G', p1, N, eqn)) = 
        (print (Print.expToString (I.Null, A.raiseType(D, A.raiseType(concat(G', G), p1))) ^ " = ");
	 print (Print.expToString (I.Null, A.raiseType(D, A.raiseType(concat(G', G), N))) ^ "\n"); 
	 printResEqn (G, D, eqn))

    fun printResEqnSub (G, D', A.Trivial, s) = print "Trivial\n"
      | printResEqnSub (G, D', A.Unify(G', p1, N, eqn), s) = 
        (print (Print.expToString (I.Null, A.raiseType(D', I.EClo(A.raiseType(concat(G', G), p1), shift(G', s)))) ^ " = ");
	 print (Print.expToString (I.Null, A.raiseType(D', I.EClo(A.raiseType(concat(G', G), N),shift(G', s)))) ^ "\n"); 
	 printResEqnSub (G, D', eqn, s))

    fun printTable () = 
      let 
        fun proofTerms (G, U,  []) = print ""
	  | proofTerms (G, U,  (((D', s', eqn'), _)::S)) = 
          ((print (Print.expToString (I.Null, A.raiseType(D', I.EClo(A.raiseType(G, U), s'))))
(*           (print (Print.expToString (I.Null, A.raiseType(D',
			I.EClo(A.raiseType(G, U), s')))) *)
	    handle _ => print "EXCEPTION\n" );	    
	 print ("\t UnifyEq ");
	   printResEqn (G, D', eqn'); 
	   (* do not print pskeletons *)
	   print ", \n\t";
	   proofTerms (G, U, S))

	fun printT [] = ()
	  | printT (((k, G, D, U, eqn), answRef)::T) = 
	  let 
	    val {solutions =  S, lookup = i} = !answRef
	  in 
	    case S
	      of [] => (printT T ; 
			print (Print.expToString (I.Null, 
						  A.raiseType(concat(G, D), U))); (* Pi D. Pi G. U *)
			print ("\nUnifyEq ");
			printResEqn (G, D, eqn);
			print ", NONE\n")
	    | (a::answ) => (printT T; 
			    print (Print.expToString (I.Null, 
							A.raiseType(concat(G, D), U)));
			    print ("\nUnifyEq ");
			    printResEqn (G, D, eqn);		    
			    print (", [\n\t");
			    proofTerms (G, U, (rev S));
			    print (" ] -- lookup : " ^ Int.toString i ^ "\n\n")) 
	  end 
      in
	print ("Table: \n");
	printT (!table);
	print ("End Table \n");
	print ("Number of table entries   : " ^ Int.toString(length(!table)) ^ "\n")
      end 			       	    


    (* printTableEntries () = () *)

    fun printTableEntries () = 
      let 
	fun printT [] = ()
	  | printT (((k, G, D, U, eqn), answRef)::T) = 
	  let
	    val {solutions =  S, lookup = i} = !answRef
	  in 
	    (printT T ; 
	     print (Print.expToString (I.Null, A.raiseType(concat(G, D), U)) ^ 
		    "\n Access Counter : " ^ (Int.toString (!k)) ^ " \n");
	     print ("UnifyEqn "); printResEqn (G, D, eqn))
	  end
      in
	print ("TableEntries: \n");
	printT (!table);
	print ("End TableEntries \n");
	print ("Number of table entries   : " ^ Int.toString(length(!table)) ^ "\n")
      end 			       	    

    
    (* ---------------------------------------------------------------------- *)

    (* Term Abstraction *)

    fun lengthSpine (I.Nil) = 0
      | lengthSpine (I.SClo(S, s')) = 1 + lengthSpine(S)


    fun exceedsTermDepth (i) = 
      case (!termDepth) of 
	NONE => false
      | SOME(n) => (i > n)

    fun exceedsCtxDepth (i) = 
      case (!ctxDepth) of 
	NONE => false
      | SOME(n) => (print ("\n exceedsCtxDepth " ^Int.toString i ^ " > " ^ Int.toString n ^ " ? ") ;(i > n))

    fun exceedsCtxLength (i) = 
      case (!ctxLength) of 
	NONE => false
      | SOME(n) => (i > n)
      
    fun max (x,y) = 
      if x > y then x
      else y

    fun oroption (NONE, NONE, NONE) = false
      | oroption (SOME(k), _ , _) = true
      | oroption (_ , SOME(n), _) = true
      | oroption (_ , _, SOME(n)) = true

    fun abstractionSet () = 
      oroption(!termDepth, !ctxDepth, !ctxLength)

    (* countDepth U = 
         ctr = (ctrTerm, ctrDecl, ctrLength)
         ctrTerm : max term depth
         ctrDecl : max type depth in decl
         ctrLength : length of decl
       
    *)
	      
    fun exceeds (U) = countDecl(0,0, U)

    and countDecl (ctrType, ctrLength, I.Pi((D, _), V)) = 
         let 
	   val ctrType' = countDec(0, D)
(*	   val _ = print ("\n ctrType' = " ^ Int.toString ctrType')  *)
	 in 	   
	   if ctrType' > ctrType then
	     countDecl (ctrType', ctrLength + 1, V)
	   else 
	     countDecl (ctrType, ctrLength + 1, V)
	 end 
      | countDecl(ctrType, ctrLength, U) = 
	 let
	   val ctrTerm = count (0, U)
(*	   val _ = print ("\n 1 ctrTerm = " ^ Int.toString ctrTerm)
	   val _ = print ("\n 1 ctxLength = " ^ Int.toString ctrLength)
	   val _ = print ("\n 1 ctxDepth = " ^ Int.toString ctrType)
*)
	 in 
	   exceedsCtxDepth(ctrType) orelse
	   exceedsCtxLength(ctrLength) orelse
	   exceedsTermDepth(count(0,U))
	 end 

    and countDec (ctr, I.Dec(_, U)) = count(ctr, U)
      | countDec (ctr, I.BDec(_,s)) = 0
    
    and count (ctr, (U as I.Uni (L))) = ctr
      | count (ctr, I.Pi((D, _), V)) = 
          let
	    val ctrTerm = count (ctr, V)
	    val ctrType = countDec (ctr, D)
(*	   val _ = print ("\n ctrTerm = " ^ Int.toString ctrTerm)
	   val _ = print ("\n ctrType = " ^ Int.toString ctrType)
*)

	  in 
          max(ctrType,ctrTerm) (* to revise ?*)
	  end 
      | count (ctr, I.Root (F, S)) =
         let
	   val ctrDepth = countSpine (1, S)
(*	   val _ = print ("\n spineDepth = " ^ Int.toString ctrDepth)
	   val _ = print ("\n RootF = " ^ Int.toString(ctrDepth + ctr))
*)
	 in 
	   (ctrDepth + 1 + ctr)
(*	   (ctrLength + ctr) *)
	 end 
      | count (ctr, I.Redex (U, S)) =
         let 
	   val ctrDepth = count (0, U)
	   val ctrDepth' =  countSpine (ctrDepth, S)
(*	   val _ = print ("\n SpindeDepth = " ^ Int.toString ctrDepth)
	   val _ = print ("\n Redex = " ^ Int.toString(max(ctrDepth',ctrDepth) + ctr))*)

	 in
	   (max(ctrDepth',ctrDepth) + ctr)
	 end 
      | count (ctr, I.Lam (D, U)) =
	 count (ctr+1, U)
      | count (ctr, (X as I.EVar _)) = 
	 (* shouldn't happen *)
	 ctr
      | count (ctr, I.EClo(E, s)) = 
	 count (ctr, E)
      | count (ctr, (F as I.FgnExp (cs, ops))) = 
	 (* shouldn't happen *)
	 (ctr)
	 
 (* count max depth of term in S + length of S *) 	  
    and countSpine (ctrDepth, I.Nil)  = ctrDepth
      | countSpine (ctr, I.SClo (S, s')) = 
         (* ? *)
         countSpine (ctr, S)
      | countSpine (ctrDepth, I.App (U, S)) =
	 let
	   val ctrDepth' = count (0, U)
	 in 
	   countSpine (max(ctrDepth', ctrDepth), S)
      end 
 


   (* ---------------------------------------------------------------------- *)
   (* reinstSub (G, D, s) = s' 
    *
    * If D', G |- s : D, G
    * then  G |- s' : D, G
    *)

   fun reinstSub (G, I.Null, s) = s
      | reinstSub (G, I.Decl(D, I.Dec(_,A)), s) = 
      let
	val X = I.newEVar (I.Null, A)
      in
	I.Dot(I.Exp(X), reinstSub (G, D, s))

      end 


   (* ---------------------------------------------------------------------- *)
   (* variant (U,s) (U',s')) = bool   *)
      
    fun variant (Us, Us') = Conv.conv (Us, Us') 

    


    (* subsumes ((G, D, U), (G', D', U')) = bool
     * 
     * if
     *    D, G   |- U 
     *    D', G' |- U'
     * then  
     *      G' |- s' : D', G'
     *    return true if D, G |- U is an instance of G' |- U'[s'] 
     *    otherwise false
     *
     *)
    fun subsumes ((G, D, U), (G', D', U')) = 
      let 
	val Upi = A.raiseType (G, U)
	val Upi' = A.raiseType (G', U')
	val s' = reinstSub (G', D', I.id)
      in 
	CSManager.trail (fn () => 
			 Unify.unifiable (D, (Upi', s'), (Upi, I.id)))
      end 

    (* too restrictive if we require order of both eqn must be the same ? 
     Sun Sep  8 20:37:48 2002 -bp *) 
    (* s = s' = I.id *)
    fun equalCtx (I.Null, s, I.Null, s') = true
      | equalCtx (I.Decl(G, D), s, I.Decl(G', D'), s') = 
        Conv.convDec((D, s), (D', s')) andalso (equalCtx (G, I.dot1 s, G', I.dot1 s'))

    (* in general, we need to carry around and build up a substitution *)
    fun equalEqn (A.Trivial, A.Trivial) = true
      | equalEqn (A.Unify(G, X, N, eqn), A.Unify(G', X', N', eqn')) = 
        equalCtx (G, I.id, G', I.id) andalso Conv.conv ((X, I.id), (X', I.id)) 
	andalso Conv.conv ((N, I.id), (N', I.id)) andalso equalEqn(eqn, eqn')

    fun equalSub (I.Shift k, I.Shift k') = (k = k')
      | equalSub (I.Dot(F, S), I.Dot(F', S')) = 
        equalFront (F, F') andalso equalSub (S, S')
      | equalSub (I.Dot(F,S), I.Shift k) = false
      | equalSub (I.Shift k, I.Dot(F,S)) = false

    and equalFront (I.Idx n, I.Idx n') = (n = n')
      | equalFront (I.Exp U, I.Exp V) = Conv.conv ((U, I.id), (V, I.id))
      | equalFront (I.Undef, I.Undef) = true

    fun equalSub1 (I.Dot(ms, s), I.Dot(ms', s')) = 
          equalSub (s, s')


    fun equalCtx (I.Null, I.Null) = true
      | equalCtx (I.Decl(Dk, I.Dec(_, A)), I.Decl(D1, I.Dec(_, A1))) = 
        Conv.conv ((A, I.id), (A1, I.id)) andalso equalCtx(Dk, D1)

    (* ---------------------------------------------------------------------- *)
    (* Call check and insert *)

    (* callCheck (G, D, U) = callState
     
       check whether D, G |- U is in the table
 
     returns NONE, 
        if D, G |- U is not already in the table
	  Sideeffect: add D, G |- U to table
     
     returns SOME(A) 
        if D, G |- U is in table and 
	  A is an entry in the table together with its answer list

    Variant: 
    if it succeeds there is exactly one table entry which is a variant to U
    Subsumption:
    if it succeeds it will return the most general table entry of which U is
    an instance of (by invariant now, the most general table entry will be found first,
    any entry found later, will be an instance of this entry)
    *)

    fun callCheckVariant (G, D, U, eqn) = 
      let
	val Upi = A.raiseType(concat(G, D), U)
	fun lookup ((G, D, U, eqn), []) = 
	  (let
	     val answRef = ref ({solutions = [],lookup = 0})
	   in 
	     table := ((ref 1, G, D, U, eqn), answRef)::(!table); 
	     answList := (answRef::(!answList)) ; 
	     (if (!Global.chatter) >= 5 then 
		(print ("\n \n Added " );
		 print (Print.expToString (I.Null, Upi) ^ "\n to Table \n"))
	      else 
		());
		added := true;
		(* if termdepth(U) > n then force the tabled engine to suspend
		 * and treat it like it is already in the table, but no answ available *)
		if abstractionSet() then 
		  ((* print ("\n term " ^ Print.expToString (I.Null, Upi) ^ 
		    " exceeds depth or length ? \n"); *)
		   
		   if exceeds (A.raiseType(G, U)) then 
		     ((if (!Global.chatter) >= 5 then 
			 print ("\n term " ^ Print.expToString (I.Null, Upi) ^ 
				" exceeds depth or length \n")
		       else 
			 ());
			 RepeatedEntry (answRef)) (* ? Thu Sep 12 14:06:57 2002 -bp *)
		   else 
		     NewEntry (answRef))
		else 
		  NewEntry (answRef)
	   end)
	  | lookup ((G, D, U, eqn), ((H as ((k, G', D', U', eqn'), answRef))::T)) =
	    if variant ((Upi, I.id), (A.raiseType(concat(G',D'), U'), I.id)) andalso equalEqn(eqn, eqn') then
	      (k := !k+1;
	       (if (!Global.chatter) >= 5 then
		  print ("call " ^ Print.expToString (I.Null, Upi) ^ " found in table \n ")
		else 
		  ());
		  RepeatedEntry (answRef))
	    else  
	      lookup ((G, D, U, eqn), T)
      in 
	lookup ((G, D, U, eqn), (!table))
      end



    (* ---------------------------------------------------------------------- *)
    (* answer check and insert 
      
      if     G |- U[s]
          D, G |- U
	     G |- s : D, G 
      
      answerCheck (G, D, (U,s)) = repeated
         if s already occurs in answer list for U
      answerCheck (G, D, (U,s)) = new
         if s did not occur in answer list for U
         Sideeffect: update answer list for U
       
        Dk, G |- sk : D, G
	Dk, G |- U[sk]

        sk is the abstraction of s and Dk contains all "free" vars
      
     *) 
    fun answCheckVariant (G, D, U, eqn, s, answRef, O) =  
      let 
	val {solutions = S, lookup = i} = !answRef

	fun member ((Dk, sk, eqnk), []) = false
	  | member ((Dk, sk, eqnk), (((D1, s1, eqn1),_)::S)) = 
	    if equalSub (sk,s1) andalso equalCtx (Dk, D1) andalso equalEqn (eqnk, eqn1) then   
	      true
	    else 
	      member ((Dk, sk, eqnk), S)
	
	val (Dk, sk, eqnk) = A.abstractAnswSub (G, s)
(*	val _ = print ("Length of Dk = " ^ Int.toString (I.ctxLength(Dk)) ^ "\n")
	val _ = print ("Length of G = " ^ Int.toString (I.ctxLength(G)) ^ "\n") *)
      in 	
	if member ((Dk, sk, eqnk), S) then  
	  repeated
	else 
	  (answRef := {solutions = (((Dk, sk, eqnk), O)::S), 
		       lookup = i}; 
	   (if (!Global.chatter) >= 5 then 
	      (print ("\n solution added for " ); 
	       print (Print.expToString(I.Null, A.raiseType(D, A.raiseType(G, U))) ^ "\n");
	       print ("solution is : " ^ Print.expToString (I.Null, I.EClo(A.raiseType(G, U), s)) ^ "\n");

	       print ("closed sol.: " ^ Print.expToString(I.Null, A.raiseType(Dk, I.EClo(A.raiseType(G, U), sk))) ^ "\n");
	       print ("             "); printResEqn(G, Dk, eqnk); print "\n")
	    else 
	      ());
	      new)
      end 


   (* ---------------------------------------------------------------------- *)
   (* TOP LEVEL *)

    fun reset () = (table := [])
    fun tableSize () = (List.length(!table))

    fun solutions {solutions = S, lookup = i} = S
    fun lookup {solutions = S, lookup = i} = i

(*
    fun noAnswers [] = true
      | noAnswers ((H as ((G', D', U', eqn'), answRef))::L') = 
      let
	val answ = !answRef
      in 
	case (List.take (solutions(answ), lookup(answ))) 
	  of [] => noAnswers L'
	| L  => false
      end
*)
    fun noAnswers answ =     
    (case solutions(answ) 
       of [] => true
     | L  => false)


    fun callCheck (G, D, U, eqn) = 
          case (!strategy) of 
	    Variant => callCheckVariant (G, D, U, eqn)
	  | Subsumption => raise Error "Subsumption is missing currently\n"

    fun answCheck (G, D, U, eqn, s, answRef, O) = 
      case (!strategy) of
	Variant => answCheckVariant (G, D, U, eqn, s, answRef, O)
      | Subsumption => raise Error "Subsumption is missing currently\n"
	      

    (* needs to take into account previous size of table *)
    fun updateTable () = 
      let
	fun update [] Flag = Flag
	  | update (answRef::AList) Flag = 
	  let
	    val {solutions = S, lookup = i} = !answRef
		val l = length(S) 
	      in 
		if (l = i) then 
		  (* no new solutions were added in the previous stage *) 	      
		  (answRef := {solutions = S, lookup = l};
		  update AList Flag)
		else 
		  (* new solutions were added *)
		  (answRef := {solutions = S, lookup = l};
		  update AList true)
	      end 
	    val Flag = update (!answList) false
	    val r = Flag orelse (!added) 
	  in  
	    added := false; 
	    r
	  end 
(*
    fun updateTable () = 
          let 
	    fun update [] Flag = Flag
	      | update (((k, G, D, U, eqn), answRef )::T) Flag =
	      let 
		val {solutions = S, lookup = i} = !answRef
		val l = length(S) 
	      in 
		if (l = i) then 
		  (* no new solutions were added in the previous stage *) 	      
		  (answRef := {solutions = S, lookup = List.length(S)};
		  update T Flag)
		else 
		  (* new solutions were added *)
		  (answRef := {solutions = S, lookup = List.length(S)};
		  update T true)
	      end 
	    val Flag = update (!table) false
	    val r = Flag (* orelse (!added) *)
	  in  
(*	    added := false; *)
(*	    table := rev(T); *)
            (* in each stage incrementally increase termDepth *)
(*	    termDepth := (!termDepth +1); *)
	    r
	  end 
*)
  in

(*  val termDepth = termDepth
    val ctxDepth = ctxDepth
    val ctxLength = ctxLength
*)
    val table = table
    val solutions = (fn answRef => solutions (!answRef))
    val lookup = (fn answRef => lookup (!answRef))
    val noAnswers = (fn answRef => noAnswers (!answRef))

    val reset = reset

    val printTable = printTable
    val printTableEntries = printTableEntries

    val callCheck = callCheck
    val answerCheck = answCheck

    val updateTable = updateTable

    val tableSize = tableSize
  end (* local *)

end;  (* functor TableIndex *)

