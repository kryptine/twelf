(* Front End Interface *)
(* Author: Frank Pfenning *)
(* Modified: Carsten Schuermann, Jeff Polakow *)

functor Twelf
  (structure Global : GLOBAL
   structure Timers : TIMERS
   structure IntSyn' : INTSYN
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn'
   structure Print : PRINT
     sharing Print.IntSyn = IntSyn'

   structure Names : NAMES
     sharing Names.IntSyn = IntSyn'
   structure Paths' : PATHS
   structure Origins : ORIGINS
     sharing Origins.Paths = Paths'
   structure Lexer : LEXER
     sharing Lexer.Paths = Paths'
   structure Parsing : PARSING
     sharing Parsing.Lexer = Lexer
   structure Parser : PARSER
     sharing Parser.Names = Names
   structure TypeCheck : TYPECHECK
   structure Strict : STRICT
     sharing Strict.IntSyn = IntSyn'
   structure Abstract : ABSTRACT
     sharing Abstract.IntSyn = IntSyn'
   structure TpReconQ : TP_RECON
     sharing TpReconQ.IntSyn = IntSyn'
     sharing TpReconQ.Paths = Paths'
     sharing type TpReconQ.term = Parser.ExtSynQ.term
     sharing type TpReconQ.query = Parser.ExtSynQ.query
     (* sharing type TpReconQ.Paths.occConDec = Origins.Paths.occConDec *)
   structure TpRecon : TP_RECON
     sharing TpRecon.IntSyn = IntSyn'
     sharing TpRecon.Paths = Paths'
     sharing type TpRecon.condec = Parser.ExtSyn.condec
     sharing type TpRecon.term = Parser.ExtSyn.term
     (* sharing type TpRecon.Paths.occConDec = Origins.Paths.occConDec *)

   structure ModeSyn : MODESYN
     sharing ModeSyn.IntSyn = IntSyn'
   structure ModeCheck : MODECHECK
     sharing ModeCheck.ModeSyn = ModeSyn
     sharing ModeCheck.Paths = Paths'
   structure ModeRecon : MODE_RECON
     sharing ModeRecon.ModeSyn = ModeSyn
     sharing ModeRecon.Paths = Paths'
     sharing type ModeRecon.modedec = Parser.ExtModes.modedec
   structure ModePrint : MODEPRINT
     sharing ModePrint.ModeSyn = ModeSyn
   structure ModeDec : MODEDEC
     sharing ModeDec.ModeSyn = ModeSyn
     sharing ModeDec.Paths = Paths'

   structure Terminate : TERMINATE
     sharing Terminate.IntSyn = IntSyn'

   structure Index : INDEX
     sharing Index.IntSyn = IntSyn'
   structure Subordinate : SUBORDINATE
     sharing Subordinate.IntSyn = IntSyn'
   structure CompSyn' : COMPSYN
     sharing CompSyn'.IntSyn = IntSyn'
   structure Compile : COMPILE
     sharing Compile.IntSyn = IntSyn'
     sharing Compile.CompSyn = CompSyn'
   structure Trail : TRAIL
     sharing Trail.IntSyn = IntSyn'
   structure AbsMachine : ABSMACHINE
     sharing AbsMachine.IntSyn = IntSyn'
     sharing AbsMachine.CompSyn = CompSyn'
   structure Solve : SOLVE
     sharing Solve.IntSyn = IntSyn'
     sharing type Solve.ExtSynQ.term = Parser.ExtSynQ.term
     sharing type Solve.ExtSynQ.query = Parser.ExtSynQ.query
     sharing Solve.Paths = Paths'
   structure ThmSyn : THMSYN
     sharing ThmSyn.Paths = Paths'
   structure Thm : THM
     sharing Thm.ThmSyn = ThmSyn
     sharing Thm.Paths = Paths'
   structure ThmRecon : THM_RECON
     sharing ThmRecon.ThmSyn = ThmSyn
     sharing ThmRecon.Paths = Paths'
     sharing ThmRecon.ThmSyn.ModeSyn = ModeSyn
     sharing type ThmRecon.tdecl = Parser.ThmExtSyn.tdecl
     sharing type ThmRecon.theorem = Parser.ThmExtSyn.theorem
     sharing type ThmRecon.theoremdec = Parser.ThmExtSyn.theoremdec 
     sharing type ThmRecon.prove = Parser.ThmExtSyn.prove
   structure ThmPrint : THMPRINT
     sharing ThmPrint.ThmSyn = ThmSyn

   structure MetaGlobal : METAGLOBAL
   structure Prover : PROVER
     sharing Prover.MetaSyn.IntSyn = IntSyn'
   structure ClausePrint : CLAUSEPRINT
     sharing ClausePrint.IntSyn = IntSyn')
 :> TWELF =
struct

  local
    structure IntSyn = IntSyn'
    structure S = Parser.Stream

    fun fileOpenMsg (fileName) =
	(case !Global.chatter
	   of 0 => ()
	    | 1 => print ("[Loading file " ^ fileName ^ " ...")
	    | _ => print ("[Opening file " ^ fileName ^ "]\n"))

    fun fileCloseMsg (fileName) =
	(case !Global.chatter
	   of 0 => ()
	    | 1 => print ("]\n")
	    | _ => print ("[Closing file " ^ fileName ^ "]\n"))

    (* result of a computation *)
    datatype 'a Result = Value of 'a | Exception of exn

    (* val withOpenIn : string -> (TextIO.instream -> 'a) -> 'a *)
    (* withOpenIn fileName (fn instream => body) = x
       opens fileName for input to obtain instream and evaluates body.
       The file is closed during normal and abnormal exit of body.
    *)
    fun withOpenIn (fileName) (scope) =
	let
	  val instream = TextIO.openIn fileName
	  val _ = fileOpenMsg (fileName)
	  val result = Value (scope instream) handle exn => Exception (exn)
	  val _ = fileCloseMsg (fileName)
	  val _ = TextIO.closeIn instream
	in
	  case result
	    of Value (x) => x
	     | Exception (exn) => raise exn
	end

    (* evarInstToString Xs = msg
       formats instantiated EVars as a substitution.
       Abbreviate as empty string if chatter level is < 3.
    *)
    fun evarInstToString (Xs) =
	if !Global.chatter >= 3
	  then Print.evarInstToString (Xs)
	else ""

    (* expToString (G, U) = msg
       formats expression as a string.
       Abbreviate as empty string if chatter level is < 3.
    *)
    fun expToString GU =
	if !Global.chatter >= 3
	  then Print.expToString GU
	else ""

    (* status ::= OK | ABORT  is the return status of various operations *)
    datatype Status = OK | ABORT

    fun abort (msg) = (print (msg); ABORT)
    fun abortFileMsg (fileName, msg) = abort (fileName ^ ":" ^ msg ^ "\n")

    fun abortIO (fileName, {cause = OS.SysErr (msg, _), function = f, name = n}) =
	(print ("IO Error on file " ^ fileName ^ ":\n" ^ msg ^ "\n");
	 ABORT)
      | abortIO (fileName, {function = f, ...}) =
	(print ("IO Error on file " ^ fileName ^ " from function "
		       ^ f ^ "\n");
	 ABORT)

    (* val handleExceptions : string -> ('a -> Status) -> 'a -> Status *)
    (* handleExceptions filename f x = f x
       where standard exceptions are handled and an appropriate error message is
       issued.  Unrecognized exceptions are re-raised.
    *)
    fun handleExceptions fileName (f:'a -> Status) (x:'a) =
	(f x
	 handle TpRecon.Error (msg) => abortFileMsg (fileName, msg)
	      | TpReconQ.Error (msg) => abortFileMsg (fileName, msg)
	      | ModeRecon.Error (msg) => abortFileMsg (fileName, msg)
	      | ThmRecon.Error (msg) => abortFileMsg (fileName, msg)
	      | TypeCheck.Error (msg) => abort ("Double-checking types fails: " ^ msg ^ "\n"
						^ "This indicates a bug in Twelf.\n")
	      | Strict.Error (msg) => abortFileMsg (fileName, msg)
	      | Abstract.Error (msg) => abortFileMsg (fileName, msg)
	      | Terminate.Error (msg) => abort (msg ^ "\n") (* Terminate includes filename *)
	      | Thm.Error (msg) => abortFileMsg (fileName, msg)
	      | ModeSyn.Error (msg) => abortFileMsg (fileName, msg)
	      | ModeCheck.Error (msg) => abortFileMsg (fileName, msg)
	      | ModeDec.Error (msg) => abortFileMsg (fileName, msg)
	      | Parsing.Error (msg) => abortFileMsg (fileName, msg)
	      | Lexer.Error (msg) => abortFileMsg (fileName, msg)
	      | IntSyn.Error (msg) => abort ("Signature error: " ^ msg ^ "\n")
	      | Names.Error (msg) => abortFileMsg (fileName, msg)
	      | IO.Io (ioError) => abortIO (fileName, ioError)
	      | Solve.AbortQuery (msg) => abortFileMsg (fileName, msg)
	      | ThmSyn.Error (msg) => abortFileMsg (fileName, msg)
	      | Prover.Error (msg) => abort ("Prover error: " ^ msg ^ "\n")
	      | exn => (abort ("Unrecognized exception\n"); raise exn))

    (* installConDec (conDec, ocOpt)
       installs the constant declaration conDec which originates at ocOpt
       in various global tables, including the global signature.
    *)
    fun installConDec (conDec, fileNameocOpt) =
	let
	    val cid = IntSyn.sgnAdd conDec
	    val _ = Names.installName (IntSyn.conDecName conDec, cid)
	    val _ = Origins.installOrigin (cid, fileNameocOpt)
	    val _ = Index.install cid
	    val _ = (Timers.time Timers.compiling Compile.install) cid
	    val _ = (Timers.time Timers.subordinate Subordinate.install) cid
	in 
	  cid
	end

    (* install1 (decl) = ()
       Installs one declaration
       Effects: global state
                may raise standard exceptions
    *)
    fun install1 (fileName, Parser.ConDec(condec, r)) =
        (* Constant declarations c : V, c : V = U plus variations *)
	let
	  val (optConDec, ocOpt) = TpRecon.condecToConDec (condec, r)
	  fun icd (SOME(conDec)) =
	      let
		  val _ = (Timers.time Timers.modes ModeCheck.checkD) (conDec, ocOpt)
		  (* allocate new cid after checking modes! *)
		  val cid = installConDec (conDec, (fileName, ocOpt))
	      in
		()
	      end
	    | icd (NONE) = (* anonymous definition for type-checking *)
	      ()
	in
	  icd optConDec
	end

      (* Solve declarations %solve c : A *)
      | install1 (fileName, Parser.Solve((name,tm), r)) =
	let
	  val conDec = Solve.solve ((name, tm), r)
	  val _ = Strict.check (conDec, NONE)
	  (* allocate cid after strictness has been checked! *)
	  val cid = installConDec (conDec, (fileName, NONE))
	  val _ = if !Global.chatter >= 3
		    then print ((Timers.time Timers.printing Print.conDecToString)
				       conDec ^ "\n")
		  else if !Global.chatter >= 2
			 then print (" OK\n")
		       else ();
	in
	  ()
	end

      (* %query <expected> <try> A or %query <expected> <try> X : A *)
      | install1 (fileName, Parser.Query(expected,try,query, r)) =
        (* Solve.query might raise Solve.AbortQuery (msg) *)
	(Solve.query (expected, try, query)
	 handle Solve.AbortQuery (msg)
	        => raise Solve.AbortQuery (Paths.wrap (r, msg)))

      (* Fixity declaration for operator precedence parsing *)
      | install1 (fileName, Parser.FixDec ((name,r),fixity)) =
	(Names.installFixity (name, fixity)
	 handle Names.Error (msg) => raise Names.Error (Paths.wrap (r,msg)))

      (* Name preference declaration for printing *)
      | install1 (fileName, Parser.NamePref ((name,r), namePref)) =
	(Names.installNamePref (name, namePref)
	 handle Names.Error (msg) => raise Names.Error (Paths.wrap (r,msg)))

      (* Mode declaration *)
      | install1 (fileName, Parser.ModeDec mterm) =
	let 
	  val (mdec, r) = ModeRecon.modeToMode mterm
	  val _ =  ModeSyn.installMode mdec
	    handle ModeSyn.Error (msg) => raise ModeSyn.Error (Paths.wrap (r, msg))
	  val _ = if !Global.chatter >= 3 
		    then print ("%mode " ^ (ModePrint.modeToString mdec) ^ ".\n")
		  else ()
	in
	  ()
	end

      (* Termination declaration *)
      | install1 (fileName, Parser.TerminatesDec lterm) =
	let
	  val (T, rrs) = ThmRecon.tdeclTotDecl lterm 
	  val La = Thm.install (T, rrs)
	  val _ = map (Timers.time Timers.terminate Terminate.checkFam) La
	  val _ = if !Global.chatter >= 3 
		    then print ("%terminates " ^ (ThmPrint.tDeclToString T) ^ ".\n")
		  else ()
	in
	  ()
	end

      (* Theorem declaration *)
      | install1 (fileName, Parser.TheoremDec tdec) =
	let 
	  val (Tdec, r) = ThmRecon.theoremDecToTheoremDec tdec
	  val E as IntSyn.ConDec (name, k, V, L) = ThmSyn.theoremDecToConDec (Tdec, r)
	  val cid = installConDec (E, (fileName, NONE))
	  val MS = ThmSyn.theoremDecToModeSpine (Tdec, r)
	  val _ = ModeSyn.installMode (cid, MS)
	  val _ = if !Global.chatter >= 3
		    then print ("%theorem " ^ name ^ " : " ^ 
				       ClausePrint.theoremToString cid ^ ".\n")
		  else ()
	in
	  ()
	end

      (* Prove declaration *)
      | install1 (fileName, Parser.ProveDec lterm) =
	let 
	  val (ThmSyn.PDecl (depth, T), rrs) = ThmRecon.proveToProve lterm 
	  val La = Thm.install (T, rrs)  (* La is the list of type constants *)
	  val _ = if !Global.chatter >= 3 
		    then print ("%prove " ^ (Int.toString depth) ^ " " ^
				       (ThmPrint.tDeclToString T) ^ ".\n")
		  else ()
	  val _ = Prover.init (depth, La)
	  val _ = if !Global.chatter >= 3 
		    then map (fn a => print ("%mode " ^ 
					     (ModePrint.modeToString (a, valOf (ModeSyn.modeLookup a)))
					     ^ ".\n")) La   (* mode must be declared!*)
		  else [()]

	  val _ = Prover.auto () (* times itself *)
	in
	  Prover.install (fn E => installConDec (E, (fileName, NONE)))
	end


    (* loadFile (fileName) = status
       reads and processes declarations from fileName in order, issuing
       error messages and finally returning the status (either OK or
       ABORT).
    *)
    fun loadFile (fileName) = 
	handleExceptions fileName (withOpenIn fileName)
	 (fn instream =>
	  let
	    fun install s = install' ((Timers.time Timers.parsing S.expose) s)
	    and install' (S.Empty) = OK
	      | install' (S.Cons(decl, s')) =
	        (install1 (fileName, decl); install s')
	  in
	    install (Parser.parseStream instream)
	  end)

    (* Interactive Query Top Level *)

    fun sLoop () = if Solve.qLoop () then OK else ABORT

    fun topLoop () = case (handleExceptions "stdIn" sLoop) () (* "stdIn" as fake fileName *)
		       of ABORT => topLoop ()
			| OK => ()

    (* top () = () starts interactive query loop *)
    fun top () = topLoop ()

    (* reset () = () clears all global tables, including the signature *)
    fun reset () = (IntSyn.sgnReset (); Names.reset (); ModeSyn.reset ();
		    Index.reset (); Subordinate.reset (); Terminate.reset ();
		    CompSyn.sProgReset () (* necessary? -fp *)
		    )

    fun readDecl () =
        handleExceptions "stdIn"
	(fn () =>
	 let fun install s = install' ((Timers.time Timers.parsing S.expose) s)
	     and install' (S.Empty) = ABORT
	       | install' (S.Cons (decl, s')) =
	         (install1 ("stdIn", decl); OK)
	 in
	   install (Parser.parseStream TextIO.stdIn)
	 end) ()

    (* decl (id) = () prints declaration of constant id *)
    fun decl (id) = decl' (id, Names.nameLookup id)
    and decl' (id, NONE) = (print (id ^ " has not been declared\n"); ABORT)
      | decl' (id, SOME(cid)) =
        let
	  val conDec = IntSyn.sgnLookup (cid)
	  (* val fixity = Names.getFixity (cid) *)
	  (* can't get name preference right now *)
	  (* val mode = ModeSyn.modeLookup (cid) *)
	  (* can't get termination declaration *)
	in
	  print (Print.conDecToString conDec ^ "\n");
	  OK
	end

    (* config = ["fileName1",...,"fileName<n>"] *)
    (* Files will be read in the order given! *)
    structure Config =
    struct
      (* A configuration (pwdir, sources) consists of an absolute directory
         pwdir and a list of source file names which are interpreted
         relative to pwdir.  pwdir will be the current working directory
         when a configuration is loaded, which may not be same as the
         directory in which the configuration file is located.

	 This representation allows shorter file names in chatter and
	 error messages.
      *)
      type config = string * string list

      fun read (configFile) =
	  withOpenIn (configFile)
	  (fn instream =>
	   let
	     fun parseLine (sources, line) =
		 if Substring.isEmpty line
		   then List.rev (sources) (* end of file *)
		 else parseLine' (sources, Substring.dropl Char.isSpace line)
	     and parseLine' (sources, line') =
		 if Substring.isEmpty line' orelse Substring.sub (line', 0) = #"%"
		   then parseStream sources	(* ignore empty or comment line *)
		 else parseStream (Substring.string (Substring.takel (not o Char.isSpace) line')
				:: sources)
	     and parseStream (sources) =
	           parseLine (sources, Substring.all (TextIO.inputLine instream))

	     val {dir=configDir, file=_} = OS.Path.splitDirFile configFile
	     (* mkRel interpretes a path p in the config file relative to
	        configDir, the directory of the config file.
             *)
	     fun mkRel (p) = if OS.Path.isAbsolute p
			       then p
			     else OS.Path.concat (configDir, p)
	     fun relSources (sources) = List.map mkRel sources
	     val pwdir = OS.FileSys.getDir ()
	   in
	     (pwdir, relSources (parseStream nil))
	   end)
	  (*
	  handle IO.Io (ioError) => (abortIO (configFile, ioError); raise IO.io (ioError))
	  *)

      fun loadAbort (filename, OK) = loadFile (filename)
	| loadAbort (_, ABORT) = ABORT

      (* load (config) = Status
         reset global signature and then reads the files in config
         in order, stopping at the first error.
      *)
      fun load (pwdir, sources) =
	  (reset ();
	   if pwdir = OS.FileSys.getDir () (* allow shorter messages if safe *)
	     then List.foldl loadAbort OK sources
	   else List.foldl loadAbort OK
	        (List.map (fn p => OS.Path.mkAbsolute (p, pwdir)) sources))

      fun define (sources) = (OS.FileSys.getDir (), sources)

    end  (* structure Config *)
  in

    (* re-exporting environment parameters and utilities defined elsewhere *)
    structure Print :
      sig
	val implicit : bool ref		(* false, print implicit args *)
	val depth : int option ref	(* NONE, limit print depth *)
	val length : int option ref	(* NONE, limit argument length *)
	val indent : int ref		(* 3, indentation of subterms *)
	val width : int ref		(* 80, line width *)
      end
    =
    struct
      val implicit = Print.implicit
      val depth = Print.printDepth
      val length = Print.printLength
      val indent = Print.Formatter.Indent
      val width = Print.Formatter.Pagewidth
    end

    structure Timers :
      sig
	val show : unit -> unit		(* show and reset timers *)
	val reset : unit -> unit		(* reset timers *)
	val check : unit -> unit		(* display, but not no reset *)
      end
    = Timers

    structure OS  :
      sig
	val chDir : string -> unit	(* change working directory *)
	val getDir : unit -> string	(* get working directory *)
	val exit : unit -> unit		(* exit Twelf and ML *)
      end
    =
    struct
      val chDir = OS.FileSys.chDir
      val getDir = OS.FileSys.getDir
      fun exit () = OS.Process.exit (OS.Process.success)
    end

    structure Prover :
    sig					(* F=Filling, R=Recursion, S=Splitting *)
      datatype Strategy = datatype MetaGlobal.Strategy  (* FRS or RFS *)
      val strategy : Strategy ref	(* FRS, strategy used for %prove *)
      val maxSplit : int ref		(* 2, bound on splitting  *)
      val maxRecurse : int ref		(* 10, bound on recursion *)
    end
    =
    struct
      datatype Strategy = datatype MetaGlobal.Strategy  (* FRS or RFS *)
      val strategy = MetaGlobal.strategy
      val maxSplit = MetaGlobal.maxSplit
      val maxRecurse = MetaGlobal.maxRecurse
    end

    val chatter : int ref = Global.chatter
    val doubleCheck : bool ref = Global.doubleCheck

    datatype Status = datatype Status
    val reset = reset
    val loadFile = loadFile
    val readDecl = readDecl
    val decl = decl

    val top = top

    structure Config :
      sig
	type config			(* configuration *)
	val read : string -> config	(* read configuration from config file *)
	val load : config -> Status	(* reset and load configuration *)
	val define : string list -> config  (* explicitly define configuration *)
      end
    = Config

    val version = "Twelf 1.2, Aug 27 1998"
  end  (* local *)
end; (* functor Twelf *)