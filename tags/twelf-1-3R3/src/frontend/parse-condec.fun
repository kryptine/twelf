(* Parsing Signature Entries *) 
(* Author: Frank Pfenning *)

functor ParseConDec
  (structure Parsing' : PARSING
   structure ExtSyn' : EXTSYN
   structure ParseTerm : PARSE_TERM
     sharing ParseTerm.Parsing.Lexer = Parsing'.Lexer
     sharing ParseTerm.ExtSyn = ExtSyn')
     : PARSE_CONDEC =
struct

  structure Parsing = Parsing'
  structure ExtSyn = ExtSyn'

  local
    structure L = Parsing.Lexer
    structure LS = Parsing.Lexer.Stream  

    (* parseConDec3  "U" *)
    fun parseConDec3 (optName, optTm, s) =
        let
	  val (tm', f') = ParseTerm.parseTerm' (LS.expose s)
	in
	  (ExtSyn.condef (optName, tm', optTm), f')
	end

    (* parseConDec2  "= U" | "" *)
    fun parseConDec2 (optName, (tm, LS.Cons((L.EQUAL, r), s'))) =
          parseConDec3 (optName, SOME(tm), s')
      | parseConDec2 (SOME(name), (tm, f)) =
	  (ExtSyn.condec (name, tm), f)
      | parseConDec2 (NONE, (tm, LS.Cons((t,r),s'))) =
	  Parsing.error (r, "Illegal anonymous declared constant")

    (* parseConDec1  ": V = U" | "= U" *)
    fun parseConDec1 (optName, LS.Cons ((L.COLON, r), s')) =
          parseConDec2 (optName, ParseTerm.parseTerm' (LS.expose s'))
      | parseConDec1 (optName, LS.Cons ((L.EQUAL, r), s')) =
	  parseConDec3 (optName, NONE, s')
      | parseConDec1 (optName, LS.Cons ((t,r), s')) =
	  Parsing.error (r, "Expected `:' or `=', found " ^ L.toString t)
   

   (* BlockDec parser *)

      
    fun parseBlock (LS.Cons ((L.ID (_, "block"), r), s')) =
          ParseTerm.parseCtx' (LS.expose s')
      | parseBlock (LS.Cons ((t, r), s')) =
	  Parsing.error (r, "Expected `block', found " ^ L.toString t)

    fun parseSome (name, LS.Cons ((L.ID (_, "some"), r), s')) =
        let
	  val (g1, f') = ParseTerm.parseCtx' (LS.expose s')
	  val (g2, f'') = parseBlock f'
	in
	  (ExtSyn.blockdec (name, g1, g2), f'') 
	end
      | parseSome (name, f as LS.Cons ((L.ID (_, "block"), r), s')) =
	let
	  val (g2, f') = parseBlock f
	in
	  (ExtSyn.blockdec (name, nil, g2), f')  
	end
      | parseSome (name, LS.Cons ((t, r), s')) =
	  Parsing.error (r, "Expected `some' or `block', found " ^ L.toString t)

    fun parseBlockDec1 (name, LS.Cons ((L.COLON, r), s')) = 
          parseSome (name, LS.expose s')   
      | parseBlockDec1 (name, LS.Cons ((t, r), s')) =
	  Parsing.error (r, "`:' expected, found token " ^ L.toString t)

    fun parseBlockDec' (LS.Cons ((L.ID (idCase,name), r), s')) =
          parseBlockDec1 (name, LS.expose s')
      | parseBlockDec' (LS.Cons ((t, r), s')) =
	  Parsing.error (r, "Label identifier expected, found token " ^ L.toString t)

    (* parseConDec' : lexResult front -> ExtSyn.ConDec * lexResult front
       Invariant: first token in exposed input stream is an identifier or underscore
    *)
    fun parseConDec' (LS.Cons ((L.ID (idCase,name), r), s')) =
          parseConDec1 (SOME(name), LS.expose s')
      | parseConDec' (LS.Cons ((L.UNDERSCORE, r), s')) =
	  parseConDec1 (NONE, LS.expose s')
      | parseConDec' (LS.Cons ((L.BLOCK, r), s')) = 
	  parseBlockDec' (LS.expose s')

    (* parseConDec --- currently not exported *)
    fun parseConDec (s) = parseConDec' (LS.expose s)
    fun parseAbbrev' (LS.Cons ((L.ABBREV, r), s)) = parseConDec (s) 
  in
    val parseConDec' = parseConDec'
    val parseAbbrev' = parseAbbrev'
  end  (* local ... in *)

end;  (* functor ParseConDec *)