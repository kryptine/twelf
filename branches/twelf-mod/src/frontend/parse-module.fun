(* Parsing modules *)
(* Author: Keven Watkins *)
(* Redesigned: Florian Rabe, Jan 09 *)

functor ParseModule
  ((*! structure Paths : PATHS !*)
   (*! structure Parsing' : PARSING !*)
   (*! sharing Parsing'.Lexer.Paths = Paths !*)
   structure ModExtSyn' : MODEXTSYN
   (*! sharing ModExtSyn'.Paths = Paths !*)
   structure ParseTerm : PARSE_TERM
   (*! sharing ParseTerm.Lexer = Parsing'.Lexer !*)
     sharing ParseTerm.ExtSyn = ModExtSyn'.ExtSyn)
  : PARSE_MODULE =
struct

  (*! structure Parsing = Parsing' !*)
  structure ModExtSyn = ModExtSyn'

  structure L = Lexer
  structure LS = Lexer.Stream  
  structure E = ModExtSyn

  type ID = string list * Paths.region
  type Front = (L.Token * Paths.region) LS.front

  fun parseSingleToken' (token, ascii) f' : Paths.region * Front =
     let
     	val LS.Cons ((t, r), s') = f'
     in 
     	if t = token
     	then (r, LS.expose s')
        else Parsing.error (r, "Expected `" ^ ascii ^ "', found token " ^ L.toString t)
     end
  val parseLBrace' = parseSingleToken'(L.LBRACE, "{")
  val parseArrow' = parseSingleToken'(L.ARROW, "->")
  val parseEqual' = parseSingleToken'(L.EQUAL, "=")
  val parseColon' = parseSingleToken'(L.COLON, ":")
  val parseDot' = parseSingleToken'(L.DOT, ".")
  
  fun parseQualId'(f') :  ID * Front =
    let
       val ((ids, (L.ID (_, id), r)), f' as LS.Cons((_,r'),s')) = ParseTerm.parseQualId' (f')
    in
       ((ids @ [id], Paths.join(r, r')), f')
    end
  
  fun parseLink' (f' as LS.Cons ((L.ID _, _), _)) =
      let
          val (id, f') = parseQualId' f'
      in
         (E.morlink(id), f')
      end
    | parseMorph' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected structure or view identifier, found token " ^ L.toString t)

  fun parseMorph'(f' as LS.Cons ((L.ID _, _), _)) =
      let
          val (link, f') = parseLink' f'
      in
         link :: parseMorph(f')
      end
    | parseMorph'(_) = nil

  fun parseConInst' (f' as LS.Cons ((L.ID _, r0), _)) =
      let
         val (con, f') = parseQualId'(f')
         val (_, f') = parseColon'(f')
         val (_, f') = parseEqual'(f')
         val (tm, f') = ParseTerm.parseTerm'(f')
         val (r2, f') = parseDot' (f')
      in
        (E.coninst (con, (tm, Paths.join (r0, r2))), f')
      end
    | parseConInst' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected identifier, found token " ^ L.toString t)

  fun parseStrInst2' (r0, f' as LS.Cons ((L.ID _, r1), _)) =
      let
         val (str, f') = parseQualId' (f')
         val (_, f') = parseColon' (f')
         val (_, f') = parseEqual' (f')
         val (mor, f') = parseMorph' (f')
         val (r3, f') = parseDot' (f')
      in
        (E.strinst (str, (mor, Paths.join (r0, r3))), f')
      end
    | parseStrInst2' (r0, LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected structure identifier, found token " ^ L.toString t)

  fun parseStrInst' (LS.Cons ((L.STRUCT, r), s')) =
        parseStrInst2' (r, LS.expose s')
    | parseStrInst' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `%struct', found token " ^ L.toString t)

  fun parseInsts' (f as LS.Cons ((L.ID _, _), _)) =
      let
        val (inst, f') = parseConInst' (f)
        val (insts, f'') = parseInsts' (f')
      in
        (inst::insts, f'')
      end
    | parseInsts' (f as LS.Cons ((L.STRUCT, _), _)) =
      let
        val (inst, f') = parseStrInst' (f)
        val (insts, f'') = parseInsts' (f')
      in
        (inst::insts, f'')
      end
    | parseInsts' (LS.Cons ((L.RBRACE, _), s')) =
        (nil, LS.expose s')
    | parseInsts' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected identifier, `%struct', or `}', found token " ^ L.toString t)

  fun parseInstantiate' (f as LS.Cons ((L.LBRACE, _), s')) =
        parseInsts' (LS.expose s')
    | parseInstantiate' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `{', found token " ^ L.toString t)

  fun parseSigBegin' (LS.Cons ((L.SIG, r), s')) =
     case LS.expose s'
       of LS.Cons ((L.ID (_, id), r1), s') =>
          let
             val f' = LS.expose s'
             val (_, f') = parseEqual' (f')
             val (_, f') = parseLBrace' (f')
          in
             (E.sigbegin id, f')
          end 
        | LS.Cons ((t, r1), s') =>
	  Parsing.error (r, "Expected new module identifier, found token " ^ L.toString t)

  fun parseViewBegin' (LS.Cons ((L.VIEW, r), s')) =
     case LS.expose s'
       of LS.Cons ((L.ID (_, id), r1), s') =>
          let
             val f' = LS.expose s'
             val (_, f') = parseColon' (f')
             val (dom, f') = parseQualId' (f')
             val (_, f') = parseArrow'(f')
             val (cod, f') = parseQualId' (f')
             val (_, f') = parseEqual' (f')
             val (_, f') = parseLBrace' (f')
          in
             (E.viewbegin(id, dom, cod), f')
          end 
        | LS.Cons ((t, r1), s') =>
	  Parsing.error (r, "Expected new module identifier, found token " ^ L.toString t)

  fun parseStrDec' (LS.Cons ((L.STRUCT, r0), s')) =
     case LS.expose s'
        of LS.Cons ((L.ID (_, id), r1), s1') => (
           case LS.expose s1'
              of LS.Cons ((L.COLON, r2), s2') =>
                 let
                     val f' = LS.expose s2'
                     val (dom,f') = parseQualId'(f')
                     val (_, f') = parseEqual' (f')
                     val (insts, f') = parseInstantiate'(f')
                  in
                     (E.strdec(id, dom, insts), f')
                  end
               | LS.Cons ((L.EQUAL, r2), s2') =>
                 let
                    val (mor, f' as LS.Cons((_,r3),_)) = parseMorph' (LS.expose s2')
                 in
                    ((E.strdef (id, (mor, Paths.join(r0,r3)))), f')
                 end
               | LS.Cons ((t, r), s') =>
                 Parsing.error (r, "Expected `:' or `=', found token " ^ L.toString t)
         )
         | LS.Cons ((t, r), s') =>
           Parsing.error (r, "Expected new identifier, found token " ^ L.toString t)

  (* ignoring these two tokens *)
  fun parseInclude' (LS.Cons ((L.INCLUDE, r), s')) = ((), LS.expose s')
  fun parseOpen' (LS.Cons ((L.OPEN, r), s')) = ((), LS.expose s')

end