(* Lexer *)
(* Author: Frank Pfenning *)

signature LEXER =
sig

  (* Stream is not memoizing for efficiency *)
  structure Stream : STREAM
  structure Paths : PATHS

  datatype IdCase =
      Upper				(* [A-Z]<id> or _<id> *)
    | Lower				(* any other <id> *)
    | Quoted				(* '<id>', currently unused *)

  datatype Token =
      EOF				(* end of file or stream, also `%.' *)
    | DOT				(* `.' *)
    | COLON				(* `:' *)
    | LPAREN | RPAREN			(* `(' `)' *)
    | LBRACKET | RBRACKET		(* `[' `]' *)
    | LBRACE | RBRACE			(* `{' `}' *)
    | BACKARROW | ARROW			(* `<-' `->' *)
    | TYPE				(* `type' *)
    | EQUAL				(* `=' *)
    | LESS                              (* `<' *)  (*  -bp6/5/99. *)
    | LEQ 				(* `<=' *) (*  -bp6/5/99. *)
    | ID of IdCase * string		(* identifer *)
    | UNDERSCORE			(* `_' *)
    | INFIX | PREFIX | POSTFIX		(* `%infix' `%prefix' `%postfix' *)
    | NAME				(* `%name' *)
    | SOLVE				(* `%solve' *)
    | QUERY				(* `%query' *)
    | MODE				(* `%mode' *)
    | TERMINATES       			(* `%terminates' *)
    | REDUCES       			(* `%reduces' *) (*  -bp6/5/99. *)
    | THEOREM                           (* `%theorem' *)
    | PROVE                             (* `%prove' *)
    | ESTABLISH				(* `%establish' *)
    | ASSERT				(* `%assert' *)
    | ABBREV				(* `%abbrev' *)
    | USE                               (* `%use'    *)
    | STRING of string                  (* string constants *)

  exception Error of string

  (* lexer returns an infinite stream, terminated by EOF token *)
  val lexStream : TextIO.instream -> (Token * Paths.region) Stream.stream
  val lexTerminal : string * string -> (Token * Paths.region) Stream.stream

  val toString : Token -> string

  (* Utilities *) 
  exception NotDigit of char
  val stringToNat : string -> int
  val isUpper : string -> bool
end;  (* signature LEXER *)
