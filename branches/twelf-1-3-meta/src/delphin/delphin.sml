(* Delphin Front End Interface *)
(* Author: Carsten Schuermann *)

structure DextSyn : DEXTSYN = 
    DextSyn (structure Stream' = Stream
             structure ParseTerm' = ParseTerm
             structure ExtSyn' = ParseTerm.ExtSyn
             structure Parsing' = Parsing
             structure Lexer' = Lexer);

structure DelphinLrVals : Delphin_LRVALS = 
   DelphinLrValsFun (structure Token = LrParser.Token
                     structure DextSyn' = DextSyn
                     structure Stream = Stream
                     structure Lexer' = Lexer
                     structure Parsing' = Parsing);

structure Interface : INTERFACE = Interface ();

structure DelphinLex : LEXERR =
   DelphinLexFun (structure Tokens = DelphinLrVals.Tokens
                  structure Interface = Interface
                  structure Lexer = Lexer);

structure DelphinParser : PARSERR =
   Join (structure ParserData = DelphinLrVals.ParserData
         structure Lex = DelphinLex
         structure LrParser = LrParser);

structure Parse : PARSE =
   Parse (structure DextSyn = DextSyn
          structure Interface = Interface
          structure Parserr = DelphinParser
          structure Tokens = DelphinLrVals.Tokens);
(*
structure Trans (*: TRANS *) =
   Trans (structure DextSyn' = DextSyn
	  structure ParseTerm' = ParseTerm
	  structure Print = Print
          structure Tomega' = Tomega
          structure ExtSyn' =  TpRecon
          structure IntSyn' = Tomega.IntSyn
	  structure Unify = UnifyTrail
	  structure Abstract = Abstract
          structure TpRecon' = TpRecon
	  structure TypeCheck = TypeCheck
	  structure Names = Names
	  structure Whnf = Whnf
          structure Stream' = Stream
	  structure Normalize = Normalize
          structure DelphinPrint = DelphinPrint
          structure Parsing' = Parsing
	  structure Paths = Paths)

*)



structure Delphin = 
  Delphin (structure Tomega = Tomega
	   structure Twelf = Twelf
	   structure Parse = Parse
	   structure DextSyn = DextSyn
	   structure Parser = Parser);

(*
structure Tomega =
  Tomega (structure IntSyn' = IntSyn
	  structure Whnf = Whnf
	  structure Conv = Conv);

structure Normalize =
  Normalize (structure Tomega' = Tomega);
*)
 (*structure Opsem =
  Opsem (structure Tomega' = Tomega
	 structure Unify = UnifyTrail
	 structure Normalize = Normalize);
*)




