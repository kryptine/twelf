(* Delphin external syntax *)
(* Author: Richard Fontana *)

functor DextSyn ( (* structure Stream' : STREAM *)
                  structure ExtSyn' : EXTSYN  
                  structure Parsing' : PARSING 
(*                    sharing Parsing'.Lexer.Paths = ExtSyn'.Paths  *)
(*                  structure Lexer' : LEXER *)
(*                    sharing Lexer' = Parsing'.Lexer *)
      ) : DEXTSYN =

struct
(*  structure Stream = Stream' *)
  structure ExtSyn = ExtSyn'  
  structure Parsing = Parsing' 
(*  structure Paths = ExtSyn.Paths
  structure Lexer = Lexer' *)
  structure L = Lexer
(*  structure S = Parsing'.Lexer.Stream *)
  structure S = Stream



datatype Ast =  Ast of Decs

and Decs 
  = Empty
  | FunDecl of FunDecl * Decs
  | FormDecl of FormDecl * Decs
  | ValDecl of ValDecl * Decs

and FormDecl 
  = Form of string * Form

and FunDecl 
  = Fun of Head * Prog
  | Bar of Head * Prog

and ValDecl
  = Val of Pat * Prog * Form option

and Cases 
  = First of Pat * Prog
  | Alt of Cases * Pat * Prog


and Form 
  = True
  | Forall of string * Form
  | Exists of string * Form
  | And of Form * Form
  | World of string * Form
(* | Arrow of Form * Form *)
(* | WldDef of (string list) * Form *)

and Prog 
  = Unit 
  | Pair of Prog * Prog
  | AppProg of Prog * Prog
  | AppTerm of Prog * string
  | Inx of string * Prog 
  | Lam of string * Prog
  | Const of string
  | Case of  (Pat list * Prog) list
  | Let of Decs * Prog 
  | New of string * Prog 
(* | Rec of MDec * Prog *)

and Head 
  = Head of string
  | AppLF of Head * Term
  | AppMeta of Head * Pat

and Pat 
  = PatInx of Term * Pat
  | PatPair of Pat * Pat
  | PatVar of MDec
  | PatUnderscore 
  | PatUnit 

and MDec 
  = MDec of string * (Form option)

and Block 
  = Block of string list

and Term 
  = Term of string


local
(*
fun parseLFDecs (Ast dl) =
  let val tf = OS.FileSys.tmpName ()
      val tos = TextIO.openOut tf
      fun parseLFDecs' [] = ()
       |  parseLFDecs' ((LFConDec ld) ::ds) =
           (TextIO.output(tos, ld); 
           parseLFDecs' ds)
       |  parseLFDecs' (_ ::ds) = parseLFDecs' ds          
      val _ = parseLFDecs' dl
      val _ = TextIO.closeOut tos
      val _ = Twelf.loadFile tf
      val _ = OS.FileSys.remove tf
  in ()
  end

*)
(*

fun rulesToCase (Ast decs) =
   let 
      fun rulesToCase' [] = []
      |   rulesToCase' (ProgDec (Head (s,pts), prg) :: ds) =
            let val cds = rulesToCase' ds
            in 
               case cds of
                  ProgDec (Head (s',_), Case ps) ::ds'' =>
                     if s = s' 
                     then ProgDec (Head (s, []), Case ((pts,prg)::ps))::ds''
                     else 
                         ProgDec (Head (s,[]), Case [(pts,prg)]):: cds
                | _ => ProgDec (Head (s,[]), Case [(pts,prg)]):: cds
             end           
      |   rulesToCase' (d::ds) =
             let val cds = rulesToCase' ds
             in
                (d::cds)
             end
             
   in 
      Ast (rulesToCase' decs)
   end


 (* Invariant:  all programs in ast have been put in case form *)
  fun abstractProgs' [] = []
    | abstractProgs' (ProgDec (Head (nm,e), cp)::ds) =
         ProgDec (Head (nm,e), Rec (MDec (nm, NONE), cp))::
                 (abstractProgs' ds)
    | abstractProgs' (d::ds) = (d::(abstractProgs' ds))


 fun abstractProgs ast = 
      let 
          val ast' = rulesToCase ast
          val (Ast decs) = ast'
          val decs' = abstractProgs' decs
      in (Ast decs')
      end          

*)
in 
(*     val appendPats = appendPats
     val parseLFDecs = parseLFDecs
     val abstractProgs = abstractProgs
*)
end

end (* functor DextSyn *)
























