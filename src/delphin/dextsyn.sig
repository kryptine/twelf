(* Delphin external syntax *)


signature DEXTSYN = 
sig

(* structure Lexer : LEXER *)

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

and Cases 
  = First of Pat * Prog
  | Alt of Cases * Pat * Prog

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

end







