(* Elim  Version 1.4 *)
(* Author: Carsten Schuermann *)

functor Elim 
  (structure Data : DATA
   (*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure State' : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   (*! sharing Abstract.Tomega = Tomega' !*)
   structure TypeCheck : TYPECHECK
   (*! sharing TypeCheck.IntSyn = IntSyn' !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Unify : UNIFY
   (*! sharing Unify.IntSyn = IntSyn' !*)
 
       )
     : ELIM =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'

  exception Error of string

  datatype Operator = 
    Local of Tomega.Prg * int

  type operator = Operator 

  local
    structure S = State
    structure T = Tomega
    structure I = IntSyn

    exception Success of int

(* These lines need to move *)

    fun stripTC (T.Abs (_, TC)) = TC
      
    fun stripTCOpt NONE = NONE
      | stripTCOpt (SOME TC) = SOME (stripTC TC)

    fun stripDec (T.UDec D) = T.UDec D
      | stripDec (T.PDec (name, F, TC1, TC2)) = T.PDec (name, F, TC1, stripTCOpt TC2)

    fun strip I.Null = I.Null
      | strip (I.Decl (Psi, D)) = I.Decl (strip Psi, stripDec D)


    (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
    fun expand (S.Focus (Y as T.EVar (Psi, r, G, V, _), W)) =   (* Y is lowered *)
      let	  
	fun matchCtx (I.Null, _, Fs) = Fs 
	  | matchCtx (I.Decl (G, T.PDec (x, F, _, _)), n, Fs) =
	  matchCtx (G, n+1, Local (Y, n) :: Fs)
	  | matchCtx (I.Decl (G, T.UDec _), n, Fs) = 
	  matchCtx (G, n+1, Fs)
	  
      in
	matchCtx (Psi, 1, nil)
      end

    (* apply op = B' 

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)
   fun apply (Local (R as T.EVar (Psi, r, T.All ((D, _), F), NONE, NONE), n)) =  
	  (r := SOME (T.Redex (T.Var n, T.AppPrg (T.newEVar (I.Decl (strip Psi, D), F), T.Nil))))
      | apply (Local (T.EVar (Psi, r, T.FClo (F, s), TC1, TC2), n)) = 
	   apply (Local (T.EVar (Psi, r, T.forSub (F, s), TC1, TC2), n)) 


    (* menu op = s'
       
       Invariant: 
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
    fun menu (Local (X as T.EVar (Psi, _, _, _, _), n)) =
        (case (I.ctxLookup (Psi, n)) 
	  of T.PDec (SOME x, _, _, _) => 
	    ("Elim " ^ TomegaPrint.nameEVar X  ^ " with variable " ^ x))
	   (* Invariant: Context is named  --cs Fri Mar  3 14:31:08 2006 *)
      
  in
    val expand = expand
    val apply = apply
    val menu = menu
  end (* local *)
end; (* functor elim *)