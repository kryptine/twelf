(* Introduce *)
(* Author: Carsten Schuermann *)

functor Introduce 
  ((*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure State' : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
       ) : INTRODUCE  =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'

  local 
  structure S = State'
  structure T = Tomega
  structure I = IntSyn

    exception Error = S.Error
    type operator = T.Prg option ref * T.Prg

    fun stripTC (T.Abs (_, TC)) = TC
      
    fun stripTCOpt NONE = NONE
      | stripTCOpt (SOME TC) = SOME (stripTC TC)

    fun stripDec (T.UDec D) = T.UDec D
      | stripDec (T.PDec (name, F, TC1, TC2)) = T.PDec (name, F, TC1, stripTCOpt TC2)

    fun strip I.Null = I.Null
      | strip (I.Decl (Psi, D)) = I.Decl (strip Psi, stripDec D)


    (* expand S = S'

       Invariant:
       If   S = (Psi |> all x1:A1 .... xn: An. F)
       and  F does not start with an all quantifier
       then S' = (Psi, x1:A1, ... xn:An |> F)
    *)
    fun expand (S.Focus (T.EVar (Psi, r, T.All ((D, _), F), NONE, NONE), W)) =  
	  SOME (r, T.Lam (D, T.newEVar (I.Decl (strip Psi, D), F)))
      | expand (S.Focus (T.EVar (Psi, r, T.Ex ((D as I.Dec (_, V), _), F), NONE, NONE), W)) =  
	   let 
	     val X = I.newEVar (T.coerceCtx (Psi), V)
	     val Y = T.newEVar (Psi, T.forSub (F, T.Dot (T.Exp X, T.id)))
	   in
	     SOME (r, T.PairExp (X, Y))
	   end
      | expand (S.Focus (T.EVar (Psi, r, T.True, NONE, NONE), W)) = 
	   (SOME (r, T.Unit))
      | expand (S.Focus (T.EVar (Psi, r, _, _, _), W)) = NONE

    (* apply O = S 
     
       Invariant:
       O = S 
    *)
    fun apply (r, P) = (r := SOME P)   (* need to trail for back *)

    (* menu O = s 

       Invariant:
       s = "Apply universal introduction rules"
    *)
    fun menu _ = "Intro"
      

  in
    exception Error = Error
    type operator = operator
      
    val expand = expand
    val apply = apply
    val menu =menu
  end
end