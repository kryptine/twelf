(* Coverage checker for programs *)
(* Author: Carsten Schuermann *)

functor TomegaCoverage
  (structure IntSyn' : INTSYN
   structure Tomega' : TOMEGA
     sharing Tomega'.IntSyn = IntSyn'
   structure Normalize : NORMALIZE
     sharing Normalize.IntSyn = IntSyn'
     sharing Normalize.Tomega = Tomega'
   structure TomegaPrint : TOMEGAPRINT
     sharing TomegaPrint.IntSyn = IntSyn'
     sharing TomegaPrint.Tomega = Tomega'
   structure TomegaTypeCheck : TOMEGATYPECHECK
     sharing TomegaTypeCheck.IntSyn = IntSyn'
     sharing TomegaTypeCheck.Tomega = Tomega'
   structure Cover : COVER
     sharing Cover.IntSyn = IntSyn'
     sharing Cover.Tomega = Tomega') : TOMEGACOVERAGE = 
struct
  structure IntSyn = IntSyn'
  structure Tomega = Tomega'

  exception Error of string 
  
  local 
    structure I = IntSyn'
    structure T = Tomega
      

    (* purifyFor ((P, t), (Psi, F), s) = (t', Psi', s')

       Invariant:
       If    Psi0 |- t : Psi
       and   Psi0 |- P in F[t]
       and   Psi |- s : Psi1
       and   P == <M1, <M2, ... Mn, <>>>>
       and   F[t] = Ex x1:A1 ... Ex xn:An.true
       then  Psi' = Psi, x::A1, .... An
       and   t' = Mn...M1.t
       then  Psi0 |- t' : Psi'
       and   Psi' |- s' : Psi1
    *)
    fun purifyFor ((T.Unit, t), (Psi, T.True), s) = (t, Psi, s)
      | purifyFor ((T.PairExp (U, P), t), (Psi, T.Ex (D, F)), s) =
	  purifyFor ((P, T.Dot (T.Exp U, t)), (I.Decl (Psi, T.UDec D), F), T.comp (s, T.shift))
    (*  | purifyFor (Psi, T.All (_, F), s) = (Psi, s)
        cannot occur by invariant Mon Dec  2 18:03:20 2002 -cs *)
         
    (* purifyCtx (t, Psi) = (t', Psi', s')
       If    Psi0 |- t : Psi
       then  Psi0 |- t' : Psi'
       and   Psi' |- s' : Psi
    *)
    fun purifyCtx (t as T.Shift k, Psi) =  (t, Psi, T.id)
      | purifyCtx (T.Dot (T.Prg P, t), I.Decl (Psi, T.PDec (_, T.All _))) =
        let 
	  val (t', Psi', s') = purifyCtx (t, Psi)
	in 
          (t', Psi', T.Dot (T.Undef, s'))
	end
      | purifyCtx (T.Dot (T.Prg P, t), I.Decl (Psi, T.PDec (_, F))) =
        let 
	  val (t', Psi', s') = purifyCtx (t, Psi)
	  val (t'', Psi'', s'') = purifyFor ((P, t'), (Psi', Normalize.normalizeFor (F, s')), s')
	in 
          (t'', Psi'', T.Dot (T.Undef, s''))
	end
      | purifyCtx (T.Dot (F, t), I.Decl (Psi, T.UDec D)) =
        let 
	  val (t', Psi', s') = purifyCtx (t, Psi)
	in
	  (T.Dot (F, t'), I.Decl (Psi', T.UDec (I.decSub (D, T.coerceSub s'))), T.dot1 s')
	end


    fun purify (Psi0, t, Psi) = 
        let 
	  val (t', Psi', s') = purifyCtx (t, Psi)
	  val _ = TomegaTypeCheck.checkSub (Psi0, t', Psi')
	  val _ = print "*"
	in 
	  (Psi0, t', Psi')
	end


    (* subToSpine (Psi', t, Psi) *)
    fun coverageCheckPrg (W, Psi, T.Lam (D, P)) = 
          coverageCheckPrg (W, I.Decl (Psi, D), P)
      | coverageCheckPrg (W, Psi, T.New P) = 
	  coverageCheckPrg (W, Psi, P)
      | coverageCheckPrg (W, Psi, T.PairExp (U, P)) = 
	  coverageCheckPrg (W, Psi, P)
      | coverageCheckPrg (W, Psi, T.PairBlock (B, P)) = 
	  coverageCheckPrg (W, Psi, P)
      | coverageCheckPrg (W, Psi, T.PairPrg (P1, P2)) = 
	  (coverageCheckPrg (W, Psi, P1); coverageCheckPrg (W, Psi, P2))
      | coverageCheckPrg (W, Psi, T.Unit) = ()
      | coverageCheckPrg (W, Psi, T.Root (H, S)) = 
	  coverageCheckSpine (W, Psi, S)
      | coverageCheckPrg (W, Psi, T.Rec (D, P)) = 
	  coverageCheckPrg (W, I.Decl (Psi, D), P)
      | coverageCheckPrg (W, Psi, T.Case (T.Cases Omega)) = 
	  coverageCheckCases (W, Psi, Omega, nil)
      | coverageCheckPrg (W, Psi, P as T.Let (D, P1, P2)) = 
	  (coverageCheckPrg (W, Psi, P1);
	   print (TomegaPrint.prgToString (Psi, P)); 
	   coverageCheckPrg (W, I.Decl (Psi, D), P2))
(*    | coverageCheckPrg (Psi, T.Redex (P, S)) = 
          should not occur by invariant  *)
(*    | coverageCheckPrg (Psi, T.EVar) = 
          should not occur by invariant  *)

    and coverageCheckSpine (W, Psi, T.Nil) = ()
      | coverageCheckSpine (W, Psi, T.AppExp (U, S)) = 
          coverageCheckSpine (W, Psi, S)
      | coverageCheckSpine (W, Psi, T.AppBlock (B, S)) =
	  coverageCheckSpine (W, Psi, S)
      | coverageCheckSpine (W, Psi, T.AppPrg (P, S)) =
	  (coverageCheckPrg (W, Psi, P);
	   coverageCheckSpine (W, Psi, S))
(*    | coverageCheckSpine (Psi, T.SClo _) = 
          should not occur by invariant  *)

      
    and coverageCheckCases (W, Psi, nil, Cs) = 
      let 
	  val _ = print ("[coverage]" ^ Int.toString (List.length Cs) ^ " cases\n")
	  val (Cs' as (_, _, Psi') :: _) = map purify Cs
	  val Cs'' = map (fn (Psi0, t, _) => (T.coerceCtx Psi0, T.coerceSub t)) Cs'
	in
	  Cover.coverageCheckCases (W, Cs'', T.coerceCtx Psi')
	end
      | coverageCheckCases (W, Psi, (Psi', t, P) :: Omega, Cs) =
	  (coverageCheckPrg (W, Psi', P); 
	   coverageCheckCases (W, Psi, Omega, 
			       (Psi', t, Psi) :: Cs))
  in
    val coverageCheckPrg = coverageCheckPrg
  end
end	      
