(* Coverage checker for programs *)
(* Author: Carsten Schuermann *)

functor TomegaCoverage
  (structure IntSyn' : INTSYN
   structure Tomega' : TOMEGA
     sharing Tomega'.IntSyn = IntSyn'
   structure TomegaPrint : TOMEGAPRINT
     sharing TomegaPrint.IntSyn = IntSyn'
     sharing TomegaPrint.Tomega = Tomega'
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
        (print ("[coverage]" ^ Int.toString (List.length Cs) ^ " cases\n");
	 Cover.coverageCheckCases (W, Cs, T.coerceCtx Psi))
      | coverageCheckCases (W, Psi, (Psi', t, P) :: Omega, Cs) =
	  (coverageCheckPrg (W, Psi', P); 
	   coverageCheckCases (W, Psi, Omega, 
			       (T.coerceCtx Psi', T.coerceSub t)
			       :: Cs))
  in
    val coverageCheckPrg = coverageCheckPrg
  end
end	      
