(* Coverage checker for programs *)
(* Author: Carsten Schuermann *)

functor TomegaCoverage
  (structure IntSyn' : INTSYN
   structure Tomega' : TOMEGA
     sharing Tomega'.IntSyn = IntSyn'
   structure Cover : COVER
     sharing Cover.IntSyn = IntSyn') : TOMEGACOVERAGE = 
struct
  structure IntSyn = IntSyn'
  structure Tomega = Tomega'

  exception Error of string 
  
  local 
    structure I = IntSyn'
    structure T = Tomega

    (* subToSpine (Psi', t, Psi) *)


    fun coverageCheckPrg (Psi, T.Lam (D, P)) = 
          coverageCheckPrg (I.Decl (Psi, D), P)
      | coverageCheckPrg (Psi, T.New P) = 
	  coverageCheckPrg (Psi, P)
      | coverageCheckPrg (Psi, T.PairExp (U, P)) = 
	  coverageCheckPrg (Psi, P)
      | coverageCheckPrg (Psi, T.PairBlock (B, P)) = 
	  coverageCheckPrg (Psi, P)
      | coverageCheckPrg (Psi, T.PairPrg (P1, P2)) = 
	  (coverageCheckPrg (Psi, P1); coverageCheckPrg (Psi, P2))
      | coverageCheckPrg (Psi, T.Unit) = ()
      | coverageCheckPrg (Psi, T.Root (H, S)) = 
	  coverageCheckSpine (Psi, S)
      | coverageCheckPrg (Psi, T.Rec (D, P)) = 
	  coverageCheckPrg (I.Decl (Psi, D), P)
      | coverageCheckPrg (Psi, T.Case (T.Cases Omega)) = 
	  coverageCheckCases (Psi, Omega, nil)
      | coverageCheckPrg (Psi, T.Let (D, P1, P2)) = 
	  (coverageCheckPrg (Psi, P1);
	   coverageCheckPrg (I.Decl (Psi, D), P2))
(*    | coverageCheckPrg (Psi, T.Redex (P, S)) = 
          should not occur by invariant  *)
(*    | coverageCheckPrg (Psi, T.EVar) = 
          should not occur by invariant  *)

    and coverageCheckSpine (Psi, T.Nil) = ()
      | coverageCheckSpine (Psi, T.AppExp (U, S)) = 
          coverageCheckSpine (Psi, S)
      | coverageCheckSpine (Psi, T.AppBlock (B, S)) =
	  coverageCheckSpine (Psi, S)
      | coverageCheckSpine (Psi, T.AppPrg (P, S)) =
	  (coverageCheckPrg (Psi, P);
	   coverageCheckSpine (Psi, S))
(*    | coverageCheckSpine (Psi, T.SClo _) = 
          should not occur by invariant  *)

      
    and coverageCheckCases (Psi, nil, Cs) = 
        (print ("[coverage]" ^ Int.toString (List.length Cs) ^ " cases\n");
	 Cover.coverageCheckCases (Cs, T.coerceCtx Psi))
      | coverageCheckCases (Psi, (Psi', t, P) :: Omega, Cs) =
	  (coverageCheckPrg (Psi', P); 
	   coverageCheckCases (Psi, Omega, 
			       (T.coerceCtx Psi', T.coerceSub t)
			       :: Cs))
  in
    val coverageCheckPrg = coverageCheckPrg
  end
end	      
