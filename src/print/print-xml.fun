(* Printing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)

functor PrintXML
  ((*! structure IntSyn' : INTSYN !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   structure Constraints : CONSTRAINTS
   (*! sharing Constraints.IntSyn = IntSyn' !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Formatter' : FORMATTER)
  : PRINT_XML =
struct

  (*! structure IntSyn = IntSyn' !*)
structure Formatter = Formatter'

local
  (* Shorthands *)
  structure I = IntSyn
  structure F = Formatter
  val Str = F.String
  fun Str0 (s, n) = F.String0 n s
  fun Name (x) = F.String ("\"" ^ x ^ "\"")
  fun Integer (n) = F.String (Int.toString n)

  fun sexp (fmts) = F.Hbox [Str "(", F.HVbox fmts, Str ")"]

  (* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)
  fun fmtCon (G, I.BVar(n)) = sexp [Str "<Bvar>", F.Break, Integer n, Str "</Bvar>"]
    | fmtCon (G, I.Const(cid)) = sexp [Str "<Const>", F.Break, Integer cid, Str "</Const>"]
    | fmtCon (G, I.Def(cid)) = sexp [Str "<Def>", F.Break, Integer cid, Str "</Def>"]
    (* I.Skonst, I.FVar cases should be impossible *)

  (* fmtUni (L) = "L" *)
  fun fmtUni (I.Type) = Str "<Type>"
    | fmtUni (I.Kind) = Str "<Kind>"

  (* fmtExpW (G, (U, s)) = fmt
     
     format the expression U[s].

     Invariants:
       G is a "printing context" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)
  fun fmtExpW (G, (I.Uni(L), s)) = sexp [Str "<Uni>", F.Break, fmtUni L, Str "</Uni>"]
    | fmtExpW (G, (I.Pi((D as I.Dec(_,V1),P),V2), s)) =
      (case P (* if Pi is dependent but anonymous, invent name here *)
	 of I.Maybe => let
			 val D' = Names.decLUName (G, D) (* could sometimes be EName *)
			 val G' = I.Decl (G, D')
		       in
			 sexp [Str "<Pi>", F.Break, fmtDec (G, (D', s)),
			       F.Break, (* Str "tw*maybe", F.Break, *) fmtExp (G', (V2, I.dot1 s)),
			       Str "</Pi>"]
		       end
	  | I.No => let
		       val G' = I.Decl (G, D)
		    in
		      sexp [Str "<Arrow>", F.Break, fmtDec (G, (D, s)),
			    F.Break, (* Str "tw*no", F.Break,*) fmtExp (G', (V2, I.dot1 s)),
			    Str "</Arrow>"]
		    end)
    | fmtExpW (G, (I.Root (H, S), s)) =
	 sexp [fmtCon (G, H),
	       F.Break, fmtSpine (G, (S, s))]
    | fmtExpW (G, (I.Lam(D, U), s)) = 
      let
	val D' = Names.decLUName (G, D)
	val G' = I.Decl (G, D')
      in
	sexp [Str "<Lam>", F.Break, fmtDec (G, (D', s)),
	      F.Break, fmtExp (G', (U, I.dot1 s)), Str "</Lam>"]
      end
    (* I.EClo, I.Redex, I.EVar not possible *)

  and fmtExp (G, (U, s)) = fmtExpW (G, Whnf.whnf (U, s))

  (* fmtSpine (G, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *)
  and fmtSpine (G, (I.Nil, _)) = Str "<Empty>"
    | fmtSpine (G, (I.SClo (S, s'), s)) =
         fmtSpine (G, (S, I.comp(s',s)))
    | fmtSpine (G, (I.App(U, S), s)) =
	 sexp [Str "<App>", F.Break, fmtExp (G, (U, s)),
	       F.Break, fmtSpine (G, (S, s)), Str "</App>"]

  and fmtDec (G, (I.Dec (NONE, V), s)) =
        sexp [Str "<Dec>", F.Break, fmtExp (G, (V, s)), Str "</Dec>"]
    | fmtDec (G, (I.Dec (SOME(x), V), s)) =
	sexp [Str "<Dec name =", Name x,  Str ">", F.Break, fmtExp (G, (V, s)), Str "</Dec>"]

  (* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
  fun fmtConDec (I.ConDec (name, parent, imp, _, V, L)) =
      let
	val _ = Names.varReset IntSyn.Null
      in
	sexp [Str "<Condec name=",  Name (name), Str ">", F.Break,
	      Integer (imp), F.Break, fmtExp (I.Null, (V, I.id)),
	      F.Break, fmtUni (L), Str "</Condec>"]
      end
    | fmtConDec (I.SkoDec (name, parent, imp, V, L)) =
      Str ("%% Skipping Skolem constant " ^ name ^ " %%")
    | fmtConDec (I.ConDef (name, parent, imp, U, V, L, _)) =
      let
	val _ = Names.varReset IntSyn.Null
      in
	sexp [Str "<Condef name=", Name (name), Str ">", F.Break,
	      Integer (imp), F.Break, fmtExp (I.Null, (U, I.id)),
	      F.Break, fmtExp (I.Null, (V, I.id)),
	      F.Break, fmtUni (L), Str "</Condef>"]
      end
    | fmtConDec (I.AbbrevDef (name, parent, imp, U, V, L)) =
      let
	val _ = Names.varReset IntSyn.Null
      in
	sexp [Str "<Abbrevdef name=", Name (name), Str ">", F.Break,
	      Integer (imp), F.Break, fmtExp (I.Null, (U, I.id)),
	      F.Break, fmtExp (I.Null, (V, I.id)),
	      F.Break, fmtUni (L), Str "</Abbrevdef>"]
      end

  (* fmtEqn assumes that G is a valid printing context *)
  fun fmtEqn (I.Eqn (G, U1, U2)) = (* print context?? *)
      sexp [Str "<Equation>", F.Break, fmtExp (G, (U1, I.id)), F.Break, fmtExp (G, (U2, I.id)),
	    Str "</Equation>"]

  (* fmtEqnName and fmtEqns do not assume that G is a valid printing
     context and will name or rename variables to make it so.
     fmtEqns should only be used for printing constraints.
  *)
  fun fmtEqnName (I.Eqn (G, U1, U2)) =
      fmtEqn (I.Eqn (Names.ctxLUName G, U1, U2))

in

  (* In the functions below, G must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)
  fun formatDec (G, D) = fmtDec (G, (D, I.id))
  fun formatExp (G, U) = fmtExp (G, (U, I.id))
  fun formatSpine (G, S) = fmtSpine (G, (S, I.id))
  fun formatConDec (condec) = fmtConDec (condec)
  fun formatEqn (E) = fmtEqn E

  fun decToString (G, D) = F.makestring_fmt (formatDec (G, D))
  fun expToString (G, U) = F.makestring_fmt (formatExp (G, U))
  fun conDecToString (condec) = F.makestring_fmt (formatConDec (condec))
  fun eqnToString (E) = F.makestring_fmt (formatEqn E)

  fun printSgn () =
      IntSyn.sgnApp (fn (cid) => (print (F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid)));
				  print "\n"))

end  (* local ... *)

end  (* functor PrintXml *)
