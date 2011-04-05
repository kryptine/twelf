(* Truthful monadic abstractions *)
(* Taus Brock-Nannestad, Carsten Schuermann *)

functor Tma 
  ( structure Print : PRINT 
    structure Names : NAMES
  ) : TMA = 
  struct 
    structure F = Print.Formatter
    structure N = Names
    structure I = IntSyn
   (* labels for cases for tracing coverage checker *)
    datatype caseLabel =
        Top				(* ^ *)
      | Child of caseLabel * int        (* lab.n, n >= 1 *)

    fun labToString (Top) = "^"
      | labToString (Child(lab, n)) = labToString(lab) ^ "." ^ Int.toString(n)

    fun chatter chlev f =
        if !Global.chatter >= chlev
	  then print (f ())
	else ()

    fun pluralize (1, s) = s
      | pluralize (n, s) = s ^ "s"

    (* we pass in the mode spine specifying coverage, but currently ignore it *)
    fun abbrevCSpine (S, ci) = S

    (* fix to identify existential and universal prefixes *)
    fun abbrevCGoal (G, V, 0, ci) = (G, abbrevCGoal' (G, V, ci))
      | abbrevCGoal (G, I.Pi((D, P), V), p, ci) = (* p > 0 *)
        let 
	  val D' = N.decEName (G, D)
	in
	  abbrevCGoal (I.Decl (G, D'), V, p-1, ci)
	end
    and abbrevCGoal' (G, I.Pi((D, P), V), ci) =
        let
	  val D' = N.decUName (G, D)
	in
	  I.Pi ((D', P), abbrevCGoal' (I.Decl (G, D'), V, ci))
	end
      | abbrevCGoal' (G, I.Root (a, S), ci) =
 	  I.Root (a, abbrevCSpine (S, ci))

    fun formatCGoal (V, p, ci) =
        let
	  val _ = N.varReset I.Null
	  val (G, V') = abbrevCGoal (I.Null, V, p, ci)
	in
	  F.HVbox [Print.formatCtx (I.Null, G), F.Break, F.String "|-",
		   F.Space, Print.formatExp (G, V')]
	end

    fun formatCGoals ((V,p)::nil, ci) = [formatCGoal (V, p, ci)]
      | formatCGoals ((V,p)::Vs, ci) =
          formatCGoal (V, p, ci) :: F.String "," :: F.Break :: formatCGoals (Vs, ci)
      | formatCGoals (nil, _) = []

    fun missingToString (Vs, ci) =
        F.makestring_fmt (F.Hbox [F.Vbox0 0 1 (formatCGoals (Vs, ci)), F.String "."])

    fun resolve (Vs, ms)=  (print "Welcome to the theorem prover\n";
			    print (missingToString (Vs, ms));
			    print "\nGood-bye\n";
			    (Vs, ms))
  end 