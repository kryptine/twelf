

local
  structure I = IntSyn
  structure T = Tomega

  fun load file =
    case Twelf.Config.load (Twelf.Config.read file)
      of Twelf.OK => Twelf.OK
       | Twelf.ABORT => raise Domain;
	

  fun printS nil = ()
    | printS (condec :: S) =
        (TextIO.print ((Print.conDecToString condec) ^ "\n"); printS S)
in

 val _ = Compiler.Control.Print.printDepth := 10;


  fun test names =
    (let 
      val a = map (fn x => valOf (Names.constLookup (valOf (Names.stringToQid x)))) names
      val name = foldr op^ "" names
      val _ = Names.varReset IntSyn.Null 
      val Ss = map Worldify.worldify a
      val S = foldr op@ nil Ss
      val _ = printS S
      val _ = TextIO.print "[tomega] "
      val P = Converter.convertPrg a
      val _ = TextIO.print "Checking: "
      val F = Converter.convertFor a
      val _ = TextIO.print (TomegaPrint.forToString (I.Null, F) ^ "\n")

      val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F))
(*      val _ = (FunTypeCheck.check (P, F); Twelf.OK)   *)
(*      val LD = F.LemmaDec (names, P, F) *)
(*      val _ = TextIO.print (FunPrint.lemmaDecToString LD) *)
    in P
(*      FunNames.installName (name, F.lemmaAdd LD) *)
    end)

       
  fun print names =
    let
      val P = test names
    in
      TextIO.print (TomegaPrint.funToString P ^ "\n")
    end


  val _ = Twelf.chatter := 1
(*  val _ = FunNames.reset(); --cs *)
  

  (* Regression print for Mini-ML *)
  val _ = load "examples/mini-ml/sources.cfg"
  val _ = Twelf.loadFile "examples/mini-ml/reduce.elf"
  val _ = print ["eval"]



  val _ = print ["value"]
  val _ = print ["vs"]
  val _ = print ["tps"]
  val _ = print ["==>"]
(*  val _ = print ["==>*"]     -- error case: Lemmas not yet available *)
(*  val _ = print ["closed"]   -- error case check back later *)

  (* Regression print for prop-calc *)
  val _ = load "examples/prop-calc/sources.cfg"
  val _ = print ["combdefn"]

  (* Regression print for ccc *)
  val _ = load "examples/ccc/sources.cfg"
  val _ = print ["conc"]

  (* Regression print for compile *)
  val _ = load "examples/compile/cpm/sources.cfg"
  val _ = print ["ccp"]
  val _ = print ["peq"]


  (* Regression print for copy *)
  val _ = Twelf.loadFile "TEST/cp.elf"
  val _ = print ["cpt"] 



(*

  (* Regression test for compile *)
  val _ = load "examples/compile/cls/sources.cfg"
  val _ = test ["trans", "vtrans"]
  val _ = test ["feval"]
  val _ = test ["=>"]
  val _ = test [">=>*"]
  val _ = test [">ceval"] 
  val _ = test ["append"]
  val _ = test ["subcomp"] 
  val _ = test ["cev_complete"]
  val _ = test ["<"]
  val _ = test ["trans*"]
  val _ = test ["spl"]
  val _ = test ["cls_sound"]

  (* Regression test for logic programming *)
  val _ = load "examples/lp/sources.cfg"
  val _ = test ["can", "atm"]
  val _ = test ["iscan", "isatm"]
  val _ = test ["s_sound", "h_sound", "i_sound"]
  val _ = test ["cmpcs", "cmpai"]
  val _ = test ["gl", "pg"]
  val _ = test ["r_total"]
  (* Cannot work yet because we do not have mutual
     recursive functions.
  *)

  (* Regression test for Church-Rosser *)
  val _ = load "examples/church-rosser/sources.cfg"
  val _ = test ["identity"]
  val _ = test ["append"]
  val _ = test ["subst"] 
  val _ = test ["dia"]
  val _ = test ["strip"] 
  val _ = test ["conf"]
  val _ = test ["cr"]


  (* Regression test for Cut-Elimination *)
  val _ = load "examples/cut-elim/sources.cfg"
  val _ = test ["ca"]
  val _ = test ["ce"]
  val _ = test ["ca'"]
  val _ = test ["ce'"]

  val _ = load "examples/kolm/sources.cfg"
  val _ = test ["kolm"]
  val _ = test ["existskolm"]
  val _ = test ["nj_nk"]
  val _ = test ["equiv"]
  val _ = test ["complete"]
*)
end

