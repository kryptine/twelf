structure DbgPlanner =
struct

structure I = IntSyn;

type AaName = string;
type ApiName = string;
type McName = string;
type MlamName = string;
type Mbound = int;

(* LF Families *)
datatype A 
  = Aa of AaName 
  | Aapp of A * M 
  | Api of ApiName * A * A
(* LF Objects *)
and M 
  = Mc of McName
  | Mx of Mbound
  | Mlam of MlamName * A * M
  | Mapp of M * M;

(* Delphin things *)
type DlamName = string;
datatype D
  = Top
  | Forall of (DlamName * A * D)
  | Exists of (DlamName * A * D);

(* derivative of Families in Families *)
datatype dAA
  = dAAapp1 of M
  | dAAapp2 of A
  | dAApi1 of ApiName * A
  | dAApi2 of ApiName * A;
(* derivative of Families in Objects *)
datatype dAM
  = dAMlam of MlamName * M
(* derivative of Objects in Families *)
datatype dMA
  = dMAapp2 of A;
(* derivative of Objects in Objects *)
datatype dMM
  = dMMlam of MlamName * A
  | dMMapp1 of M
  | dMMapp2 of M;

(* deriviatives wrt both *)
datatype dA = Dam of dAM * (dM list)
            | Daa of dAA
and dM = Dmm of dMM
       | Dma of dMA * (dA list);

(* one hole contexts: zippers *)
type Mzip = dM list;
type Azip = dA list;

(* Embeddings of LF Type Families *)
datatype EmbA 
  = Aa of AaName * Azip
  | Aapp of (A * M) * Azip
  | Api of (ApiName * A * A) * Azip
(* LF Objects *)
and EmbM 
  = Mc of McName * Mzip
  | Mx of Mbound * Mzip
  | Mlam of (MlamName * A * M) * Mzip
  | Mapp of (M * M) * Mzip;


(* embeddings *)
datatype Dir = GoalToRule | RuleToGoal;

datatype Embed = Embed 
         of { goal : A, (* goal term *)
              rule : A, (* rule you believe to be true *)
              dir : Dir,   (* direction of embedding expression *)
              emb : EmbA  (* embedding expression *)
            };

exception impossible_exps of string * I.Exp * I.Exp;

fun embed goal rule = 
    NONE;                                          

type Plan = unit;

fun plan name = 
    let
      val cid = valOf (Names.constLookup (valOf (Names.stringToQid name)))
      val V = I.conDecType (I.sgnLookup cid)
    in
      print (Print.expToString (I.Null, V))
    end;

end; (* struct Planner *)

structure Planner : PLANNER = DbgPlanner;