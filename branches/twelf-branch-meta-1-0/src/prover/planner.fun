structure DbgPlanner =
struct

structure I = IntSyn;

type AaName = int;
type ApiName = string option;
type McName = int;
type MlamName = string option;
type Mbound = int;

(* LF Families *)
datatype A 
  = Aa of AaName 
  | Aapp of A * M 
  | Api of ApiName * A * A
(* LF Objects *)
and M 
  = Mc of McName
  | Md of McName
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
  = Ea of AaName * Azip
  | Eapp of (A * M) * Azip
  | Epi of (ApiName * A * A) * Azip
(* LF Objects *)
and EmbM 
  = EMc of McName * Mzip
  | EMx of Mbound * Mzip
  | EMlam of (MlamName * A * M) * Mzip
  | EMapp of (M * M) * Mzip;


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


(* Invariant : G |- V : exp    G |- M : exp *)
fun expToA (I.Root (I.Const c, S)) = expToASpine (Aa c, S)
  | expToA (I.Pi ((I.Dec (x, V1), _), V2)) = 
      Api (x, expToA V1, expToA V2)

and expToASpine (A, I.Nil) = A
  | expToASpine (A, I.App (U, S)) =
      expToASpine (Aapp (A, expToM U), S)
  
and expToM (I.Root (I.Const c, S)) = expToMSpine ((Mc c), S)
  | expToM (I.Root (I.Def d, S)) = expToMSpine ((Md d), S)
  | expToM (I.Root (I.BVar k, S)) = expToMSpine ((Mx k), S)
  | expToM (I.Lam (I.Dec (x, V), U)) = Mlam (x, expToA V, expToM U)

and expToMSpine (M, I.Nil) = M
  | expToMSpine (M, I.App (U, S)) = 
      expToMSpine (Mapp (M, expToM U), S)


fun plan name = 
    let
      val cid = valOf (Names.constLookup (valOf (Names.stringToQid name)))
      val V = I.conDecType (I.sgnLookup cid)
    in
      print (Print.expToString (I.Null, V))
    end;

end; (* struct Planner *)

structure Planner : PLANNER = DbgPlanner;