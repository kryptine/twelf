(* Proof-theoretic compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Carsten Schuermann, Larry Greenfield, Roberto Virga *)
(* Modified: Kevin Watkins *)

functor PTCompile (structure IntSyn' : INTSYN
                   structure CompSyn' : COMPSYN
                     sharing CompSyn'.IntSyn = IntSyn'
                   structure Whnf : WHNF
                     sharing Whnf.IntSyn = IntSyn'
                   structure Abstract : ABSTRACT
                     sharing Abstract.IntSyn = IntSyn') : PTCOMPILE =
struct

  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'

  local
    structure I = IntSyn
    structure C = CompSyn
  in

    exception Error of string

    (* isConstraint(H) = B
       where B iff H is a constant with constraint status
    *)
    fun isConstraint (I.Const (c)) =
          (case I.constStatus (c)
             of (I.Constraint _) => true
              | _ => false)
      | isConstraint H = false

    (* head (A) = H, the head of V

       Invariants:
       G |- A : type, A enf
       A = H @ S
    *)
    fun head (I.Root(h, _)) = h
      | head (I.Pi (_, A)) = head(A)

  (* compileGoalN  fromCS A => g
     if A is a type interpreted as a subgoal in a clause and g is its
     compiled form.  No optimization is performed.

     Invariants:
     If G |- A : type,  A enf
        A has no existential type variables
     then G |- A ~> g  (A compiles to goal g)
     and  G |- g  goal

     Note: we don't accept objects that may introduce assumptions of
     constraint types, unless fromCS = true (the object come from a
     Constraint Solver module.
  *)
  fun compileGoalN fromCS (R as I.Root _) =
      (* A = H @ S *)
        C.Atom (R)
    | compileGoalN fromCS (I.Pi((I.Dec(_,A1), I.No), A2)) =
      (* A = A1 -> A2 *)
      let
	val a1 = I.targetFam A1
      in
	(* A1 is used to build the proof term, a1 for indexing *)
	C.Impl (compileClauseN fromCS A1, A1, a1, 
		compileGoalN fromCS A2)
      end
    | compileGoalN fromCS (I.Pi((D as I.Dec (_, A1), I.Maybe), A2)) =
      (* A = {x:A1} A2 *)
       if not fromCS andalso isConstraint (head (A1))
       then raise Error "constraint appears in dynamic clause position"
       else C.All (D, compileGoalN fromCS A2)
  (*  compileGoalN _ should not arise by invariants *)

  (* compileClauseN A => G
     if A is a type interpreted as a clause and G is its compiled form.

     Some optimization is attempted if so flagged.

     Invariants:
     If G |- A : type, A enf
        A has no existential type variables
     then G |- A ~> r  (A compiles to residual goal r)
     and  G |- r  resgoal
  *)

  and compileClauseN fromCS (R as I.Root (h, S)) =
        if not fromCS andalso isConstraint (h)
        then raise Error "constraint appears in dynamic clause position"
        else C.Eq(R)
    | compileClauseN fromCS (I.Pi((D as (I.Dec(_,A1)),I.No), A2)) =
      (* A = A1 -> A2 *)
	C.And (compileClauseN fromCS A2, A1, 
	       compileGoalN fromCS A1)
    | compileClauseN fromCS (I.Pi((D as (I.Dec(_,A1)),I.Meta), A2)) =
      (* A = {x: A1} A2, x  meta variable occuring in A2 *)
	C.In (compileClauseN fromCS A2, A1, 
		compileGoalN fromCS A1)
    | compileClauseN fromCS (I.Pi((D,I.Maybe), A2)) =
      (* A = {x:A1} A2 *)
        C.Exists (D, compileClauseN fromCS A2)
    (*  compileClauseN _ should not arise by invariants *)

  fun compileClause fromCS A = compileClauseN fromCS (Whnf.normalize (A, I.id))
  fun compileGoal fromCS A = compileGoalN fromCS (Whnf.normalize (A, I.id))

  (* wrapQuery (G, (q, s)) = q'

     Invariants:
     If  . |- s : G  and  G |- q query
     then  . |- q' query
  *)
  fun wrapQuery (I.Null, (q, s)) = q (* s = I.id *)
    | wrapQuery (I.Decl(G, V), (q, I.Dot(I.Exp(U), s))) =
        wrapQuery (G, (C.QueryVar(U, V, q), s))
    
  (* compileQuery fromCS (A) = q

     Invariants:
     If    . |- A : type
     then  . |- q query
     and   . |- A ~> q
  *)
  fun compileQuery fromCS (A) =
      let
        val (G, (A', s)) = Abstract.abstractQuery (A)
      in
        wrapQuery (G, (C.QueryGoal(compileGoalN fromCS A'), s))
      end

  (* compileConDec (a, condec) = ()
     Effect: install compiled form of condec in program table.
             No effect if condec has no operational meaning
  *)
  (* Defined constants are currently not compiled *)
  fun compileConDec fromCS (I.ConDec(_, _, _, A, I.Type)) =
        SOME (compileClauseN fromCS A)
    | compileConDec fromCS (I.SkoDec(_, _, A, I.Type)) =
        SOME (compileClauseN fromCS A)
    | compileConDec _ _ = NONE

  end  (* local open ... *)

end
