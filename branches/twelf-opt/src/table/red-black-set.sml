(* redblack-set.sml
 *
 * This code is based on Chris Okasaki's implementation of
 * red-black trees.  The linear-time tree construction code is
 * based on the paper "Constructing red-black trees" by Hinze,
 * and the delete function is based on the description in Cormen,
 * Leiserson, and Rivest.
 *
 * A red-black tree should satisfy the following two invariants:
 *
 *   Red Invariant: each red node has a black parent.
 *
 *   Black Condition: each path from the root to an empty node has the
 *     same number of black nodes (the tree's black height).
 *
 * The Red condition implies that the root is always black and the Black
 * condition implies that any node with only one child will be black and
 * its child will be a red leaf.
 *)
structure RBSet : RBSET = 

struct

  type key = int
  type 'a entry = key * 'a

 datatype 'a dict =
    Empty				(* considered black *)
  | Red of 'a entry * 'a dict * 'a dict
  | Black of 'a entry * 'a dict * 'a dict

  datatype 'a set = Set of (int * 'a dict)

  type 'a ordSet = 'a set ref

  fun isEmpty (Set(_, Empty)) = true
    | isEmpty (Set(_,T)) = false

  val empty = Set(0, Empty)
  
  fun singleton x = Set(1, Red(x, Empty, Empty))

  val compare = Int.compare
  (* Representation Invariants *)
  (*
     1. The tree is ordered: for every node Red((key1,datum1), left, right) or
        Black ((key1,datum1), left, right), every key in left is less than
        key1 and every key in right is greater than key1.

     2. The children of a red node are black (color invariant).

     3. Every path from the root to a leaf has the same number of
        black nodes, called the black height of the tree.
  *)

  local

  fun lookup (Set(n, dict)) key =
    let
      fun lk (Empty) = NONE
	| lk (Red tree) = lk' tree
        | lk (Black tree) = lk' tree
      and lk' ((key1, datum1), left, right) =
	    (case compare(key,key1)
	       of EQUAL => SOME(datum1)
	        | LESS => lk left
		| GREATER => lk right)
      in
	lk dict
      end

  fun last (Set(n, dict)) = (n, valOf (lookup (Set(n, dict)) n))

  (* val restore_right : 'a dict -> 'a dict *)
  (*
     restore_right (Black(e,l,r)) >=> dict
     where (1) Black(e,l,r) is ordered,
           (2) Black(e,l,r) has black height n,
	   (3) color invariant may be violated at the root of r:
               one of its children might be red.
     and dict is a re-balanced red/black tree (satisfying all invariants)
     and same black height n.
  *)
  fun restore_right (Black(e, Red lt, Red (rt as (_,Red _,_)))) =
         Red(e, Black lt, Black rt)	(* re-color *)
    | restore_right (Black(e, Red lt, Red (rt as (_,_,Red _)))) =
         Red(e, Black lt, Black rt)	(* re-color *)
    | restore_right (Black(e, l, Red(re, Red(rle, rll, rlr), rr))) =
	 (* l is black, deep rotate *)
	 Black(rle, Red(e, l, rll), Red(re, rlr, rr))
    | restore_right (Black(e, l, Red (re, rl, rr as Red _))) =
	 (* l is black, shallow rotate *)
	 Black(re, Red(e, l, rl), rr)
    | restore_right dict = dict

  (* restore_left is like restore_right, except *)
  (* the color invariant may be violated only at the root of left child *)
  fun restore_left (Black(e, Red (lt as (_,Red _,_)), Red rt)) =
	 Red(e, Black lt, Black rt)	(* re-color *)
    | restore_left (Black(e, Red (lt as (_,_,Red _)), Red rt)) =
	 Red(e, Black lt, Black rt)	(* re-color *)
    | restore_left (Black(e, Red(le, ll as Red _, lr), r)) =
	 (* r is black, shallow rotate *)
	 Black(le, ll, Red(e, lr, r))
    | restore_left (Black(e, Red(le, ll, Red(lre, lrl, lrr)), r)) =
	 (* r is black, deep rotate *)
	 Black(lre, Red(le, ll, lrl), Red(e, lrr, r))
    | restore_left dict = dict

  fun insert (Set(n, dict), entry as (key, datum)) = 
    let      
      val nItems = ref n
      (* val ins : 'a dict -> 'a dict  inserts entry *)
      (* ins (Red _) may violate color invariant at root *)
      (* ins (Black _) or ins (Empty) will be red/black tree *)
      (* ins preserves black height *)
      fun ins (Empty) = (nItems := n+1; Red(entry, Empty, Empty))
	| ins (Red(entry1 as (key1, datum1), left, right)) =
	  (case compare(key,key1)
	     of EQUAL => Red(entry, left, right)
	      | LESS => Red(entry1, ins left, right)
	      | GREATER => Red(entry1, left, ins right))
	| ins (Black(entry1 as (key1, datum1), left, right)) =
	  (case compare(key,key1)
	     of EQUAL => Black(entry, left, right)
	      | LESS => restore_left (Black(entry1, ins left, right))
	      | GREATER => restore_right (Black(entry1, left, ins right)))
      val dict' =  case ins dict
	            of Red (t as (_, Red _, _)) => Black t (* re-color *)
		  | Red (t as (_, _, Red _)) => Black t (* re-color *)
		  | dict => dict
    in
      Set(!nItems, dict')
    end


  fun insertList (S, nil) = S
    | insertList (S, e::list) = insertList (insert (S, e), list)


  fun insertLast (Set(n, dict), datum) = 
    let
      val Set(n', dic') =  insert (Set(n, dict), (n+1, datum))
    in 
      Set(n', dic')
    end 
  (* input: set sc
     output set s' *)


  fun insertShadow (Set(n, dict), entry as (key, datum)) =  
    let val oldEntry = ref NONE (* : 'a entry option ref *)
      fun ins (Empty) = Red(entry, Empty, Empty)
	| ins (Red(entry1 as (key1, datum1), left, right)) =
	(case compare(key,key1)
	   of EQUAL => (oldEntry := SOME(entry1);
			Red(entry, left, right))
	 | LESS => Red(entry1, ins left, right)
	 | GREATER => Red(entry1, left, ins right))
	| ins (Black(entry1 as (key1, datum1), left, right)) =
	   (case compare(key,key1)
	      of EQUAL => (oldEntry := SOME(entry1);
			   Black(entry, left, right))
	    | LESS => restore_left (Black(entry1, ins left, right))
	    | GREATER => restore_right (Black(entry1, left, ins right)))
      val (dict', oldEntry') = (oldEntry := NONE;
				((case ins dict
				    of Red (t as (_, Red _, _)) => Black t (* re-color *)
				  | Red (t as (_, _, Red _)) => Black t (* re-color *)
				  | dict => dict),
				    !oldEntry))
    in
      Set(n, dict')
    end


  (* doesn't apply f to all elements of S in order! *)
  fun app f (Set(n, dict)) =
      let fun ap (Empty) = ()
	    | ap (Red tree) = ap' tree
	    | ap (Black tree) = ap' tree
	  and ap' (entry1 as (_, datum), left, right) =
	      (ap left; f datum; ap right)
      in
	ap dict
      end

  fun update f (Set(n, dict)) =
      let fun upd (Empty) = Empty
	    | upd (Red tree) = Red(upd' tree)
	    | upd (Black tree) = Black(upd' tree)
	  and upd' (entry1 as (k, datum), left, right) =
	      let
		 val left' = upd left
		 val datum' = f datum
		 val right' =  upd right
	       in 
		 ((k, datum'), left', right')
	       end 
      in
	Set(n, upd dict)
      end

  fun forall (Set(n, dict)) f =
      let fun ap (Empty) = ()
	    | ap (Red tree) = ap' tree
	    | ap (Black tree) = ap' tree
	  and ap' (entry, left, right) =
	      (ap left; f entry; ap right)
      in
	ap dict
      end

  fun setsize (Set (n, _)) = n

  (* support for constructing red-black trees in linear time from increasing
   * ordered sequences (based on a description by R. Hinze).  Note that the
   * elements in the digits are ordered with the largest on the left, whereas
   * the elements of the trees are ordered with the largest on the right.
   *)
  (* functions for walking the tree while keeping a stack of parents
   * to be visited.
   *)
    fun next ((t as Red( _, _, b))::rest) = (t, left(b, rest))
      | next ((t as Black( _, _, b))::rest) = (t, left(b, rest))
      | next _ = (Empty, [])
    and left (Empty, rest) = rest
      | left (t as Red(_, a, _), rest) = left(a, t::rest)
      | left (t as Black(_, a, _), rest) = left(a, t::rest)
    fun start m = left(m, [])

    datatype 'a digit
      = ZERO
      | ONE of ('a entry * 'a dict * 'a digit)
      | TWO of ('a entry * 'a dict * 'a entry * 'a dict * 'a digit)
  (* add an item that is guaranteed to be larger than any in l *)
    fun addItem (a, l) = 
      let
	fun incr (a, t, ZERO) = ONE(a, t, ZERO)
	  | incr (a1, t1, ONE(a2, t2, r)) = TWO(a1, t1, a2, t2, r)
	  | incr (a1, t1, TWO(a2, t2, a3, t3, r)) =
	  ONE(a1, t1, incr(a2, Black (a3, t3, t2), r))
      in
	incr(a, Empty, l)
      end
  (* link the digits into a tree *)
    fun linkAll t = let
	  fun link (t, ZERO) = t
	    | link (t1, ONE(a, t2, r)) = link(Black (a, t2, t1), r)
	    | link (t, TWO(a1, t1, a2, t2, r)) =
		link(Black (a1, Red(a2, t2, t1),  t), r)
	  in
	    link (Empty, t)
	  end

    fun getEntry (Red (x, _, _)) = x
      | getEntry (Black (x, _, _)) = x

      
  (* return the union of the two sets *)
    fun union (Set (n1, s1), Set (n2, s2)) = 
      let
	fun ins ((Empty, _), n, result) = (n, result)
	  | ins ((Red (x, _, _), r), n, result) =
	    ins(next r, n+1, addItem(x, result))
	  | ins ((Black (x, _, _), r), n, result) =
	    ins(next r, n+1, addItem(x, result))
	  fun union' (t1, t2, n, result) = 
	    (case (next t1, next t2)
	       of ((Empty, _), (Empty, _)) => (n, result)
	        | ((Empty, _), t2) => ins(t2, n, result)
		| (t1, (Empty, _)) => ins(t1, n, result)
		| ((tree1, r1), (tree2, r2))  => 
		 let 
		   val e1 as (x, d1) = getEntry tree1
		   val e2 as (y, d2) = getEntry tree2
		 in 
		   case compare(x, y)
		     of LESS => union' (r1, t2, n+1, addItem(e1, result))
		      | EQUAL => union' (r1, r2, n+1, addItem(e1, result))
		      | GREATER => union' (t1, r2, n+1, addItem(e2, result))
		 end)
      in
	case s1 of 
	  Empty => Set(n2, s2)
	| _ => (case s2 of 
		  Empty => Set(n1, s1)
		| _ => let
			 val (n, result) = union' (start s1, start s2, 0, ZERO) 
		       in 
			 Set(n, linkAll result)
		       end)
      end

  (* return the intersection of the two sets *)
    fun intersection (Set(_, s1), Set(_, s2)) = 
      let
	fun intersect (t1, t2, n, result) = 
	  (case (next t1, next t2)
	     of ((Empty, r), (tree, r')) => (n, result)
	       | ((tree, r), (Empty, r')) => (n, result)
	       | ((tree1, r1), (tree2, r2)) => 
	       let
		 val e1 as (x, d1) = getEntry tree1
		 val e2 as (y, d2) = getEntry tree2
	       in 
		 case compare(x, y)
		   of LESS => intersect (r1, t2, n, result)
		 | EQUAL => intersect (r1, r2, n+1, addItem(e1, result))
		 | GREATER => intersect (t1, r2, n, result)
	       end)
	val (n, result) = intersect (start s1, start s2, 0, ZERO)
      in
	Set(n, linkAll result)
      end


  (* return the set difference  S1 - S2 
     if there are elements in S2 which do not appear in S1
     they are ignored !*)
    fun difference (Set(_, s1), Set(_, s2)) = 
      let
	fun ins ((Empty, _), n, result) = (n, result)
	  | ins ((Red (x, _, _), r), n, result) =
	    ins(next r, n+1, addItem(x, result)) 
	  | ins ((Black (x, _, _), r), n, result) =
	    ins(next r, n+1, addItem(x, result)) 
	fun diff (t1, t2, n, result) = 
	  (case (next t1, next t2)
	     of ((Empty, _), _) => (n, result)
	      | (t1, (Empty, _)) => ins(t1, n, result)
	      | ((tree1, r1), (tree2, r2)) => 
	       let
		 val e1 as (x, d1) = getEntry tree1
		 val e2 as (y, d2) = getEntry tree2
	       in 
		 case compare(x, y)
		   of LESS => diff (r1, t2, n+1, addItem(e1, result))
		    | EQUAL => diff (r1, r2, n, result)
		    | GREATER => diff (t1, r2, n, result)
	       end)
	val (n, result) = diff (start s1, start s2, 0, ZERO)
      in
	Set(n, linkAll result)
      end

    (* returns difference (d1, d2) where d1 
     contains all elements occurring in S1 but not in S2
     and d2 contains all elements occurring in S2 but not in S1
       *)
    fun difference2 (Set(_, s1), Set(_, s2)) = 
      let
	fun ins ((Empty, _), n, result) = (n, result)
	  | ins ((Red (x, _, _), r), n, result) =
	    ins(next r, n+1, addItem(x, result)) 
	  | ins ((Black (x, _, _), r), n, result) =
	    ins(next r, n+1, addItem(x, result)) 
	fun diff (t1, t2, (n1, result1), (n2, result2)) = 
	  (case (next t1, next t2)
	     of ((Empty, _), t2) => ((n1, result1), ins(t2, n2, result2))
	      | (t1, (Empty, _)) => (ins(t1, n1, result1), (n2, result2))
	      | ((tree1, r1), (tree2, r2)) => 
	       let
		 val e1 as (x, d1) = getEntry tree1
		 val e2 as (y, d2) = getEntry tree2
	       in 
		 case compare(x, y)
		   of LESS => diff (r1, t2, (n1+1, addItem(e1, result1)), (n2, result2))
		    | EQUAL => diff (r1, r2, (n1, result1), (n2, result2))
		    | GREATER => diff (t1, r2, (n1, result1), (n2+1, addItem(e2, result2)))
	       end)
	val ((n1, result1), (n2, result2)) = diff (start s1, start s2, (0, ZERO), (0, ZERO))
      in
	(Set(n1, linkAll result1), Set(n2, linkAll result2))
      end


   (* S1 - S2 = R1 
      S2 - S1 = R2
      intersection (S1, S2) requires 
      for all (x, d1) in S1 
        and (x, d2) in S2, d1 ~ d2
    *)

    fun diffMod F (Set(_, s1), Set(_, s2)) = 
     let
	fun ins ((Empty, _), n, result) = (n, result)
	  | ins ((Red (x, _, _), r), n, result) =
	    ins(next r, n+1, addItem(x, result)) 
	  | ins ((Black (x, _, _), r), n, result) =
	    ins(next r, n+1, addItem(x, result)) 
	fun diff (t1, t2, (n1, result1), (n2, result2)) = 
	  (case (next t1, next t2)
	     of ((Empty, _), t2) => ((n1, result1), ins(t2, n2, result2))
	      | (t1, (Empty, _)) => (ins(t1, n1, result1), (n2, result2))
	      | ((tree1, r1), (tree2, r2)) => 
	       let
		 val e1 as (x, d1) = getEntry tree1
		 val e2 as (y, d2) = getEntry tree2
	       in 
		 case compare(x, y)
		   of LESS => diff (r1, t2, (n1+1, addItem(e1, result1)), (n2, result2))
		    | EQUAL => ((F d1 d2) ; diff (r1, r2, (n1, result1), (n2, result2)))
		    | GREATER => diff (t1, r2, (n1, result1), (n2+1, addItem(e2, result2)))
	       end)
	val ((n1, result1), (n2, result2)) = diff (start s1, start s2, (0, ZERO), (0, ZERO))
      in
	(Set(n1, linkAll result1), Set(n2, linkAll result2))
      end


    fun splitSets F (Set(_, s1), Set(_, s2)) = 
     let
	fun ins ((Empty, _), n, result) = (n, result)
	  | ins ((Red (x, _, _), r), n, result) =
	    ins(next r, n+1, addItem(x, result)) 
	  | ins ((Black (x, _, _), r), n, result) =
	    ins(next r, n+1, addItem(x, result)) 
	fun split (t1, t2, nr as (n, result), nr1 as (n1, result1), nr2 as (n2, result2)) = 
	  (case (next t1, next t2)
	     of ((Empty, _), t2) => (nr, nr1, ins(t2, n2, result2))
	      | (t1, (Empty, _)) => (nr, ins(t1, n1, result1), nr2)
	      | ((tree1, r1), (tree2, r2)) => 
	       let
		 val e1 as (x, d1) = getEntry tree1
		 val e2 as (y, d2) = getEntry tree2
	       in 
		 case compare(x, y)
		   of LESS => split (r1, t2, nr, (n1+1, addItem(e1, result1)), nr2)
		    | EQUAL => (case (F d1 d2) 
				  of NONE => split (r1, r2, nr, (n1+1, addItem(e1, result1)), 
						   (n2+1, addItem(e2, result2)))
		                   | SOME(d) => split (r1, r2, (n+1, addItem((x, d), result)), nr1, nr2))
		    | GREATER => split (t1, r2, nr, nr1, (n2+1, addItem(e2, result2)))
	       end)
	val ((n, r), (n1, r1), (n2, r2)) = split (start s1, start s2, (0, ZERO), (0, ZERO), (0, ZERO))
      in
	(Set(n, linkAll r), Set(n1, linkAll r1), Set(n2, linkAll r2))
      end

  in
    fun new () = ref (empty) (* ignore size hint *)
    fun copy S = let val S' = new() in S' := (!S); S' end
    val insert = (fn set => fn entry => (set := insert (!set, entry)))
    val insertLast = (fn set => fn datum => (set := insertLast (!set, datum)))
    val insertList = (fn set => fn list => (set := insertList (!set, list)))
    val insertShadow = (fn set => fn entry => (set := insertShadow (!set, entry)))

    val isEmpty = (fn ordSet => isEmpty (!ordSet))
    val last = (fn ordSet => last (!ordSet))

    
    val lookup = (fn ordSet => fn key => lookup (!ordSet) key)

    val clear = (fn ordSet => (ordSet := empty))

    val app = (fn ordSet => fn f => app f (!ordSet))
    val update = (fn ordSet => fn f => ((ordSet := (update f (!ordSet)); ordSet)))
    val forall = (fn ordSet => fn f => forall (!ordSet) f)

    fun size S = setsize (!S) 

    val difference = (fn set1 => fn set2 => (let val set = new() in set := difference (!set1, !set2); set end))

    val difference2 = (fn set1 => fn set2 => (let val r1 = new()
					      val r2 = new() 
					      val (rset1, rset2) = difference2 (!set1, !set2)
					      in r1 := rset1; r2:= rset2 ;
					      (r1, r2) end))


    val differenceModulo = (fn set1 => fn set2 => fn F => 
			    (let val r1 = new()
				 val r2 = new() 
				 val (rset1, rset2) = diffMod F (!set1, !set2)
			     in r1 := rset1; r2:= rset2 ;
			       (r1, r2) end))


    val splitSets = (fn set1 => fn set2 => fn F => 
		    (let val r1 = new()
			 val r2 = new() 
			 val r = new() 
			 val (rset, rset1, rset2) = splitSets F (!set1, !set2)
		     in r:= rset; r1 := rset1; r2:= rset2 ;
		       (r, r1, r2) 
		     end))

    val intersection = (fn set1 => fn set2 => (let val set = new() in set := intersection (!set1, !set2); set end))
    val union = (fn set1 => fn set2 => (let val set = new() in set := union (!set1, !set2); set end))

(*  
    val e1 : string entry = (1, "a")
    val e2 : string entry = (2, "b")
    val e3 : string entry = (3, "c")
    val e4 : string entry = (4, "d")
    val e5 : string entry = (5, "e")
    val e6 : string entry = (6, "f")


   val f3 : string entry = (3, "c")
   val f4 : string entry = (4, "d")
   val f5 : string entry = (5, "e")
   val f7 : string entry = (7, "g")
 
    val S : string ordSet = insertList (new()) [e1, e2, e3, e4, e5, e6] 
*)
  end
end;  (* functor RedBlackSet *)

