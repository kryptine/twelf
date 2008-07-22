(* Termination checking based on LPOs *)
(* Author: Jeffrey Sarnat, Carsten Schuermann *)

structure Lpo =
struct
  exception Error of string

  local
    val maxDrop = Global.maxCid
    val dropArray = Array.array (maxDrop+1, (0, 0))
      : (int * int) Array.array
    val nextDrop = ref (0)
      
  in

    fun installDrop (c1, c2) = 
        let
	  val i = !nextDrop
	in
	  if i > maxDrop
	    then raise Error ("Drop signature size " ^ Int.toString (maxDrop+1) ^ " exceeded")
	  else (Array.update (dropArray, i, (c1, c2)) ;
		nextDrop := i + 1)
	end

    fun printDrops () =
        Array.foldl (fn ((c1, c2), ()) => 
		     (print "("; print (Int.toString c1); print ",";
		      print (Int.toString c2); print ")\n")) () dropArray
  end
end