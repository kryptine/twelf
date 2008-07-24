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


    structure P = Precedence
      
    fun installDrop (c1, c2) = 
        let
	  val i = !nextDrop
	in
	  if i > maxDrop
	    then raise Error ("Drop signature size " ^ Int.toString (maxDrop+1) ^ " exceeded")
	  else (Array.update (dropArray, i, (c1, c2)) ;
		nextDrop := i + 1)
	end

    (* Invariant :  c1, c2 object level constants *)
    fun installOrder (c1, c2) = P.addSubord (c1, c2)

  in
    val installDrop = installDrop
    val installOrder = installOrder
  end
end