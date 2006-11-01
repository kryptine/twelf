signature PLANNER = 
sig

(* LF Families *)
type A 
type M

type Embed
type Plan

val embed : A -> A -> Embed option

val plan : string -> Plan

end 