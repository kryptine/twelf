(* Weak head-normal forms for simple syntax *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)
(* Modified: Kevin Watkins *)

signature SIMPWHNF =
sig

  structure SimpSyn : SIMPSYN

  (* Patterns *)
  val isPatSub : SimpSyn.Sub -> bool

  (* Weak head normalization *)
  val whnf : SimpSyn.eclo -> SimpSyn.eclo
  val expandDef : SimpSyn.eclo -> SimpSyn.eclo

  (* Full normalization *)
  val normalize: SimpSyn.eclo -> SimpSyn.Exp

  (* Inverting substitutions *)
  val invert : SimpSyn.Sub -> SimpSyn.Sub
  val isId : SimpSyn.Sub -> bool

end
