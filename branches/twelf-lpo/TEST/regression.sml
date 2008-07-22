(* Regression test *)
(* Requires three functions:
 * test : file -> Twelf.Status - runs in safe mode, expects success
 * testUnsafe : file -> Twelf.Status - runs in unsafe mode, expects success
 * conclude : unit -> unit - provided in case of any necessary cleanup *)

(* Examples, part of the distribution *)
(* test "examples/arith/test.cfg"; *)
test "examples/ccc/test.cfg";
test "examples/church-rosser/test.cfg";
test "examples/compile/cls/test.cfg";
test "examples/compile/cpm/test.cfg";
test "examples/compile/cps/test.cfg";
test "examples/compile/cxm/test.cfg";
test "examples/compile/debruijn/test.cfg";
test "examples/compile/debruijn1/test.cfg";
test "examples/cpsocc/test.cfg";
test "examples/cut-elim/test.cfg";
test "examples/fol/test.cfg";
test "examples/guide/test.cfg";
test "examples/handbook/test.cfg";
test "examples/incll/test.cfg";
test "examples/kolm/test.cfg";
testUnsafe "examples/lp/test.cfg";
test "examples/lp-horn/test.cfg";
test "examples/mini-ml/test.cfg";
test "examples/polylam/test.cfg";
test "examples/prop-calc/test.cfg";

(* CLP Examples, part of the distribution *)
test "examples-clp/arith/test.cfg";
test "examples-clp/base/test.cfg";
test "examples-clp/crypt/test.cfg";
test "examples-clp/integers/test.cfg";
test "examples-clp/laplace/test.cfg";
test "examples-clp/lists/test.cfg";
test "examples-clp/mortgage/test.cfg";
test "examples-clp/pelletier/test.cfg";
test "examples-clp/sieve/test.cfg";

(* Exercises, not part of the distribution *)
(*test "exercises/units/test.cfg";
test "exercises/opt-eval/test.cfg";
*)


conclude ();
