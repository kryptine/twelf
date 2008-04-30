open Twelf
val pref = "./examples/module-test/directive-unit-tests/"
fun loadFile' s = loadFile (pref^s)
fun testPlain str =
	let
	val _ = reset ()
	val _ = unsafe := true
	val _ = loadFile' "natplus.elf"
	val _ = loadFile' str
	in ()
	end

fun testModOpenNat str =
	let
	val _ = reset ()
	val _ = unsafe := true
	val _ = loadFile' "natplus-module-open-nat.elf"
	val _ = loadFile' str
	in ()
	end

fun testModRedec str =
	let
	val _ = reset ()
	val _ = unsafe := true
	val _ = loadFile' "natplus-module-redec.elf"
	val _ = loadFile' str
	in ()
	end

fun testModInc str =
	let
	val _ = reset ()
	val _ = unsafe := true
	val _ = loadFile' "natplus-module-include.elf"
	val _ = loadFile' str
	in ()
	end
val testModInclude = testModInc

fun testModOpenAll str =
	let
	val _ = reset ()
	val _ = unsafe := true
	val _ = loadFile' "natplus-module-open-all.elf"
	val _ = loadFile' str
	in ()
	end

