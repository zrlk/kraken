/-
**Checks of `Spike/Lib/Hello1oRuns.lean`**: concrete terms of `hello1o`'s
runs found among `hello1oTerms` by `simp` (the setup block's start, `printL`'s
element load and byte advance, `print`'s call into `printL`, `main`'s call of
`print`), the check `hello1o_ok`, and the axioms of the library's lemmas.
-/
import Spike.Lib.Hello1oRuns

namespace Spike.Test.Hello1oRuns

open CoreLang CoreTerm
open Spike.Lib.Hello1oRuns Spike.Lib.PrintSrc
open Spike.Lib.Hello1Runs (setupStartTerm)
open Spike.Test.Hello1MainSrc (hello1o)

example : setupStartTerm ∈ hello1oTerms := by simp [hello1oTerms]

example : printLoad ∈ hello1oTerms := by
  simp [hello1oTerms, sufs, hello1o, printLD, printLBody, printLoad]

example : printNext ∈ hello1oTerms := by
  simp [hello1oTerms, sufs, hello1o, printLD, printLBody, printLoad, printLane, printEmit]

example : .tail "printL" ["z", "mn"] (.var "a1") [] ∈ hello1oTerms := by
  simp [hello1oTerms, sufs, hello1o, printD, printBody]

example : (.ret (.lit 0) : Expr) ∈ hello1oTerms := by
  simp [hello1oTerms, sufs, hello1o, Spike.Lib.Hello1Src.hello1Src]

/-- `hello1o`'s `printL` reads its slot by `loadAt`, which `goodB` accepts. -/
example : goodB printLoad = true := rfl

/-- A `load` fails the check. -/
example : goodB (.let_ "x" (.load true (.var "a")) (.ret .unit)) = false := rfl

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.Hello1oRuns.hello1o_ok' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms hello1o_ok

/--
info: 'Spike.Lib.Hello1oRuns.good1Ho_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms good1Ho_run

/--
info: 'Spike.Lib.Hello1oRuns.Good1Ho.newBuf_ty' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Good1Ho.newBuf_ty

/--
info: 'Spike.Lib.Hello1oRuns.good1Ho_of_mem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms good1Ho_of_mem

end Spike.Test.Hello1oRuns
