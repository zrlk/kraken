/-
**`hello1`'s landing premises at the program** (x86-64; the twin of
`Spike/Test/A64Hello1H1Of.lean`):

- `hello1_hTn`: every allocation of every compiled block of `hello1o` has
  an element type taking a word (`elem2`), at the blocks in range
  (`H1OpenX.hTn`'s guarded shape, at `T j := TailAt2 hello1o j`).
-/
import Spike.Test.X64Hello1HsOf

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Spike.Lib.LowerNode (compiled2 TailAt2)

/-- The program. -/
local notation "P1X" => Spike.Test.Hello1MainSrc.hello1o

/-- **`hello1o`'s allocations take a word per element** at every compiled
block in range (`tailsL` of each block's body decided, as
`hello1_rodata_elem2` at every block). -/
theorem hello1_hTn : ∀ j d, (compiled2 P1X)[j]? = some d →
    ∀ x cn τ e, TailAt2 P1X j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true := by
  have hc : ∀ d ∈ compiled2 P1X, (tailsL d.body).all (fun t => match t with
      | .let_ _ (.newBuf _ τ) _ => Scc.Lower.elem2 τ
      | _ => true) = true := by
    decide
  intro j d hd x cn τ e ht
  simpa using List.all_eq_true.mp (hc d (List.mem_of_getElem? hd)) _ (tailOf_mem_tailsL (ht d hd))

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_hTn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_hTn
