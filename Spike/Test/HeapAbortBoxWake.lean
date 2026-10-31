/-
**`HeapReadyBox` at `hello.w`'s box, from the program itself**
(`WakeT1.wakeSrc`): `main`'s body is `let z = zero[Int] in mZ` with `mZ = let
o = new z in …` (`SpawnViewLtSteps.main_decl`, by `rfl`); the `zero` step
binds `z` at `Int` to the word `0`; at the control it lands in, the `new` is
`HeapReadyBox` at every heap use that the box's two units carry past the
cells from within them. So the box arm of the heap abort's obligation is
satisfiable at the program's actual allocation.
-/
import Spike.Lib.HeapAbortBox
import Spike.Lib.SpawnViewLtSteps

namespace Spike.Test.HeapAbortBoxWake

open CoreLang CoreTerm TermRun
open Spike.Lib Spike.Lib.SpawnViewLtSteps
open Spike.Lib.WakeT1 (wakeSrc)

/-- `main`'s body in `wakeSrc` is `let z = zero[Int] in mZ`, `mZ` the box allocation. -/
theorem main_box : (wakeSrc.find? (·.name == "main")).map (·.body) = some (.let_ "z" (.zero .int) mZ) ∧
    mZ = .let_ "o" (.new (.var "z") (some .int)) mO := ⟨main_find, rfl⟩

/-- `zero[Int]` (no type arguments) binds the word `0` at `Int`, in one step. -/
theorem zero_int (g : G) (env : Env) (s : St) : evalOp g env [] s (.zero .int) = [(s, .int, [cst (.num 0)])] := by
  have hz : zeroWords .int = some [.num 0] := by unfold zeroWords; rfl
  simp [evalOp, close, ol, substTs, hz]

/-- **The box at `mZ` is `HeapReadyBox`** after the `zero` step, at every
overflowing heap use. -/
theorem mZ_heapReadyBox {cells old : Nat} {env : Env} {h : Option (Nat × Word)} (hle : old ≤ cells)
    (hlt : cells < old + 2) : HeapReadyBox cells old ⟨mZ, ("z", .int, [cst (.num 0)]) :: env, h⟩ :=
  ⟨"o", .var "z", mO, .int, cst (.num 0), ⟨_, rfl⟩, by simp [evalAt, lookupE], rfl, hle, hlt⟩

end Spike.Test.HeapAbortBoxWake
