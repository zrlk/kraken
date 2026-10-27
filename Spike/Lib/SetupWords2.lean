/-
**The setup words of an `Accepted2` program's lowering** (ISA-generic):
with a setup block, the words `lowerWithMarks` passes `mainThreadF`
(`setupWords2`) are the value words of the setup block `rodata`'s result
type (`valWords_setupWords2`).
-/
import Spike.Lib.LowerProgC2Core

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc Scc.IR

/-- **`setupWords2` at a setup block**: the value words of `rodata`'s result
type, when it has some. -/
theorem valWords_setupWords2 {p : Prog} (hs : (Lower.setupOf p).isSome = true) {r : Decl}
    (hr : p.find? (·.name == "rodata") = some r) (hv : (Obj.valWords r.retTy).isSome = true) :
    Obj.valWords r.retTy = some (setupWords2 p) := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hv
  simp [setupWords2, hs, hr, hn]

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.valWords_setupWords2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms valWords_setupWords2

end Spike.Lib.LowerNode
