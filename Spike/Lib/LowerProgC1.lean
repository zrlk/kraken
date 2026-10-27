/-
**`lowerAll`'s IR on an `Accepted1` program** (AArch64): the ISA-free
statements are in `Spike/Lib/LowerProgC1Core.lean` (`lowerIR_accepted1`,
`Pairwise2`, `funcs1`, `mem_progOf_funcs1`, `find_index`, ...).

- `lowerAll_accepted1_a64`: `lowerAll`'s IR (AArch64).
-/
import Spike.Lib.LowerProgC1Core
import Scc.Lower.InvA64

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc Scc.IR
open Scc.Lower
open Scc.Lower.Inv

/-- **`lowerAll`'s IR on an `Accepted1` program** (AArch64), when the
lowering and emission succeed: the runtime functions, then `funcs1`, each
code block's closed form without the depth counter. -/
theorem lowerAll_accepted1_a64 (cfg : Config) {p : Prog} (hp : Accepted1 p = true)
    {e : Scc.Lower.A64.Emitted} (h : Scc.Lower.A64.lowerAll? cfg p = .ok e) :
    ∃ rs rt, Pairwise2 (LowC p cfg.layout.obj none) p rs ∧
      rtFuncs cfg.layout ⟨.unit, true⟩ 0 = .ok rt ∧
      (Scc.Lower.A64.lowerAll cfg p).low.ir = progOf cfg.layout rt (funcs1 p rs) ∧
      (Scc.Lower.A64.lowerAll cfg p).low.marks = marksAll1 p rs := by
  obtain ⟨rs, rt, hrs, hrt, hir, hm⟩ := lowerIR_accepted1 cfg hp (Scc.Lower.InvA64.lowerAll?_low_a64 h)
  refine ⟨rs, rt, hrs, hrt, ?_, ?_⟩ <;> simp only [Scc.Lower.A64.lowerAll, h]
  · exact hir
  · exact hm

end Spike.Lib.LowerNode
