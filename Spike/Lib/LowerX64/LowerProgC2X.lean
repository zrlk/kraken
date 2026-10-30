/-
**`lowerAll`'s IR on an `Accepted2` program** (x86-64): the ISA-free
statements are in `Spike/Lib/LowerProgC2Core.lean` (`lowerIR_accepted2`,
`compiled2`, `funcs2`, `marksAll2`, `mem_progOf_funcs2`, ...).

- `lowerAll_accepted2_x64`: `lowerAll`'s checked program and IR (x86-64).
-/
import Spike.Lib.LowerProgC2Core
import Scc.Lower.InvX64

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc Scc.IR
open Scc.Lower
open Scc.Lower.Inv
open Spike.Lib.LowerShape

/-- **`lowerAll`'s IR on an `Accepted2` program** (x86-64), when the
lowering and emission succeed: the checked program `checked2 p`, the runtime
functions, then `funcs2`, each compiled block's closed form `lowerC2`. -/
theorem lowerAll_accepted2_x64 (cfg : Config) {p : Prog} (hp : Accepted2 p = true)
    {e : Scc.Lower.X64.Emitted} (h : Scc.Lower.X64.lowerAll? cfg p = .ok e) :
    ∃ ws rt, Pairwise2 (LowC2 p cfg.layout.obj) (compiled2 p) ws ∧
      rtFuncs cfg.arch cfg.layout (entry2 p) (setupWords2 p) = .ok rt ∧
      (Scc.Lower.X64.lowerAll cfg p).low.checked = checked2 p ∧
      (Scc.Lower.X64.lowerAll cfg p).low.ir = progOf cfg.layout rt (funcs2 p ws) ∧
      (Scc.Lower.X64.lowerAll cfg p).low.marks = marksAll2 p ws := by
  obtain ⟨ws, rt, hws, hrt, hc, hir, hm⟩ := lowerIR_accepted2 cfg hp (Scc.Lower.InvX64.lowerAll?_low_x64 h)
  refine ⟨ws, rt, hws, hrt, ?_, ?_, ?_⟩ <;> simp only [Scc.Lower.X64.lowerAll, h]
  · exact hc
  · exact hir
  · exact hm

end Spike.Lib.LowerNode
