/-
**The counter's item in the lowering's data sections** (ISA-free): the IR
of every successful lowering carries the runtime's data (`Runtime.data`).
Its first datum is `scc_rt_heap_use`, a zero-initialised word, so the
emitted `.bss` (`Secs.ofProgram`) labels the counter with an all-zero item
of 8 bytes.

- `lowerWithMarks_data`, `lowerIR_data`: a successful lowering's data is
  `Runtime.data` at the configuration's layout;
- `ctr_secs`: `Secs.ofProgram (Runtime.data lay) maps` gives
  `scc_rt_heap_use` an all-zero item of at least a word in `.bss ++ .data`,
  for every layout and stack-map table.

The ISA modules `Spike/Lib/Rt/A64CtrZOfEmitted.lean` and
`Spike/Lib/Rt/X64CtrZOfEmitted.lean` derive the `CtrZ` fact of an emitted
output from these two, through that ISA's `emitAll`.
-/
import Scc.Lower.Spec
import Scc.Emit.Data
import Scc.Cert.PlaceOK
import Scc.Cert.LinkImage

namespace Spike.Lib.Rt

open Kraken.DataImage
open Scc.Cert.PlaceOK (heapUseSym)
open Scc.Cert.Link (symItems allZero itemLen isEnd)

/-- **A successful lowering's data is the runtime's** (`lowerWithMarks`). -/
theorem lowerWithMarks_data {cfg : Scc.Config} {c : Scc.Frontend.Checked}
    {x : Scc.IR.Program × List (Scc.IR.Sym × Array (Scc.Lower.Node × Scc.Lower.Point))}
    (h : Scc.Lower.lowerWithMarks cfg c = .ok x) : x.1.data = Scc.Lower.Runtime.data cfg.layout := by
  unfold Scc.Lower.lowerWithMarks at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals (first | (cases h; rfl) | cases h)

/-- **A successful lowering's IR data is the runtime's** (`lowerIR`). -/
theorem lowerIR_data {cfg : Scc.Config} {p : CoreTerm.Prog} {l : Scc.Lower.Lowered}
    (h : Scc.Lower.lowerIR cfg p = .ok l) : l.ir.data = Scc.Lower.Runtime.data cfg.layout := by
  unfold Scc.Lower.lowerIR at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hw
  cases h
  exact lowerWithMarks_data hw

/-- **The runtime's data sections give the counter a zeroed word**: in
`Secs.ofProgram (Runtime.data lay) maps`, `scc_rt_heap_use` labels the
item `[.zero 8]` in `.bss`. -/
theorem ctr_secs (lay : Scc.Layout) (maps : Option (List (String × List Int × List Int))) :
    ∃ its, (heapUseSym, its) ∈ symItems ((Scc.Emit.Data.Secs.ofProgram (Scc.Lower.Runtime.data lay) maps).bss ++
      (Scc.Emit.Data.Secs.ofProgram (Scc.Lower.Runtime.data lay) maps).data) ∧
      allZero its = true ∧ 8 ≤ itemLen its := by
  refine ⟨[.zero 8], ?_, rfl, by decide⟩
  simp [Scc.Emit.Data.Secs.ofProgram, Scc.Lower.Runtime.data, Scc.Emit.Data.datumItems, symItems, isEnd,
    heapUseSym, Scc.Lower.Names.heapUse]

end Spike.Lib.Rt
