/-
**Non-vacuity of the x86-64 wake load's parsed form**: at
wake's generated listing (`SccCode.wakeAsm`, `Spike/Lib/X64WakeCode.lean`)
the premises `Spike.Lib.X64WakePreAsm.wake_init` and
`Spike.Lib.X64WakeLoadT.wake_initT` take of the load are met.

- `wake_wideC`: `wideIn (wakeCells.map (·.1))` (`SccCode.wake_wide`,
  `decide +kernel`).
- `wake_clear`: the Linux entry state is clear at `wakeΛ` (`decide +kernel`).
- `wake_loadParsed`: `loadParsed … wakeCells wakeSecs wakeAsm.labelOffs` is
  `some` at `wakeΛ` (`loadParsed_of_loadOk` from `SccCode.wakeΛ_load`).
- `wake_parsed`: `cellsOf wakeAsm = some wakeCells` and
  `dataSections wakeAsm.text = some wakeSecs`, **given** `parsesTo`. The
  kernel cannot run the parsers, so this equation is the generated file's
  trust boundary, checked by evaluation there (`#guard parsesTo wakeAsm
  wakeCells wakeSecs`) and here again; AArch64's `textProgram asm = .ok prog`
  premise is the same boundary.
-/
import Spike.Lib.X64WakeCode

namespace Spike.Lib.X64WakeLoadChk

open Scc.Sem Scc.Sem.X64

/-- The listing's cells are one-word (`wake_wide`). -/
theorem wake_wideC : Scc.Cert.WideX64.wideIn (SccCode.wakeCells.map (·.1)) = true := SccCode.wake_wide

/-- The Linux entry state is clear at `wakeΛ`. -/
theorem wake_clear : Entry.linux.clear SccCode.wakeΛ = true := by decide +kernel

/-- **The parsed load is defined** at `wakeΛ`, the listing's label offsets. -/
theorem wake_loadParsed (H : Hooks Kraken.Promising.X64.isa) :
    ∃ t, loadParsed H Entry.linux SccCode.wakeΛ SccCode.wakeCells SccCode.wakeSecs SccCode.wakeAsm.labelOffs =
      some t :=
  ⟨_, Scc.Cert.Link.X64.loadParsed_of_loadOk SccCode.wakeΛ_load wake_clear⟩

/-- **The parse equations** from the trust boundary's `parsesTo`. -/
theorem wake_parsed (h : Scc.Cert.Link.X64.parsesTo SccCode.wakeAsm SccCode.wakeCells SccCode.wakeSecs = true) :
    cellsOf SccCode.wakeAsm = some SccCode.wakeCells ∧ dataSections SccCode.wakeAsm.text = some SccCode.wakeSecs :=
  Scc.Cert.Link.X64.parsed_of_parsesTo h

-- The boundary holds by evaluation.
#guard Scc.Cert.Link.X64.parsesTo SccCode.wakeAsm SccCode.wakeCells SccCode.wakeSecs

end Spike.Lib.X64WakeLoadChk

/-- info: 'Spike.Lib.X64WakeLoadChk.wake_wideC' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeLoadChk.wake_wideC

/-- info: 'Spike.Lib.X64WakeLoadChk.wake_clear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeLoadChk.wake_clear

/-- info: 'Spike.Lib.X64WakeLoadChk.wake_loadParsed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeLoadChk.wake_loadParsed

/-- info: 'Spike.Lib.X64WakeLoadChk.wake_parsed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeLoadChk.wake_parsed
