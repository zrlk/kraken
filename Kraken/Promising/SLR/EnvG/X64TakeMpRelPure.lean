/-
**Part 6: the x64 writing reader makes only
release writes** (`EnvG/X64MpRelPure.lean` for `takeReaderX`).

Under `Arch.tso` the reader's `movl $43, (%rsi)` is a release store, so in
the all-release environment `(relPureQ Arch.tso (fun _ _ => False)).within
[(f, 4), (d, 4)]` every write is permitted; one specification per thread
then gives the scope `NTFree Arch.tso` and purity for any ghost at once
(`final_of_relPureSafelyQX_tsoS`, `EnvG/TakeX64Final.lean`). A take never
changes the release predicates, so no take-specific purity is needed.

- `takeReaderX_noNT`: `cfgEnv_partial` on the counted all-release
  environment, the table at `spin` being the frame.
-/
import Kraken.Promising.SLR.EnvG.X64MpRelPure
import Kraken.Promising.SLR.EnvG.X64TakeMp

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike Kraken.Promising.X64.EnvG

namespace Kraken.Promising.X64.EnvG.TakeMp

open Kraken.Promising.X64.EnvG.MpRelPure

set_option mvcgen.warning false
set_option experimental.vcgen true

variable [layout : _root_.Layout] [Executable.ValidLayout (layout takeReaderX)]

local instance takeReaderX.envNT : CodeEnv := ⟨layout takeReaderX⟩

/-- The reader's table: at `spin`, `rdi = f`, `rsi = d`, neither word in
`dmem`. -/
abbrev readerTableNX (f d : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (EnvR f d)).State → Prop :=
  fun lb s _ => lb = "spin" → s.regs.get64 .rdi = f ∧ s.regs.get64 .rsi = d ∧ Mem.loadInt s.dmem f 4 = none ∧
    Mem.loadInt s.dmem d 4 = none

/-- **The x64 writing reader makes only release writes**; counted, partial. -/
theorem takeReaderX_noNT (f d : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (EnvR f d))
      (fun s _ => s.regs.get64 .rdi = f ∧ s.regs.get64 .rsi = d ∧ Mem.loadInt s.dmem f 4 = none ∧
        Mem.loadInt s.dmem d 4 = none)
      takeReaderX (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (readerTableNX f d) (hP := by funext s g; simp [readerTableNX])
  cfg_cases_env [takeReaderX]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  case vc2 x σ1 hld _ _ =>
    -- the back edge: the frame again; the counter moved
    obtain ⟨hx0, hx1, hdf, hdd⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, -⟩
    · simp [hx0, hdf] at hm
    · refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simp [hx0], by simp [hx1], by simpa using hdf,
        by simpa using hdd⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      have hn := hst.2
      subst hg
      simp [SharedAccess.tick] at hn
  all_goals simp_all
  all_goals try exact fun h => h rfl
  all_goals trivial

end Kraken.Promising.X64.EnvG.TakeMp

#print axioms Kraken.Promising.X64.EnvG.TakeMp.takeReaderX_noNT
