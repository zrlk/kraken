/-
**x64 MP: no non-temporal store, and purity, by `vcgen`**: each x64 MP
thread in `(relPureQ Arch.tso (fun _ _ => False)).within [(f, 4), (d, 4)]`
(every write a release), by one `vcgen` call. Through
`final_of_relPureSafelyQX_tso` (`EnvG/RelPureEnvX64.lean`) this gives both
the scope `NTFree Arch.tso` and the purity hypotheses of `final_of_relWrites`.

- `mpWriterX_noNT`: both `mov` stores are releases under `Arch.tso`.
- `mpReaderX_noNT`: the reader writes nothing (`cfgEnv_partial`, counted).
-/
import Kraken.Promising.SLR.EnvG.RelPureEnvX64
import Kraken.Promising.SLR.EnvG.X64MpVCGen

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike Kraken.Promising.X64.EnvG

namespace Kraken.Promising.X64.EnvG.MpRelPure

open Kraken.Promising.X64.EnvG.MpSmoke

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The all-release environment on the MP layout. -/
abbrev EnvR (f d : BitVec 64) : SharedEnv :=
  (SharedEnv.relPureQ Arch.tso fun _ _ => False).within [(f, 4), (d, 4)]

variable [layout : _root_.Layout]

section Writer

local instance mpWriterX.env : CodeEnv := ⟨layout mpWriterX⟩

/-- **The x64 MP writer makes only release writes** (under `Arch.tso`). -/
theorem mpWriterX_noNT (f d : BitVec 64) :
    TripleEnv (EnvR f d)
      (fun s _ => s.regs.get64 .rdi = f ∧ s.regs.get64 .rsi = d)
      mpWriterX (fun _ _ => True) (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold mpWriterX
  vcgen
  all_goals simp_all
  all_goals exact fun h => h rfl

end Writer

section Reader

variable [Executable.ValidLayout (layout mpReaderX)]

local instance mpReaderX.env : CodeEnv := ⟨layout mpReaderX⟩

/-- The reader's table: at `spin`, `rdi = f` (the flag load is in the
layout). -/
abbrev readerTable (f d : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (EnvR f d)).State → Prop :=
  fun lb s _ => lb = "spin" → s.regs.get64 .rdi = f ∧ s.regs.get64 .rsi = d ∧ Mem.loadInt s.dmem f 4 = none

/-- **The x64 MP reader writes nothing**; counted, partial. -/
theorem mpReaderX_noNT (f d : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (EnvR f d))
      (fun s _ => s.regs.get64 .rdi = f ∧ s.regs.get64 .rsi = d ∧ Mem.loadInt s.dmem f 4 = none)
      mpReaderX (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (readerTable f d) (hP := by funext s g; simp [readerTable])
  cfg_cases_env [mpReaderX]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  case vc2 x σ1 hld _ _ =>
    obtain ⟨hx0, hx1, hdf⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, rfl⟩
    · simp [hx0, hdf] at hm
    · refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simp [hx0], by simp [hx1], by simpa using hdf⟩,
        .inr fun ⟨_, hg⟩ => ?_⟩
      have hn := hst.2
      subst hg
      simp [SharedAccess.tick] at hn
  all_goals simp_all
  all_goals trivial

end Reader

end Kraken.Promising.X64.EnvG.MpRelPure
