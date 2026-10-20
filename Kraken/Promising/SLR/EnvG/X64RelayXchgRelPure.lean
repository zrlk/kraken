/-
**Part 5: the x64 relay makes only release
writes** (`EnvG/X64TakeMpRelPure.lean` / `EnvG/X64SpinRelPure.lean` for
`relayX`).

Under `Arch.tso` the relay's `movl $43, (%rsi)` is a release store and its
`xchgl` an `.acqRel` RMW, so in the all-release environment
`(relPureQ Arch.tso (fun _ _ => False)).within (relayS rp)` every write is
permitted; one specification per thread then gives the scope
`NTFree Arch.tso` and purity for any ghost at once
(`final_of_relPureSafelyQX_tsoS`, `EnvG/TakeX64Final.lean`).

- `relayX_noNT`: `cfgEnv_partial` on the counted all-release environment,
  the table at `spin` being the frame.
-/
import Kraken.Promising.SLR.EnvG.X64MpRelPure
import Kraken.Promising.SLR.EnvG.X64RelayXchgVCGen

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike Kraken.Promising.X64.EnvG

namespace Kraken.Promising.X64.EnvG.RelayX

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The all-release environment on the relay's layout. -/
abbrev EnvRY (f1 d f2 : BitVec 64) : SharedEnv :=
  (SharedEnv.relPureQ Arch.tso fun _ _ => False).within [(f1, 4), (d, 4), (f2, 4)]

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relayX)]

local instance relayX.envNT : CodeEnv := ⟨layout relayX⟩

/-- The relay's frame on explicit addresses. -/
abbrev FrameY (f1 d f2 : BitVec 64) (s : MachineData) : Prop :=
  s.regs.get64 .rdi = f1 ∧ s.regs.get64 .rsi = d ∧ s.regs.get64 .rdx = f2 ∧
    Mem.loadInt s.dmem f1 4 = none ∧ Mem.loadInt s.dmem d 4 = none ∧ Mem.loadInt s.dmem f2 4 = none

/-- The relay's purity table: the frame at `spin`. -/
abbrev relayTableNX (f1 d f2 : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (EnvRY f1 d f2)).State → Prop :=
  fun lb s _ => lb = "spin" → FrameY f1 d f2 s

/-- **The x64 relay makes only release writes**; counted, partial. -/
theorem relayX_noNT (f1 d f2 : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (EnvRY f1 d f2)) (fun s _ => FrameY f1 d f2 s) relayX
      (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (relayTableNX f1 d f2) (hP := by funext s g; simp [relayTableNX])
  cfg_cases_env [relayX]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  case vc2 x σ1 hld _ _ =>
    -- the back edge: the frame again; the counter moved
    obtain ⟨hx0, hx1, hx2, hdf, hdd, hdg⟩ := hT
    simp only [Reg64s.get64] at hx0 hx1 hx2
    rcases hld with ⟨v, hm, -, -⟩ | ⟨-, v, hst, -⟩
    · simp [hx0, hdf] at hm
    · refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simp [hx0], by simp [hx1], by simp [hx2],
        by simpa using hdf, by simpa using hdd, by simpa using hdg⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      have hn := hst.2
      subst hg
      simp [SharedAccess.tick] at hn
  all_goals simp_all
  all_goals try exact fun h => h rfl
  case vc1 => trivial
  case vc6 => exact fun h => absurd rfl h

end Kraken.Promising.X64.EnvG.RelayX

#print axioms Kraken.Promising.X64.EnvG.RelayX.relayX_noNT
