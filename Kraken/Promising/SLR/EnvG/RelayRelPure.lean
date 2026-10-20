/-
**Part 3: the relay is pure** (the
`EnvG/TakeMpRelPure.lean` pattern; the purity environment is unchanged for
taking threads, `EnvG/TakeFinal.lean`).

- `relay_relPure`: the relay's only non-release write is its plain
  `str w5, [x1]` to `⟨d, 4⟩`, whose release predicate is pure (`hd`); its
  `stlr w6, [x2]` is a release, unconstrained. `cfgEnv_partial`, counted,
  for the spin loop's back edge.

The writer and the reader reuse `mpWriter_relPure` and `mpReader_relPure`.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnvA64
import Kraken.Promising.SLR.EnvG.RelaySpec
import Kraken.AArch64.EnvCfg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR

namespace Kraken.Promising.SLR.EnvG.Relay

set_option mvcgen.warning false
set_option experimental.vcgen true

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relay)]

local instance relay.relPureEnv : CodeEnv := ⟨layout relay⟩

/-- The relay's purity table: at `spin`, the three addresses in `X0`/`X1`/
`X2`, none in `dmem`. -/
abbrev relayPureTable (f1 d f2 : BitVec 64) (rel : Loc → Pred) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)).State → Prop :=
  fun lb s _ => lb = "spin" → s.regs.X0.toBitVec = f1 ∧ s.regs.X1.toBitVec = d ∧ s.regs.X2.toBitVec = f2 ∧
    Mem.loadInt s.dmem f1 4 = none ∧ Mem.loadInt s.dmem d 4 = none ∧ Mem.loadInt s.dmem f2 4 = none

/-- **The relay is pure**: its only non-release write is to `⟨d, 4⟩`;
counted, partial. -/
theorem relay_relPure (rel : Loc → Pred) (f1 d f2 : BitVec 64) (hd : ∀ v, Pred.Pure (rel ⟨d, 4⟩) v) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
      (fun s _ => s.regs.X0.toBitVec = f1 ∧ s.regs.X1.toBitVec = d ∧ s.regs.X2.toBitVec = f2 ∧
        Mem.loadInt s.dmem f1 4 = none ∧ Mem.loadInt s.dmem d 4 = none ∧ Mem.loadInt s.dmem f2 4 = none)
      relay (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (relayPureTable f1 d f2 rel) (hP := by funext s g; simp [relayPureTable])
  cfg_cases_env [relay]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  case vc4 =>
    -- the back edge (`cbz` taken): the counter moved
    have hn := (‹(SharedEnv.counted _).step _ _ _ _›).2
    refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simpa using hT.1, by simpa using hT.2.1,
      by simpa using hT.2.2.1, by simpa using hT.2.2.2.1, by simpa using hT.2.2.2.2.1, by simpa using hT.2.2.2.2.2⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; simp at hn
  all_goals simp_all [Arch.storeKind, show Arch.armv8.plainStore = .plain from rfl]

end Kraken.Promising.SLR.EnvG.Relay
