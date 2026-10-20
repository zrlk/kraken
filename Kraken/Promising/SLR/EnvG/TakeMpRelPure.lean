/-
**Part 7: the writing reader is pure** (the
`EnvG/MpRelPure.lean` pattern). The purity environment is unchanged for
taking threads (`EnvG/TakeFinal.lean`, "no `relPureT`").

- `takeReader_relPure`: the reader's only non-release write is its plain
  `str w5, [x1]` to `⟨d, 4⟩`, whose release predicate is pure (`hd`);
  `cfgEnv_partial`, counted, for the spin loop's back edge.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnvA64
import Kraken.Promising.SLR.EnvG.TakeMp
import Kraken.AArch64.EnvCfg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR

namespace Kraken.Promising.SLR.EnvG.TakeMp

set_option mvcgen.warning false
set_option experimental.vcgen true

variable [layout : _root_.Layout] [Executable.ValidLayout (layout takeReader)]

local instance takeReader.relPureEnv : CodeEnv := ⟨layout takeReader⟩

/-- The writing reader's purity table: at `spin`, both addresses in `X0`/`X1`,
neither in `dmem`. -/
abbrev pureTable (f d : BitVec 64) (rel : Loc → Pred) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)).State → Prop :=
  fun lb s _ => lb = "spin" → s.regs.X0.toBitVec = f ∧ s.regs.X1.toBitVec = d ∧ Mem.loadInt s.dmem f 4 = none ∧
    Mem.loadInt s.dmem d 4 = none

/-- **The writing reader is pure**: its only non-release write is to
`⟨d, 4⟩`; counted, partial. -/
theorem takeReader_relPure (rel : Loc → Pred) (f d : BitVec 64) (hd : ∀ v, Pred.Pure (rel ⟨d, 4⟩) v) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
      (fun s _ => s.regs.X0.toBitVec = f ∧ s.regs.X1.toBitVec = d ∧ Mem.loadInt s.dmem f 4 = none ∧
        Mem.loadInt s.dmem d 4 = none)
      takeReader (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (pureTable f d rel) (hP := by funext s g; simp [pureTable])
  cfg_cases_env [takeReader]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  case vc4 =>
    -- the back edge (`cbz` taken): the counter moved
    have hn := (‹(SharedEnv.counted _).step _ _ _ _›).2
    refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simpa using hT.1, by simpa using hT.2.1,
      by simpa using hT.2.2.1, by simpa using hT.2.2.2⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; simp at hn
  all_goals simp_all [Arch.storeKind, show Arch.armv8.plainStore = .plain from rfl]

end Kraken.Promising.SLR.EnvG.TakeMp
