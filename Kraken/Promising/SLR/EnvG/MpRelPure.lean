/-
**MP purity by `vcgen`**: each MP thread in the purity environment
`SharedEnv.relPure Arch.armv8 rel`, by one `vcgen` call.

- `mpWriter_relPure`: the writer's plain `str w2, [x1]` writes `Dt`, whose
  release predicate is pure (`hd`; `Pred.emp` for `mpGhost`); its
  `stlr w3, [x0]` is a release, unconstrained.
- `mpReader_relPure`: the reader writes nothing (`cfgEnv_partial`, counted,
  for the spin loop's back edge).

These replace `MpPure`'s `ReachW`/`ReachR`/`mp_cell` (and the `MpTrees`
`exec_*` lemmas they rest on) in `mp_envG'` (`EnvG/MpEnvGPublic2.lean`).
-/
import Kraken.Promising.SLR.EnvG.RelPureEnvA64
import Kraken.Promising.SLR.MpTrees

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.MpTrees

namespace Kraken.Promising.SLR.EnvG.MpRelPure

set_option mvcgen.warning false
set_option experimental.vcgen true

variable [layout : _root_.Layout]

section Writer

local instance mpWriter.env : CodeEnv := ⟨layout mpWriter⟩

/-- **The MP writer is pure**: its only non-release write is to `⟨d, 4⟩`. -/
theorem mpWriter_relPure (rel : Loc → Pred) (f d : BitVec 64) (hd : ∀ v, Pred.Pure (rel ⟨d, 4⟩) v) :
    TripleEnv (SharedEnv.relPure Arch.armv8 rel)
      (fun s _ => s.regs.X0.toBitVec = f ∧ s.regs.X1.toBitVec = d ∧ Mem.loadInt s.dmem f 4 = none ∧
        Mem.loadInt s.dmem d 4 = none)
      mpWriter (fun _ _ => True) (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold mpWriter
  vcgen
  all_goals simp_all [Arch.storeKind, show Arch.armv8.plainStore = .plain from rfl]

end Writer

section Reader

variable [Executable.ValidLayout (layout mpReader)]

local instance mpReader.env : CodeEnv := ⟨layout mpReader⟩

/-- The reader's table: at `spin`, the flag address in `X0`, not in `dmem`
(the acquire load goes to the environment). -/
abbrev readerTable (f : BitVec 64) (rel : Loc → Pred) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)).State → Prop :=
  fun lb s _ => lb = "spin" → s.regs.X0.toBitVec = f ∧ Mem.loadInt s.dmem f 4 = none

/-- **The MP reader is pure** (it writes nothing); counted, partial. -/
theorem mpReader_relPure (rel : Loc → Pred) (f : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
      (fun s _ => s.regs.X0.toBitVec = f ∧ Mem.loadInt s.dmem f 4 = none)
      mpReader (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (readerTable f rel) (hP := by funext s g; simp [readerTable])
  cfg_cases_env [mpReader]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹(_ → _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [forall_const] at hT
  case vc4 =>
    -- the back edge (`cbz` taken): the counter moved
    have hn := (‹(SharedEnv.counted _).step _ _ _ _›).2
    refine Table.ofLabelsEnv_at ⟨by decide, fun _ => ⟨by simpa using hT.1, by simpa using hT.2⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg; simp at hn
  all_goals simp_all

end Reader

end Kraken.Promising.SLR.EnvG.MpRelPure
