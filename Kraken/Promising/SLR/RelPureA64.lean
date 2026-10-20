/-
Conjunct (i) of option (A) (`SLR/RelPure.lean`) for the AArch64 rules.

- MP reader (`mpRuleR`, through `ThreadRuleR.toRX`): writes nothing, so (i)
  holds in its **witness form** for the existing rule with no cell re-proved
  (`mpRuleRK`, through `ThreadRuleRX.toK`).
- MP writer (`mpRuleW`): its plain store of `Dt` is a non-release write, so
  the witness form is *not* free (the witness lives inside `wpW_str`). The
  **witness-free form** (`RelPure`) holds: `WorldW` makes `g.rel Dt` pure for
  every value (`mpW_relPure`).
- SWP spinlock (`swpRuleX`): `swpa` (acquire RMW, non-release write on
  armv8) and `str c` are non-release writes, so the witness form is not free
  (the witnesses live inside `HardCellsX`). The witness-free form holds for
  the current ghost through `World` (`swp_relPure`).

Proved, no `sorry`.
-/
import Kraken.Promising.SLR.RelPure
import Kraken.Promising.SLR.MpRule
import Kraken.Promising.SLR.SwpRuleX

namespace Kraken.Promising.SLR.Mp

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.MpTrees

variable [layout : _root_.Layout]

section Writer

variable [hw : Executable.ValidLayout (layout mpWriter)]

/-- **(i‴), witness-free, for the MP writer**: its only plain store writes
`Dt`, which `WorldW` keeps pure for the current ghost. -/
theorem mpW_relPure (P : Params) (A : Arch) (tid rd : Nat) (hL : MpLocs P) (hA : A.storeKind .plain ≠ .nt)
    (hA' : A.plainStore ≠ .rel) : RelPure (mpRuleW P A tid rd hL hA hA') := by
  intro cl c₀ c r g₀ g t tree h he hle ht hex
  obtain ⟨hW, t', ht', hF, i, hp, hph, -⟩ := invW_env h.1 he hle
  rw [ht] at ht'
  obtain rfl : t = t' := Option.some.inj ht'
  rcases PhaseW.pos hph with rfl | rfl | rfl | rfl | rfl
  · rw [exec_w_mov2 t.st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_w_str t.st (hF.at hp (by decide)) hF.x1 hF.dd] at hex
    cases hex
    exact ⟨fun _ => hW.2 _, fun _ => trivial⟩
  · rw [exec_w_mov3 t.st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_w_stlr t.st (hF.at hp (by decide)) hF.x0 hF.df] at hex
    cases hex
    exact EvTree.relWrites_relStore rfl
  · rw [exec_end_w hF hp] at hex; cases hex

end Writer

section Reader

variable [hr : Executable.ValidLayout (layout mpReader)]

/-- The MP reader's trees have no write at all. -/
theorem mpR_noNonRel (P : Params) (A : Arch) (tid : Nat) (hA1 : (A.loadKind .acq).isAcquire = true)
    (hA2 : (A.loadKind .acq == .plain) = false) : NoNonRel (mpRuleR P A tid hA1 hA2).toRX := by
  intro cl c₀ c r g₀ g t tree h he hle ht hex
  obtain ⟨-, t', ht', hF, i, hp, hph⟩ := invR_env h he hle
  rw [ht] at ht'
  obtain rfl : t = t' := Option.some.inj ht'
  rcases PhaseR.pos hph with rfl | rfl | rfl | rfl
  · rw [exec_r_ldar t.st (hF.at hp (by decide)) hF.x0 hF.df] at hex; cases hex; exact fun _ => trivial
  · rw [exec_r_cbz t.st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_r_ldr t.st (hF.at hp (by decide)) hF.x1 hF.dd] at hex; cases hex; exact fun _ => trivial
  · rw [exec_end_r hF hp] at hex; cases hex

/-- **(i), witness form, for the MP reader**: its existing rule is a
`ThreadRuleRXK`. -/
def mpRuleRK (P : Params) (A : Arch) (tid : Nat) (hA1 : (A.loadKind .acq).isAcquire = true)
    (hA2 : (A.loadKind .acq == .plain) = false) : ThreadRuleRXK (I := isa) A (MpPost P tid) tid :=
  ThreadRuleRX.toK _ (mpR_noNonRel P A tid hA1 hA2)

/-- **(i‴), witness-free, for the MP reader.** -/
theorem mpR_relPure (P : Params) (A : Arch) (tid : Nat) (hA1 : (A.loadKind .acq).isAcquire = true)
    (hA2 : (A.loadKind .acq == .plain) = false) : RelPure (mpRuleR P A tid hA1 hA2).toRX :=
  relPure_of_noNonRel _ (mpR_noNonRel P A tid hA1 hA2)

end Reader

end Kraken.Promising.SLR.Mp

namespace Kraken.Promising.SLR.SwpInv

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv
open Kraken.Promising.SLR.SwpTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout swpWorker)]

/-- **(i‴), witness-free, for the SWP spinlock.** The locking `swpa` writes
`W3 = 1` to `Lk` (a non-release RMW write on armv8: acquire only), pure for
`φ = g.rel Lk` (`lockPred_pure`); the counter store `str` writes `C`, pure
by `World`; the unlock `stlr` is a release. Unlike the existing
`swp_promisePure`, this is for the *current* ghost `g`, so the cell analysis
is redone with `World` instead of an assumed `rel`. -/
theorem swp_relPure (P : Params) (A : Arch) (tid : Nat) (H : HardCellsX P A tid) :
    RelPure (swpRuleX P A tid H) := by
  intro cl c₀ c r g₀ g t tree h he hle ht hex
  obtain ⟨hW, t', ht', hF, -, i, hp, hph, -⟩ := inv_env h.1 he hle
  rw [ht] at ht'
  obtain rfl : t = t' := Option.some.inj ht'
  rcases Phase.pos hph with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_mov t.st (hF.at hp (by decide))] at hex; cases hex; trivial
  · have hx3 := hF.x3_at hp (by decide)
    rw [exec_swpa t.st (hF.at hp (by decide)) hF.x0 hF.dl] at hex
    cases hex
    refine ⟨fun _ _ new hnew => ?_, fun _ => trivial⟩
    simp only [Option.some.injEq] at hnew
    subst hnew
    show Pred.Pure (g.rel P.Lk) _
    rw [hW.1]
    exact Spinlock.lockPred_pure fun h0 => by rw [hx3] at h0; exact absurd h0 (by decide)
  · rw [exec_cbz t.st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_ldr_spin t.st (hF.at hp (by decide)) hF.x0 hF.dl] at hex; cases hex; exact fun _ => trivial
  · rw [exec_cbnz t.st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_b_try t.st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_ldr_c t.st (hF.at hp (by decide)) hF.x1 hF.dc] at hex; cases hex; exact fun _ => trivial
  · rw [exec_add t.st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_str_c t.st (hF.at hp (by decide)) hF.x1 hF.dc] at hex
    cases hex
    exact ⟨fun _ => hW.2.1 _, fun _ => trivial⟩
  · rw [exec_stlr t.st (hF.at hp (by decide)) hF.x0 hF.dl] at hex
    cases hex
    exact EvTree.relWrites_relStore rfl
  · rw [exec_b_done t.st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_end hF hp] at hex; cases hex

end Kraken.Promising.SLR.SwpInv
