/-
`NoFaultRule` for the two rules of MP: the writer's `mpRuleW` and the
reader's `mpRuleR` (a `ThreadRuleR`, through `ThreadRuleR.toRX`). At every
position of the invariant (`PhaseW.pos`, `PhaseR.pos`) the cell's event tree
(`SLR/MpTrees.lean`, read under the frame facts) has no `.fault` leaf, and at
the end (position 4) the thread has halted. So both rules' `wp` hold with
`.fault ↦ False`.
-/
import Kraken.Promising.SLR.MpRule
import Kraken.Promising.SLR.Sim.NoFault

namespace Kraken.Promising.SLR.Mp

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.MpTrees

variable [layout : _root_.Layout]

section Writer

variable [hw : Executable.ValidLayout (layout mpWriter)]

/-- At every position of `PhaseW` the writer's next event tree has no fault
leaf. -/
theorem noFault_cellW {P : Params} {st : State} (hF : FrameW P st) {i : Nat} (hp : AtPos mpWriter st i)
    (hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) {tree : EvTree isa.State} (hex : isa.exec st = some tree) :
    tree.NoFault := by
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · rw [exec_w_mov2 st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_w_str st (hF.at hp (by decide)) hF.x1 hF.dd] at hex; cases hex; exact fun _ => trivial
  · rw [exec_w_mov3 st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_w_stlr st (hF.at hp (by decide)) hF.x0 hF.df] at hex; cases hex; exact fun _ => trivial
  · rw [exec_end_w hF hp] at hex; cases hex

/-- **The MP writer's rule excludes faults.** -/
theorem mpRuleW_noFault (P : Params) (A : Arch) (tid rd : Nat) (hL : MpLocs P) (hA : A.storeKind .plain ≠ .nt)
    (hA' : A.plainStore ≠ .rel) : NoFaultRule (mpRuleW P A tid rd hL hA hA') :=
  NoFaultRule.ofNoFault fun _ t tree h he hle ht hex _ _ _ _ => by
    obtain ⟨-, t', ht', hF, i, hp, hph, -⟩ := invW_env h.1 he hle
    rw [ht] at ht'
    obtain rfl : t = t' := Option.some.inj ht'
    exact noFault_cellW hF hp (PhaseW.pos hph) hex

end Writer

section Reader

variable [hr : Executable.ValidLayout (layout mpReader)]

/-- At every position of `PhaseR` the reader's next event tree has no fault
leaf. -/
theorem noFault_cellR {P : Params} {st : State} (hF : FrameR P st) {i : Nat} (hp : AtPos mpReader st i)
    (hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) {tree : EvTree isa.State} (hex : isa.exec st = some tree) :
    tree.NoFault := by
  rcases hi with rfl | rfl | rfl | rfl
  · rw [exec_r_ldar st (hF.at hp (by decide)) hF.x0 hF.df] at hex; cases hex; exact fun _ => trivial
  · rw [exec_r_cbz st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_r_ldr st (hF.at hp (by decide)) hF.x1 hF.dd] at hex; cases hex; exact fun _ => trivial
  · rw [exec_end_r hF hp] at hex; cases hex

/-- **The MP reader's rule excludes faults** (as a `ThreadRuleRX`, through
`ThreadRuleR.toRX`). -/
theorem mpRuleR_noFault (P : Params) (A : Arch) (tid : Nat) (hA1 : (A.loadKind .acq).isAcquire = true)
    (hA2 : (A.loadKind .acq == .plain) = false) : NoFaultRule (mpRuleR P A tid hA1 hA2).toRX :=
  NoFaultRule.ofR fun t tree h ht hex => by
    obtain ⟨-, t', ht', hF, i, hp, hph⟩ := h
    rw [ht] at ht'
    obtain rfl : t = t' := Option.some.inj ht'
    exact noFault_cellR hF hp (PhaseR.pos hph) hex

end Reader

end Kraken.Promising.SLR.Mp
