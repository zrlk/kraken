/-
`NoFaultRule` for the SWP spinlock worker's rule (`SwpInv.swpRuleX`): at
every position of the invariant (`Phase.pos`) the cell's event tree
(`SLR/SwpTrees.lean`, read under `Frame`'s `X0 = l`, `X1 = c` and private
memory facts) has no `.fault` leaf, and at the end (position 16) the worker
has halted (`exec_end`). So the rule's `wp` holds with `.fault ↦ False`.
-/
import Kraken.Promising.SLR.SwpRuleX
import Kraken.Promising.SLR.SwpPure
import Kraken.Promising.SLR.Sim.NoFault

namespace Kraken.Promising.SLR.SwpInv

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv
open Kraken.Promising.SLR.SwpTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout swpWorker)]

/-- At every position of `Phase` the worker's next event tree has no fault
leaf. -/
theorem noFault_cell {P : Params} {st : State} (hF : Frame P st) {i : Nat} (hp : AtPos st i)
    (hi : i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨
      i = 16) {tree : EvTree isa.State} (hex : isa.exec st = some tree) : tree.NoFault := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_mov st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_swpa st (hF.at hp (by decide)) hF.x0 hF.dl] at hex; cases hex; exact fun _ => trivial
  · rw [exec_cbz st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_ldr_spin st (hF.at hp (by decide)) hF.x0 hF.dl] at hex; cases hex; exact fun _ => trivial
  · rw [exec_cbnz st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_b_try st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_ldr_c st (hF.at hp (by decide)) hF.x1 hF.dc] at hex; cases hex; exact fun _ => trivial
  · rw [exec_add st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_str_c st (hF.at hp (by decide)) hF.x1 hF.dc] at hex; cases hex; exact fun _ => trivial
  · rw [exec_stlr st (hF.at hp (by decide)) hF.x0 hF.dl] at hex; cases hex; exact fun _ => trivial
  · rw [exec_b_done st (hF.at hp (by decide))] at hex; cases hex; trivial
  · rw [exec_end hF hp] at hex; cases hex

/-- **The SWP worker's rule excludes faults.** -/
theorem swpRuleX_noFault (P : Params) (A : Arch) (tid : Nat) (H : HardCellsX P A tid) :
    NoFaultRule (swpRuleX P A tid H) :=
  NoFaultRule.ofNoFault fun _ t tree h he hle ht hex _ _ _ _ => by
    obtain ⟨-, t', ht', hF, -, i, hp, hph, -⟩ := inv_env h.1 he hle
    rw [ht] at ht'
    obtain rfl : t = t' := Option.some.inj ht'
    exact noFault_cell hF hp (Phase.pos hph) hex

end Kraken.Promising.SLR.SwpInv
