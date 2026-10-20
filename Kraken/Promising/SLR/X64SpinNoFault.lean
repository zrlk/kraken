/-
`NoFaultRule` for the x64 spinlock worker's rule (`X64SpinInv.spinRuleX`):
at every position of the invariant (`Phase.pos`) the cell's event tree
(`SLR/X64SpinTrees.lean`, read under `Frame`'s `RDI = l`, `RSI = c` and
private memory facts) has no `.fault` leaf, and at the end (position 14) the
worker has halted (`X64SpinTrees.exec_end`). So the rule's `wp` holds with
`.fault ↦ False`.
-/
import Kraken.Promising.SLR.X64SpinRule
import Kraken.Promising.SLR.Sim.NoFault

namespace Kraken.Promising.SLR.X64SpinInv

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.SLR.X64SpinTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

/-- Close `EvTree.NoFault` of an explicit cell tree. -/
local macro "nofault" : tactic =>
  `(tactic| first | trivial | exact fun _ => trivial | simp [EvTree.NoFault])

/-- At every position of `Phase` the worker's next event tree has no fault
leaf. -/
theorem noFault_cell {P : Params} {st : State} (hF : Frame P st) {i : Nat} (hp : AtPos st i)
    (hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
      i = 12 ∨ i = 14) {tree : EvTree isa.State} (hex : isa.exec st = some tree) : tree.NoFault := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_load_lock st (hF.at hp (by decide)) hF.rdi hF.dl] at hex; cases hex; nofault
  · rw [exec_test st (hF.at hp (by decide))] at hex; cases hex; nofault
  · rw [exec_jne_spin st (hF.at hp (by decide))] at hex; cases hex; nofault
  · rw [exec_mov_one st (hF.at hp (by decide))] at hex; cases hex; nofault
  · rw [exec_xchg st (hF.at hp (by decide)) hF.rdi hF.dl] at hex; cases hex; nofault
  · rw [exec_test2 st (hF.at hp (by decide))] at hex; cases hex; nofault
  · rw [exec_jne_retry st (hF.at hp (by decide))] at hex; cases hex; nofault
  · rw [exec_load_counter st (hF.at hp (by decide)) hF.rsi hF.dc] at hex; cases hex; nofault
  · rw [exec_add st (hF.at hp (by decide))] at hex; cases hex; nofault
  · rw [exec_store_counter st (hF.at hp (by decide)) hF.rsi hF.dc] at hex; cases hex; nofault
  · rw [exec_unlock st (hF.at hp (by decide)) hF.rdi hF.dl] at hex; cases hex; nofault
  · rw [exec_jmp_done st (hF.at hp (by decide))] at hex; cases hex; nofault
  · rw [exec_end st hF.exe hp] at hex; cases hex

/-- **The x64 spinlock worker's rule excludes faults.** -/
theorem spinRuleX_noFault (P : Params) (A : Arch) (tid : Nat) (H : HardCellsX P A tid) :
    NoFaultRule (spinRuleX P A tid H) :=
  NoFaultRule.ofNoFault fun _ t tree h he hle ht hex _ _ _ _ => by
    obtain ⟨-, t', ht', hF, -, i, hp, hph, -⟩ := inv_env h.1 he hle
    rw [ht] at ht'
    obtain rfl : t = t' := Option.some.inj ht'
    exact noFault_cell hF hp (Phase.pos hph) hex

end Kraken.Promising.SLR.X64SpinInv
