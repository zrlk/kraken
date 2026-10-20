/-
The reader's data load (`ldr w4, [x1]`, position 3 → 4) and the slot
argument behind it.

The reader does not own `Dt`: loads keep the resource (`EvTree.eraseWPR_load`).
What it has is an acquire id `ι` of `Fl` with predicate `φ` (`WorldR`) and a
flag message `(Fl, tsF)` with a non-zero low word at or below its read view
(`Seen`, from the acquire load). Under clean erasure (`T = ⊥`) at the start of
the load:

- `(Fl, tsF)` is a release message (`φ` is impure there, `Erase.pure`), so it
  carries a slot for `ι` (`Erase.slotsDom`: the reader holds `ι`, so the
  total holds it once), and that slot satisfies `φ`: it holds all of `Dt`,
  with maximal write `(1, ts)`, `ts ≤ tsF` (`slot_of_seen`);
- the load, at a view above `tsF ≥ ts`, returns `1` (the generic
  `read_max_slot` of `SLR/StoreHelpers.lean`): the total write set of `Dt`
  is the slot's (`total_max_of_slot`), and no other thread may write `Dt`
  (`not_mayWrite_of_slot`): the only way to `Dt` is the slot, which only the
  holder of `ι` may acquire (`canAcq_inv`; the reader holds `ι` once, so no
  other thread and no slot holds it, and it is not an update id).

`slot_of_seen` is in `SLR/MpSpec.lean` (moved unchanged).
-/
import Kraken.Promising.SLR.MpCells
import Kraken.Promising.SLR.StoreHelpers
import Kraken.Promising.SLR.MpSpec

namespace Kraken.Promising.SLR.Mp

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.MpTrees

/-! ## The data load -/

variable [layout : _root_.Layout] [hr : Executable.ValidLayout (layout mpReader)]

/-- **The data load** (`ldr w4, [x1]`, position 3 → 4): under clean erasure
it returns `1`. -/
theorem wpR_ldr {P : Params} {A : Arch} {tid : Nat} : CellR P A tid 3 := by
  intro cl c r g rF t tree hW ht hF hp hph hex
  have hn := lt_size_of_get? ht
  rw [exec_r_ldr t.st (hF.at hp (by decide)) hF.x1 hF.dd] at hex
  cases hex
  simp only [PhaseR] at hph
  obtain ⟨-, tsF, vF, hrdF, hvF, htsF⟩ := hph
  refine EvTree.eraseWPR_load fun x hx => ?_
  obtain ⟨hmem, hpr⟩ := readSuccs_memProm A _ hx
  obtain ⟨tr, val, rfl, -, hrd, hwi, hnp⟩ := (mem_readSuccs A).mp hx
  refine WpPostR.noWrite hmem hpr fun t' hst _ _ => ?_
  refine invR_withThread (i := 4) hW ht hst (hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl)
    rfl ?_
  simp only [PhaseR]
  refine ⟨⟨_, tsF, vF, hrdF, hvF, Nat.le_refl _⟩, fun ⟨_, E'⟩ => ?_⟩
  obtain ⟨hrel, ι, -, hι, hracq⟩ := hW
  have hacq : (total (setRes rF tid r) g c).acq P.Fl ι = 1 := by
    have h1 := sub_acq_le (sub_total_thread (g := g) (c := c) (rF := setRes rF tid r) hn) P.Fl ι
    have h2 := E'.valid.2 P.Fl ι
    rw [setRes_self, hracq] at h1
    omega
  obtain ⟨s, hs, hkey, hid, hq, tsd, hXd, hmaxd, htsd⟩ := slot_of_seen E' hrel hι hacq hrdF hvF
  have hvr : t.views.vrNew ≤ readPre A (instrViews t (isa.deps t.st)) (ctx₀ t tid c.mem) .plain :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  obtain ⟨-, rfl⟩ := read_max_slot E' ht hs hq (by rw [setRes_self, hkey, hid]; exact hracq) hXd hmaxd
    hrd hnp hwi
    (Nat.le_trans htsd (Nat.le_trans htsF (Nat.le_trans hvr (Nat.le_max_left _ _))))
  simp only [Reg64s.setXReg]
  decide

end Kraken.Promising.SLR.Mp
