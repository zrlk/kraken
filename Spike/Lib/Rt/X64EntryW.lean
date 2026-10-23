/-
**`_start`'s nodes inside `SFacts`, for any program** (`entryW_of_instOk`):
`entry_segW'`'s obligations (`EntryW`, `Spike/Lib/Rt/X64Entry.lean`) from
an instance's facts (`InstOk`, `Spike/Lib/Rt/X64RtW.lean`), the code check
`entryIn` and `_start`'s phase facts: the `xorl`'s node (`nodeW_fi_pre`),
the `andq`'s (`nodeW_and_pre`) and the call's block (`blkW_pre`), each off
the sites, not in the take's phase, its next pc in its phase. The x86-64
twin of ARM's `entryW_gen`. At a placed output the phase facts are A6's
(`Spike/Lib/Rt/X64EntryOfPlaceOK.lean`).
-/
import Spike.Lib.Rt.X64Entry
import Spike.Lib.Rt.X64RtW

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (blockAtB)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}

/-- **`_start`'s nodes inside `SFacts`** in a region with room for the
call's return address (`hR`, `hlo`, `hhi`), the source at `c0` (`hC0`),
given `_start`'s code (`hin`) and its phase facts: the `xorl`'s and the
`andq`'s pcs off the sites (`hok0`, `hok2`), their next pcs in their phase
(`hph0`, `hph2`), the call's block's phase check (`hblk`), and none of the
three pcs in the take's phase (`hT0`, `hT2`, `hT6`). -/
theorem entryW_of_instOk (hI : InstOk exe endPc cells lab μ own Tk K okPc ph)
    (hin : Code.Start.entryIn cells = true) {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -8)
    (hhi : 0 ≤ R.hi) {c0 : Ctl} (hC0 : CFacts Λ lbl c0)
    (hok0 : okPc (lab "_start" + Int64.ofNat 0).toBitVec.toNat = true)
    (hph0 : ph (lab "_start" + Int64.ofNat 0 + Int64.ofNat 2).toBitVec.toNat =
      ph (lab "_start" + Int64.ofNat 0).toBitVec.toNat)
    (hok2 : okPc (lab "_start" + Int64.ofNat 2).toBitVec.toNat = true)
    (hph2 : ph (lab "_start" + Int64.ofNat 2 + Int64.ofNat 4).toBitVec.toNat =
      ph (lab "_start" + Int64.ofNat 2).toBitVec.toNat)
    (hblk : blkPh okPc ph (fun _ => false) lab (lab "_start" + Int64.ofNat 6) 0 Code.Start.entryCall = true)
    (hT0 : ∀ s : State, pcOf s = (lab "_start" + Int64.ofNat 0).toBitVec.toNat → ¬ Tk s)
    (hT2 : ∀ s : State, pcOf s = (lab "_start" + Int64.ofNat 2).toBitVec.toNat → ¬ Tk s)
    (hT6 : ∀ s : State, pcOf s = (lab "_start" + Int64.ofNat 6).toBitVec.toNat → ¬ Tk s) :
    EntryW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F lab c0 := by
  simp only [Code.Start.entryIn, Code.Start.entryXor, Code.Start.entryAnd, Bool.and_eq_true] at hin
  obtain ⟨⟨hb0, hb1⟩, hb2⟩ := hin
  exact ⟨nodeW_fi_pre hI hb0 rfl (ofNat_zero' _).symm (fun _ _ hJ => hJ ▸ hC0) hok0 hT0 hph0,
    nodeW_and_pre hI hb1 rfl rfl (fun _ _ hJ => hJ ▸ hC0) hok2 hT2 hph2,
    blkW_pre hI (n := entryN2 lab c0) (dead := fun _ => false) (ra := 0) hb2 (ofNat_add' _ 2 4) entryCallB_ok hR
      hlo hhi (fun _ _ hJ => hJ ▸ hC0) hblk
      (fun _ _ _ k hk hr => (noRet_false (by decide) k hk hr).elim) (fun _ _ _ => rfl) hT6⟩

end Spike.Lib.X64.Rt
