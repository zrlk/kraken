/-
**`AbX` at the child's stub** (row 5i-hab1, P2's first
field, AArch64; the pilot of `A64HelloAbObl`'s recipe): `ZObl.hZc` at
`X := AbX μ lab`, the twin of `Wk.child_relH` (`A64HelloRelZ`) with
`blkW_abX` for its `rb`.

- `stubRuns`, `stubRuns_chk`: the stub's pcs, off the exits and the
  transfer sites (decided on the listing).
- `child_abX`: `AbX` at the stub's two blocks.
-/
import Spike.Lib.A64HelloAbObl
import Spike.Lib.A64HelloRelZ

namespace Spike.Lib.A64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks)
open Scc.Cert.Rt.A64 (Lays endOf blockAt)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib (Region)
open Spike.Lib.A64.Flow (ND ofNat4_succ ofNat4_zero code_of)
open Spike.Lib.A64.Flow.Worker (NodeZA)
open Spike.Lib.A64WakeOff (RunsOffA PcOffA pcOffA_add)
open Spike.Lib.A64.RunsOff (runsNeChk abPtsA runsOffA_of_chk)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words cN childN cBlk pfxM stubIn hello_stubIn cb chB cb_ok chB_ok)
open SccCode (helloProg)

/-- **The child's stub's pcs**: the `cbz` past the `clone` and the call
block. -/
def stubRuns : List (Label × Nat × Nat) :=
  [(pfxM ++ ".sp6", 26, 27), (pfxM ++ ".child13", 0, chB.length)]

theorem stubRuns_chk : runsNeChk helloProg stubRuns abPtsA = true := by decide +kernel

/-- The stub's blocks' targets off the write abort's pcs (decided at helloProg's code labels). -/
theorem chC_cb : abOffHC (pfxM ++ ".sp6") 26 (pfxM ++ ".sp6") (cb pfxM) = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem chC_ch : abOffHC (pfxM ++ ".child13") 0 (pfxM ++ ".child13") chB = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

variable {μ : Marks} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}

/-- **`AbX` at the child's stub** (`ZObl.hZc`). -/
theorem child_abX (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo helloProg l = some x →
      (_root_.Executable.labels exe).label l = Int64.ofNat x)
    (hμ : MarksL μ (_root_.Executable.labels exe).label) {R : Region} {F : MachineData → Prop}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -224) (hhi : 0 ≤ R.hi)
    {cW : Ctl} {w : Words} {tp sp0 : BitVec 64} (i : Child.CN) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) exe endPc R F
      (cN pfxM (_root_.Executable.labels exe).label cW w tp sp0 i) (cBlk i) := by
  have hin := hello_stubIn
  simp only [stubIn, Bool.and_eq_true] at hin
  obtain ⟨hcb, hch⟩ := hin
  have hoff := runsOffA_of_chk hp stubRuns_chk
  cases i
  · have he : (_root_.Executable.labels exe).label (pfxM ++ ".sp6") + Int64.ofNat (4 * 26) =
        (cN pfxM (_root_.Executable.labels exe).label cW w tp sp0 .cb).pc := by
      simp only [cN, childN, ofNat4_succ, ofNat4_zero]
    exact blkW_abX (rl := pfxM ++ ".sp6") hμ (code_of hp hend hcb he) cb_ok hR hal hlo hhi
      (fun j hj => pcOffA_add hoff (List.Mem.head _) (Nat.le_refl _) (by simp [cBlk, cb] at hj; omega) he.symm)
      he (abOffHC_sound hlab chC_cb)
      (fun _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false (by decide) j hj r hr).elim)
  · have he : (_root_.Executable.labels exe).label (pfxM ++ ".child13") + Int64.ofNat (4 * 0) =
        (cN pfxM (_root_.Executable.labels exe).label cW w tp sp0 .ch).pc := ofNat4_zero _
    exact blkW_abX (rl := pfxM ++ ".child13") hμ (code_of hp hend hch he) chB_ok hR hal hlo hhi
      (fun j hj => pcOffA_add hoff (List.Mem.tail _ (List.Mem.head _)) (Nat.le_refl _)
        (by simp only [cBlk] at hj; omega) he.symm)
      he (abOffHC_sound hlab chC_ch)
      (fun _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false (by decide) j hj r hr).elim)

end Spike.Lib.A64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.child_abX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.child_abX
