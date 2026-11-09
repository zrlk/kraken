/-
**wake.w's `clone` pc off the free pcs** (x86-64; the `clonePc` of
`Spike/Lib/A64WakeWcInv.lean` and `ne_clonePc_of_freeN` of
`Spike/Lib/A64WakeWcPreWI.lean`): main's `syscall` at `.Lwc_main.x3 + 46`
(`X64WakePreA.cloneAt`) lies in `ownG`'s range `[.Lwc_main.x2,
.Lwc_main.stk)`, so no free pc (`WcW.freeN`) is it. Checked by the kernel
against the certificate's labels, no absolute address in this file.

- `clonePc`: the clone's pc as a natural number;
- `clone_inCv`: `.x21 + 46` in `[.x20, .stk)`, below `2 ^ 64`;
- `ne_clonePc_of_freeN`: a free pc is not the clone's.
-/
import Spike.Lib.X64WakePreA
import Spike.Lib.X64WakeFree

namespace Spike.Lib.X64.Flow.WakeWc

open Kraken
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel)
open SccCode (wakeCells)
open Spike.Lib.X64.WakePh (lo)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh.WcW (cv inCv freeN)

/-- **The clone's pc** (`X64WakePreA.cloneAt`) as a natural number. -/
def clonePc (L : RuntimeLayout) : Nat := (Spike.Lib.X64WakePreA.cloneAt L.exe).toBitVec.toNat

/-- The clone's pc in `[.x20, .stk)`, below `2 ^ 64`. -/
theorem clone_inCv :
    ((codeLabel lo wakeCells ".Lwc_main.x3").isSome && decide (cv ".Lwc_main.x3" + 46 < 2 ^ 64) &&
    inCv ".Lwc_main.x2" ".Lwc_main.stk" (cv ".Lwc_main.x3" + 46)) = true := by
  unfold inCv cv; rw [← codeT_eq]; decide +kernel

/-- **A free pc is not the clone's** (`ownG`'s `[.x20, .stk)` range
contains it). -/
theorem ne_clonePc_of_freeN {L : RuntimeLayout}
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {x : Nat} (h : freeN x = true) :
    x ≠ clonePc L := by
  have hc := clone_inCv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hs, hb⟩, hin⟩ := hc
  have e : clonePc L = cv ".Lwc_main.x3" + 46 := by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
    have ey : cv ".Lwc_main.x3" = y := by simp [cv, hy]
    rw [ey] at hb ⊢
    show (L.lab ".Lwc_main.x3" + 46).toBitVec.toNat = y + 46
    rw [hlab _ y hy]
    show (BitVec.ofNat 64 y + BitVec.ofNat 64 46).toNat = y + 46
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [e]; intro hx
  unfold freeN at h
  rw [hx, hin] at h
  simp only [Bool.not_true, Bool.false_and, Bool.and_false] at h
  cases h

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.clone_inCv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.clone_inCv

/-- info: 'Spike.Lib.X64.Flow.WakeWc.ne_clonePc_of_freeN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.ne_clonePc_of_freeN
