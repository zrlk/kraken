/-
**hello.w's `clone` pc off the free pcs** (x86-64; the hello twin of
`X64WakeWcClonePc`, the `clone_inCvH` / `ne_clonePc_of_freeNH` of
`Spike/Lib/A64HelloWcPreWI.lean`): main's `syscall` at `.Lwc_main.x25 + 94`
(`X64HelloPreA.cloneAtH`, `clonePcH`) lies in `ownGH`'s range
`[.Lwc_main.x24, .Lwc_main.stk)`, so no free pc (`WcW.freeNH`) is it.
Checked by the kernel against the certificate's labels, no absolute address
in this file.

- `clone_inCvH`: `.x25 + 94` in `[.x24, .stk)`, below `2 ^ 64`;
- `ne_clonePc_of_freeNH`: a free pc is not the clone's.

## Differences from the AArch64 version

As `X64WakeWcClonePc` against AArch64 wake: the clone is the `syscall` at
`.Lwc_main.x25 + 94` (AArch64's `svc` at `.L22_wc_main.sp6 + 4 * 25`),
`ownGH`'s range is `[.x24, .stk)` (AArch64's `[.sp4, .stack_grow)`), and
labels carry no function number. AArch64 states both lemmas in
`A64HelloWcPreWI`; here they are split off as on wake, since they read the
clone's pc (`X64HelloWcInv.clonePcH`), which `X64HelloWcPreWI`'s blocks do
not need.
-/
import Spike.Lib.X64HelloWcInv
import Spike.Lib.X64HelloWcPreW

namespace Spike.Lib.X64.HelloPh.WcW

open Kraken
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel)
open SccCode (helloCells)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.Rt (RuntimeLayout)

/-- The clone's pc in `[.x24, .stk)`, below `2 ^ 64`. -/
theorem clone_inCvH :
    ((codeLabel lo helloCells ".Lwc_main.x25").isSome && decide (cvH ".Lwc_main.x25" + 94 < 2 ^ 64) &&
    inCvH ".Lwc_main.x24" ".Lwc_main.stk" (cvH ".Lwc_main.x25" + 94)) = true := by
  unfold inCvH cvH; rw [← codeT_eq]; decide +kernel

/-- **A free pc is not the clone's** (`ownGH`'s `[.x24, .stk)` range
contains it). -/
theorem ne_clonePc_of_freeNH {L : RuntimeLayout}
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {x : Nat}
    (h : freeNH x = true) : x ≠ Spike.Lib.X64HelloPreA.clonePcH L := by
  have hc := clone_inCvH
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hs, hb⟩, hin⟩ := hc
  have e : Spike.Lib.X64HelloPreA.clonePcH L = cvH ".Lwc_main.x25" + 94 := by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
    have ey : cvH ".Lwc_main.x25" = y := by simp [cvH, hy]
    rw [ey] at hb ⊢
    show (L.lab ".Lwc_main.x25" + 94).toBitVec.toNat = y + 94
    rw [hlab _ y hy]
    show (BitVec.ofNat 64 y + BitVec.ofNat 64 94).toNat = y + 94
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [e]; intro hx
  unfold freeNH at h
  rw [hx, hin] at h
  simp only [Bool.not_true, Bool.false_and, Bool.and_false] at h
  cases h

end Spike.Lib.X64.HelloPh.WcW

/-- info: 'Spike.Lib.X64.HelloPh.WcW.clone_inCvH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.clone_inCvH

/--
info: 'Spike.Lib.X64.HelloPh.WcW.ne_clonePc_of_freeNH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.ne_clonePc_of_freeNH
