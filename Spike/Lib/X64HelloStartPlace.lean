/-
**`X0WH` inside `scc_rt_alloc_tcb`** (hello.w, x86-64; the twin of `Spike/Lib/A64HelloStartPlace.lean`'s live
part, hello's copy of wake's x86-64 `X64WakeStartPlace.x0W_tcb`): `StartTcb.startTcb_WSH`'s `hX0` at
`X0WH L ax`, below hello's clone (`.Lwc_main.x3 + 94`) and off the take site.

- `x0WH_tcb`: `X0WH` in `scc_rt_alloc_tcb … scc_rt_thread_reserve`.

## Differences from the AArch64 version

- The clone is the `syscall` at `.Lwc_main.x3 + 94` (`X64HelloPreA.clonePcH`; AArch64: the `svc` at
  `.L22_wc_main.sp6 + 100`), and code labels are read by `codeLabel lo helloCells` (AArch64:
  `codeOf lo helloProg`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `hello_start_wc_place`. The live
  placed path is `X64HelloStartPlaceX.hello_rd_placeX`.
-/
import Spike.Lib.X64HelloStartH0Ti

namespace Spike.Lib.X64.HelloPh.StartPlace

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf)
open Scc.Cert.Rt.X64 (codeT_eq)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh (lo)

open Spike.Lib.X64.HelloPh.WcW (cvH freeLabsH lab_cvH clone_inCvH) in
/-- **`X0WH` inside `scc_rt_alloc_tcb`** (`startTcb_WSH`'s `hX0`): below
hello's clone (`.Lwc_main.x3 + 94`), off the take site. -/
theorem x0WH_tcb {L : RuntimeLayout} {ax : Int64}
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hax : ax.toBitVec.toNat = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) (s : State)
    (h : Spike.Lib.X64.WakePh.inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s) : X0WH L ax s := by
  have hl := fun {l : Label} hl => show (L.lab l).toBitVec.toNat = cvH l by
    have := List.all_eq_true.mp freeLabsH l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact lab_cvH hlab this.1 this.2
  have hc := clone_inCvH
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hs, hb⟩, -⟩ := hc
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
  have ey : cvH ".Lwc_main.x3" = y := by simp [cvH, hy]
  have e : Spike.Lib.X64HelloPreA.clonePcH L = y + 94 := by
    rw [ey] at hb
    show (L.lab ".Lwc_main.x3" + 94).toBitVec.toNat = y + 94
    rw [hlab _ y hy]
    show (BitVec.ofNat 64 y + BitVec.ofNat 64 94).toNat = y + 94
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hd : (decide (cvH Spike.Lib.X64.Flow.Ret0.StackTake.siteL < cvH "scc_rt_alloc_tcb" ∨
      cvH "scc_rt_thread_reserve" ≤ cvH Spike.Lib.X64.Flow.Ret0.StackTake.siteL) &&
      decide (cvH "scc_rt_thread_reserve" ≤ cvH ".Lwc_main.x3")) = true := by
    unfold cvH; rw [← codeT_eq]; decide +kernel
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
  rw [ey] at hd
  unfold Spike.Lib.X64.WakePh.inPc at h
  rw [hl (by simp), hl (by simp)] at h
  exact ⟨by rw [e]; omega, fun he => absurd he (by rw [hax, hl (by simp)]; omega)⟩

end Spike.Lib.X64.HelloPh.StartPlace

/-- info: 'Spike.Lib.X64.HelloPh.StartPlace.x0WH_tcb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartPlace.x0WH_tcb
