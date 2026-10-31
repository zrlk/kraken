/-
**`RefNoWr`: no write to the arena or the counter along the threads abort
path** (x86-64, wake.w; the twin of `Spike/Lib/A64WakeRefNoWr.lean`): the
shape of `WakePh.hpathW_hN` on `TPathW`'s seventeen nodes — the
dispatcher's and the stub's blocks silent (`AllocG.blkW_noWr`), the `leaq`
node (`AllocG.nodeW_noWr_si`), the `write` and exit calls
(`WakeWf.nodeW_noWr_svc`) — in `TObl`'s region (`callee_of_pre`).

- `tpathW_hN`: at any layout running wake.w.
- `refNoWr`: the piece.

**Where this differs from AArch64**: the stub's `leaq` is one node (A64's
`adrp`/`add`), the calls are `syscall`s; the region is `[-24, 16)` with no
alignment; the dispatcher's `j*` blocks are at `+16` and the stub's at
`+7`, `+34`, `+36` (sized cells); the parses are on `cellsOf asm`.
-/
import Spike.Lib.X64WakeRefLay
import Spike.Lib.X64WakeHAbStub

namespace Spike.Lib.X64.WakeRefNoWr

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Scc.Cert.Rt.X64 (code_field)
open Spike.Lib (Arena Region PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (lo)
open SccCode (wakeCells)
open Spike.Lib.X64.Abort (NT)
open Spike.Lib.X64.WakeWf (NoWrC)
open Spike.Lib.X64.WakeRefTP (TPathW)
open Spike.Lib.X64.WakeRefStub (RefNoWr callee_of_pre)
open Spike.Lib.X64.Flow (ofNat_zero')

set_option linter.unusedSimpArgs false

/-- **No write to the arena or the counter** at every node of the threads
abort path, at any layout running wake.w. -/
theorem tpathW_hN {L : RuntimeLayout} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {ar : Arena} {p : CoreTerm.Prog} {L0 : Spike.Lib.X64Consumer.Lbl} {ls0 : Spike.Lib.X64Consumer.Lsize}
    {Ctx : FragS isa} {fs : List TermRun.Frame} (a : BitVec 64) (hR : R.OK) (hlo' : R.lo ≤ -24)
    (hhi : 16 ≤ R.hi) :
    TPathW (NoWrC ar p L0 ls0 Ctx fs) (fun _ _ => False) L.exe L.endPc R F c0 ra := by
  have hI := Spike.Lib.X64.WakePh.instOkW hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hsd := SccCode.wake_abort
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, hj2, -, ht3, hj3, -, ht4, hj4, -, ht5, -, hg5, -⟩ := hdi
  have hst := hsd.1.2
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hx0, hn1, hx1, hsysIn, hx2, hx, -, -⟩ := hst
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hd0)
      (ofNat_zero' _) Spike.Lib.X64.Abort.Disp.d0_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact ht1)
      (ofNat_zero' _) Spike.Lib.X64.Abort.Disp.t1_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hj1)
      rfl Spike.Lib.X64.Abort.Disp.j1_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact ht2)
      (ofNat_zero' _) Spike.Lib.X64.Abort.Disp.t2_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hj2)
      rfl Spike.Lib.X64.Abort.Disp.j2_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact ht3)
      (ofNat_zero' _) Spike.Lib.X64.Abort.Disp.t3_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hj3)
      rfl Spike.Lib.X64.Abort.Disp.j3_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact ht4)
      (ofNat_zero' _) Spike.Lib.X64.Abort.Disp.t4_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hj4)
      rfl Spike.Lib.X64.Abort.Disp.j4_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact ht5)
      (ofNat_zero' _) Spike.Lib.X64.Abort.Disp.t5_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hg5)
      (ofNat_zero' _) Spike.Lib.X64.Abort.Disp.g5_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hx0)
      (ofNat_zero' _) Spike.Lib.X64.Abort.x0_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.nodeW_noWrC (Spike.Lib.X64.AllocG.nodeW_noWr_si hI (by rw [hp]; exact hn1) rfl
      (ofNat_zero' _).symm)
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hx1)
      rfl Spike.Lib.X64.Abort.x1Threads_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.nodeW_noWrC (Spike.Lib.X64.WakeWf.nodeW_noWr_svc
      (code_field L.lays rfl (by rw [hp]; exact hsysIn) rfl))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hx2)
      rfl Spike.Lib.X64.Abort.x2_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.nodeW_noWrC (Spike.Lib.X64.WakeWf.nodeW_noWr_svc
      (code_field L.lays rfl (by rw [hp]; exact hx) (ofNat_zero' _)))

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`RefNoWr`**: `NoWrW` at every node of the threads abort path. -/
theorem refNoWr {asm : Asm} (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = lo) (ls0 : Spike.Lib.X64Consumer.Lsize) (l : WeakMem.AllocLabel) (b n : Nat) :
    RefNoWr hp i ls0 l b n := by
  intro R m0 cP cA mT m1 σC c0 hpre _
  obtain ⟨hR', hlo', hhi'⟩ := callee_of_pre hp i hpre
  have hprog := Spike.Lib.X64.WakeSrcCtl.prog_W hp i hpa hwp
  have hlab := Spike.Lib.X64WakeOAb.hlab_W hp i hpa hwp hlo0
  rw [← Spike.Lib.X64.WakeRefStub.endR_eq hp i hpa hwp]
  exact tpathW_hN hprog hlo0 (Spike.Lib.X64.WakePh.siteW hprog hlo0 hlab)
    (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) hR' (by omega) (by omega)

end Spike.Lib.X64.WakeRefNoWr

/-- info: 'Spike.Lib.X64.WakeRefNoWr.tpathW_hN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefNoWr.tpathW_hN

/-- info: 'Spike.Lib.X64.WakeRefNoWr.refNoWr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefNoWr.refNoWr
