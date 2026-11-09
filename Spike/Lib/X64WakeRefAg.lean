/-
**`ownG` agrees with `own2b` along the threads abort path below main's
frame** (x86-64, wake.w; the twin of `Spike/Lib/A64WakeRefAg.lean`):
`X64WakeRefStub.RefAg`, from `WakePh.abAgree2b` at `WakePh.abPT` in the
callee's region (`callee_of_pre`), the return address `raT` being
`.Lwc_main.x5` (`raT_x23`).

- `refAg`: `RefAg`.

**Where this differs from AArch64**: the callee's region is
`R.callee (-72 - 8) (-24) 16` with no alignment; the return address is
`.Lwc_main.x5` (A64's `.L21_wc_main.sp11`); the take site's check is
`siteOff_W` at the resolved addresses; the parses are on `cellsOf asm`.
-/
import Spike.Lib.X64WakeRefLay

namespace Spike.Lib.X64.WakeRefStub

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region PlaceWX)
open Spike.Lib.X64 (DFrame CKept Abs)
open Spike.Lib.X64.WakeRefTP (TPathW)
open Spike.Lib.X64.Rt (RuntimeLayout)
open SccCode (wakeCells)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`RefAg`**: `abAgree2b` at `abPT` in the callee's region, the take site
off `scc_rt_abort`, wake's abort code laid out. -/
theorem refAg {asm : Asm} (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (l : WeakMem.AllocLabel) (b : Nat) : RefAg hp i l b := by
  intro R m0 cP cA mT m1 σC c0 hpre _
  obtain ⟨hR', hlo', hhi'⟩ := callee_of_pre hp i hpre
  have hlab := Spike.Lib.X64WakeOAb.hlab_W hp i hpa hwp hlo
  have hl := lays_W hp i hpa hwp
  have hsd := SccCode.wake_abort
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hP := Spike.Lib.X64.WakePh.abPT (μ := Spike.Lib.X64.PhRec.μ (Ly))
    (F := fun m => DFrame R m0 m ∧ CKept R (-72 - 8) (-24) 16 m1 m ∧ Abs R ⟨-72, [(.rbp, 0)]⟩ m1 σC)
    (c0 := c0) (ra := ((Ly).lab ".Lwc_main.x5").toBitVec) (endPc := Spike.Lib.X64.WakeH1Inv.endR hp i)
    hlab hR' (by omega) (by omega) (siteOff_W hp i hlab)
    (Scc.Cert.Rt.X64.Abort.code_disp hl rfl hsd.2)
    (Scc.Cert.Rt.X64.Abort.code_stubs hl rfl SccCode.wake_abort .threads)
  have hA := TPathW.ofAgree (Spike.Lib.X64.WakePh.abAgree2b (a := Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) hlab hP)
  rw [raT_x23 hlab]
  exact hA

end Inst

end Spike.Lib.X64.WakeRefStub

/-- info: 'Spike.Lib.X64.WakeRefStub.refAg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.refAg
