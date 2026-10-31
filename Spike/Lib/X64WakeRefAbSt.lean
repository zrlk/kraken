/-
**`RefAbSt`: the write abort's phase kept along the threads abort path**
(x86-64, wake.w; the twin of `Spike/Lib/A64WakeRefAbSt.lean`):
`WakeWf.tpathW_ab` at the second `scc_rt_thread_init` instance's facts
(`instOk2bP`: `own2b` at `ph2b`), `ph2b`'s phase facts on the path
(`abortPhTW`), the take site off the threads stub's exit call (`lab_ne`), in
`TObl`'s region (`callee_of_pre`).

- `refAbSt`: the piece.

**Unlike AArch64**: `TObl`'s region is `R.callee (-72 - 8) (-24) 16`, its
bounds from `callee_of_pre` (A64's alignment premise has no counterpart), the
frame condition at `⟨-72, [(.rbp, 0)]⟩`, the return address
`raT lab ".Lwc_main"`; wake's abort code is `SccCode.wake_abort`; the
assembly is a parameter `asm`, its cells `wakeCells` (`hwp`).
-/
import Spike.Lib.X64WakeRefAbW
import Spike.Lib.X64WakeRefAb
import Spike.Lib.X64WakeRefPh

namespace Spike.Lib.X64.WakeRefAbSt

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region PlaceWX)
open Spike.Lib.X64 (DFrame CKept Abs)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (lo)
open SccCode (wakeCells)
open Spike.Lib.X64.WakeRefStub (RefAbSt callee_of_pre)
open Spike.Lib.X64.WakeRefAbW (lab_ne labNe)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`RefAbSt`**: `AbSt` at every node of the threads abort path. -/
theorem refAbSt {asm : Asm} (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = lo) (l : WeakMem.AllocLabel) (b : Nat) : RefAbSt hp i l b := by
  intro R m0 cP cA mT m1 σC c0 hpre _
  obtain ⟨hR', hlo', hhi'⟩ := callee_of_pre hp i hpre
  have hprog := Spike.Lib.X64.WakeSrcCtl.prog_W hp i hpa hwp
  have hlo := Spike.Lib.X64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hlab := Spike.Lib.X64WakeOAb.hlab_W hp i hpa hwp hlo0
  have hsite := Spike.Lib.X64.WakePh.siteW hprog hlo hlab
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName := PlaceWX.abortLbl_of_placeWX (PlaceWX.link i hp)
  have h := Spike.Lib.X64.WakeWf.tpathW_ab (F := fun m => DFrame R m0 m ∧ CKept R (-72 - 8) (-24) 16 m1 m ∧
      Abs R ⟨-72, [(.rbp, 0)]⟩ m1 σC) (c0 := c0)
    (ra := Spike.Lib.X64.ThreadsAb.raT (_root_.Executable.labels (Ly).exe).label ".Lwc_main")
    (Spike.Lib.X64.WakePh.instOk2bP hprog hlo (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) (rS := ⟨0, 0⟩) hsite)
    (hprog ▸ SccCode.wake_abort) (Spike.Lib.X64.WakePh.abortPhTW hΛ hlab) hlab hR' (by omega) (by omega)
    (by rw [hsite]; rintro a ⟨⟩
        exact lab_ne hlab (by unfold labNe; rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel))
  have e : (Ly).endPc = Spike.Lib.X64.WakeH1Inv.endR hp i := by
    show Scc.Cert.Rt.X64.endOf (Ly).exe (Ly).prog (Ly).pfx = _; rw [hprog]
  rw [e] at h
  exact h

end Spike.Lib.X64.WakeRefAbSt

/-- info: 'Spike.Lib.X64.WakeRefAbSt.refAbSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefAbSt.refAbSt
