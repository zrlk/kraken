/-
**`RefAbSt`: the write abort's phase kept along the threads abort path**
(AArch64, wake.w): `WakeWf.tpathW_ab` at the second `scc_rt_thread_init`
instance's facts (`instOk2bP`: `own2b` at `ph2b`), `ph2b`'s phase facts on
the path (`abortPhTW`), the take site off the threads stub's exit call
(`lab_ne`), in `TObl`'s region (`callee_of_pre`).

- `refAbSt`: the piece.
-/
import Spike.Lib.A64WakeRefAbW

namespace Spike.Lib.WakeRefAbSt

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (Region)
open Spike.Lib.A64.Flow (DFrame CKept Abs)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WakeRefStub (RefAbSt)
open Spike.Lib.WakeRefAbW (callee_of_pre lab_ne labNe)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **`RefAbSt`**: `AbSt` at every node of the threads abort path. -/
theorem refAbSt (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = lo)
    (l : WeakMem.AllocLabel) (b : Nat) : RefAbSt hp i l b := by
  intro R m0 cP cA mT m1 σC c0 hpre _
  obtain ⟨hR', hal'⟩ := callee_of_pre hp i hpre
  have hprog := Spike.Lib.WakeSrcCtl.prog_W hp i hpa hwp
  have hlo := Spike.Lib.A64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hlab := Spike.Lib.WakeOAb.hlab_W hp i hpa hwp hlo0
  have hsite := Spike.Lib.A64.WakePh.siteW hprog hlo hlab
  have hΛ := Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hp)
  have h := Spike.Lib.A64.WakeWf.tpathW_ab (F := fun m => DFrame R m0 m ∧ CKept R (-80) (-48) 0 m1 m ∧
      Abs R Spike.Lib.A64.Flow.Worker.Wake.Parent.oP m1 σC) (c0 := c0)
    (ra := Spike.Lib.A64.ThreadsAb.raT (_root_.Executable.labels (Ly).exe).label
      Spike.Lib.A64.Flow.Worker.Wake.Child.pfxM)
    (Spike.Lib.A64.WakePh.instOk2bP hprog hlo (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (rS := ⟨0, 0⟩) hsite)
    (hprog ▸ Spike.Lib.A64.WakePh.abortIn_wakeR) (Spike.Lib.A64.WakePh.abortPhTW hΛ hlab) hlab hR' hal'
    (by simp [Region.callee]) (by simp [Region.callee])
    (by rw [hsite]; rintro a ⟨⟩
        exact lab_ne hlab (by unfold labNe; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel))
  have e : (Ly).endPc = Spike.Lib.WakeSpawnR.endR hp i := by
    show Scc.Cert.Rt.A64.endOf (Ly).exe (Ly).prog (Ly).pfx = _; rw [hprog]
  rw [e] at h
  exact h

end Spike.Lib.WakeRefAbSt

/-- info: 'Spike.Lib.WakeRefAbSt.refAbSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRefAbSt.refAbSt
