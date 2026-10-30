/-
**`ownG` agrees with `own2b` along the threads abort path below main's
frame** (AArch64, wake.w): `WakeRefStub.RefAg`, from `abAgree2b` at `abPT` in
the callee's region, the return address `raT` being `.L21_wc_main.sp11`.

- `raT_sp11`: the return address of the refusal's call is `sp11`'s.
- `callee80`: the callee's region at `-80` of a `Pre` region is `abPT`'s.
- `refAg`: `RefAg`.
-/
import Spike.Lib.A64WakeRefStub

namespace Spike.Lib.WakeRefStub

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (Region)
open Spike.Lib.A64.Flow (DFrame CKept Abs)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (oP)
open Spike.Lib.WakeRefTP (TPathW)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.ThreadsAb (raT)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Scc.Cert.Rt.A64 (codeT_eq)
open Scc.Cert.Link.A64 (codeOf)

/-- **The return address of the refusal's call is `sp11`'s**: `raT` is
`.1_spawnfail5 + 8`, the instruction after the call. -/
theorem raT_sp11 {L : RuntimeLayout}
    (hlab : ∀ l x, codeOf Spike.Lib.A64.WakePh.lo wakeProg l = some x → L.lab l = Int64.ofNat x) :
    raT L.lab pfxM = (L.lab ".L21_wc_main.sp11").toBitVec := by
  have h5 : L.lab (pfxM ++ ".1_spawnfail5") = Int64.ofNat 2169376 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have h11 : L.lab ".L21_wc_main.sp11" = Int64.ofNat 2169384 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  unfold raT
  rw [h5, h11]
  decide

/-- **The callee's region at `-80`** of a region of `RefObl`'s shape is
`OK`, 16-aligned, with offsets `[-48, 0]`. -/
theorem callee80 {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -336) (hhi : 0 ≤ R.hi) :
    (R.callee (-80) (-48) 0).OK ∧ (R.callee (-80) (-48) 0).base.toNat % 16 = 0 ∧
      (R.callee (-80) (-48) 0).lo ≤ -48 ∧ 0 ≤ (R.callee (-80) (-48) 0).hi := by
  have hkc : (-80 : Int) < R.hi := by omega
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ -80 + -48 by omega) (by decide) hkc
  refine ⟨Region.callee_ok hR (by omega) (by decide) hkc (by omega), ?_, by simp [Region.callee],
    by simp [Region.callee]⟩
  have : (((R.callee (-80) (-48) 0).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
  omega

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **`RefAg`**: `abAgree2b` at `abPT` in the callee's region (`callee80`),
the take site below `scc_rt_abort`, wake's abort code laid out. -/
theorem refAg (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    (l : WeakMem.AllocLabel) (b : Nat) : RefAg hp i l b := by
  intro R m0 cP cA mT m1 σC c0 hpre _
  obtain ⟨-, -, -, hR, hal, hlo', hhi, -⟩ := hpre
  obtain ⟨hR', hal', hlo'', hhi'⟩ := callee80 hR hal hlo' hhi
  have hlab := Spike.Lib.WakeOAb.hlab_W hp i hpa hwp hlo
  have hlays : Scc.Cert.Rt.A64.Lays (Ly).exe wakeProg (Ly).pfx := by
    rw [← Spike.Lib.WakeSrcCtl.prog_W hp i hpa hwp]; exact (Ly).lays
  have hsd := Spike.Lib.A64.WakePh.abortIn_wakeR
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  obtain ⟨e1, -⟩ := Spike.Lib.A64.WakePh.ab_labs hlab
  have hst : (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL = Int64.ofNat 2165940 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have hP := Spike.Lib.A64.WakePh.abPT (μ := Spike.Lib.A64.PhRec.μ (Ly))
    (F := fun m => DFrame R m0 m ∧ CKept R (-80) (-48) 0 m1 m ∧ Abs R oP m1 σC) (c0 := c0)
    (ra := ((Ly).lab ".L21_wc_main.sp11").toBitVec) hlab hR' hal' hlo'' hhi'
    (fun a ha => by
      rw [Spike.Lib.PlaceW.site_ofPlaceW hp i] at ha
      cases ha
      left
      rw [hst, e1]
      decide)
    (Scc.Cert.Rt.A64.Abort.code_disp hlays rfl hsd.2)
    (Scc.Cert.Rt.A64.Abort.code_stubs hlays rfl Spike.Lib.A64.WakePh.abortIn_wakeR .threads)
  have hA := TPathW.ofAgree (Spike.Lib.A64.WakePh.abAgree2b (a := Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) hlab hP)
  rw [raT_sp11 hlab]
  exact hA

end Inst

end Spike.Lib.WakeRefStub

/-- info: 'Spike.Lib.WakeRefStub.refAg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRefStub.refAg
