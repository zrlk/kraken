/-
**`SFactsAC` along the threads abort path below main's frame** (AArch64,
wake.w): `WakeRefStub.RefAC`, from `StubW.stubTW_sfactsAC` at the instance
`WakePh.instOk2bP` (`own2b` through `ph2b`), the path's phase check
`WakePh.abortPhTW`, in the callee's region at `-80` (`callee80`).

- `refAC`: `RefAC`, for a label `l` fresh in the start's labels.
-/
import Spike.Lib.A64WakeRefAg

namespace Spike.Lib.WakeRefStub

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (Region)
open Spike.Lib.A64.Flow (DFrame CKept Abs NodeW)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (oP)
open Spike.Lib.WakeRefTP (TPathW)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.ThreadsAb (raT)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Scc.Cert.Rt.A64 (codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Cert.Rt.A64.Print (add4 add0)
open Spike.Lib.A64Consumer (Lsize)
open Spike.Lib.WakeSpawnR (endR)

/-- A memory side with the kernel `abi`, every state an abort site (the
memory side `stubTW_sfactsAC` reads only through `K` and `abortAt`). -/
def msT : Spike.Lib.MemSide isaLSE2 where
  rd _ := True
  rt _ := True
  K := some abi
  G _ _ := True
  heap := 0
  ctr := 0
  units _ _ := 0
  off _ _ := 0
  cells := 0
  abortAt _ := True

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **`RefAC`**: `stubTW_sfactsAC` at `instOk2bP` with the empty take range
`rSW`, the phase check `abortPhTW`, the source placed by `placedSE_stub`
(main's slots kept by the callee), the `write` call's tail `DtW` (`x0 = 2`),
for `l` fresh in the start's labels (`hl`). -/
theorem refAC (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    (ls0 : Lsize) {l : WeakMem.AllocLabel} {b : Nat} (n : Nat)
    (hl : Spike.Lib.WakeLoadT.L0T (Ly).Λ l = none) : RefAC hp i ls0 l b n := by
  intro R m0 cP cA mT m1 σC c0 hpre hE
  obtain ⟨hsrc, hcA, hmT, hR, hal, hlo', hhi, -⟩ := hpre
  obtain ⟨hR', hal', hlo'', hhi'⟩ := callee80 hR hal hlo' hhi
  have hkc : (-80 : Int) < R.hi := by omega
  have hpW := Spike.Lib.WakeSrcCtl.prog_W hp i hpa hwp
  have hlab := Spike.Lib.WakeOAb.hlab_W hp i hpa hwp hlo
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hp)
  have hEnd : endR hp i = (Ly).endPc := by
    simp only [endR, RuntimeLayout.endPc, hpW]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e16⟩ := Spike.Lib.A64.WakePh.ab_labs hlab
  have hex : (Ly).lab Spike.Lib.A64.Abort.threads.exit = Int64.ofNat 2168548 := e16
  have hst : (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL = Int64.ofNat 2165940 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have hI := Spike.Lib.A64.WakePh.instOk2bP hpW hlo (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab)
    (Spike.Lib.PlaceW.site_ofPlaceW hp i) (rS := rSW hp i)
  have hprog : Scc.Cert.Rt.A64.Abort.abortIn (Ly).prog = true := by
    rw [hpW]; exact Spike.Lib.A64.WakePh.abortIn_wakeR
  have hphs := Spike.Lib.A64.WakePh.abortPhTW hΛ hlab
  have hF := Spike.Lib.A64.Flow.fstable_enter (kc := -80) (lo' := -48) (hi' := 0) (o := oP) (m0 := m1) (σC := σC) hR
    (Spike.Lib.A64.Flow.FStable.dframe R m0) (by omega) (by decide) hkc (by decide) (by decide) (by decide)
    (by decide)
  have hsub : (rSW hp i).Sub (Ly).Λ.stackPool := ⟨Nat.le_refl _, by simp [rSW]⟩
  have hfit : (rSW hp i).lo + (rSW hp i).size ≤ 2 ^ 64 := by
    have := (Ly).pool_fit; simp only [rSW]; omega
  have hFO : ∀ m, (fun m => DFrame R m0 m ∧ CKept R (-80) (-48) 0 m1 m ∧ Abs R oP m1 σC) m →
      Spike.Lib.A64.Flow.Ret0.StackOff (rSW hp i) (R.callee (-80) (-48) 0) m := by
    intro m _ a _ ha
    simp only [rSW, Scc.Sem.Range.contains] at ha
    omega
  obtain ⟨hlc, hlm⟩ := Spike.Lib.WakeRefSeg.lbl_of_toNat hl hcA hmT
  have hctl := Spike.Lib.WakeSrcCtl.spawnSrc_ctl hsrc
  have hc0 : c0 = cP := hE.1
  have hc : Spike.Lib.A64.StubW.RefCtl (Ly).Λ Spike.Lib.WakeT1.wakeSrc (fun s _ => ownW hp i s)
      (Spike.Lib.A64ConsumerA.upd (Spike.Lib.WakeLoadT.L0T (Ly).Λ) l b)
      (fun m => DFrame R m0 m ∧ CKept R (-80) (-48) 0 m1 m ∧ Abs R oP m1 σC) c0 [] := {
    noRet := fun _ => hc0 ▸ hctl.1,
    cell := hc0 ▸ hctl.2.cell,
    place := fun s hFs => Spike.Lib.WakeSrcCtl.placedSE_stub hsrc hR (by omega) hhi hE hFs
      (Spike.Lib.A64.Flow.DFrame.refl _ _) rfl hlc hlm,
    runOut := fun _ _ _ _ => rfl,
    runIn := fun _ _ _ _ => rfl,
    zero := hc0 ▸ hctl.2.zero }
  -- The phase facts of the stub's `svc`.
  have hsd := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hstb := hsd.1.2
  simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hstb
  obtain ⟨-, -, -, -, hsvcIn, -⟩ := hstb
  have hph := hphs
  simp only [Spike.Lib.A64.StubW.abortPhThreadsOk, Spike.Lib.A64.StubW.phOne, Bool.and_eq_true, beq_iff_eq,
    and_assoc] at hph
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, o7, q7, -⟩ := hph
  have hR8 : (R.callee (-80) (-48) 0).base.toNat % 8 = 0 := by omega
  have hl8 : (R.callee (-80) (-48) 0).lo % 8 = 0 := by simp [Region.callee]
  have hh8 : (R.callee (-80) (-48) 0).hi % 8 = 0 := by simp [Region.callee]
  have he7 : (Ly).lab Spike.Lib.A64.Abort.threads.entry + Int64.ofNat (4 * 7) =
      (Spike.Lib.A64.Abort.NT (Ly).lab Spike.Lib.A64.Abort.threads c0 (raT (Ly).lab pfxM) .svc).pc := by
    simp only [Spike.Lib.A64.Abort.NT, Spike.Lib.A64.Abort.pcSvc, add4, add0]
  have hsvcT : NodeW (fun s c => ACW hp i ls0 l b n s c) (Spike.Lib.A64.PhRec.K (Ly) (rSW hp i)) (Ly).exe
      (Ly).endPc (R.callee (-80) (-48) 0)
      (fun m => DFrame R m0 m ∧ CKept R (-80) (-48) 0 m1 m ∧ Abs R oP m1 σC)
      (Spike.Lib.A64.Abort.NT (Ly).lab Spike.Lib.A64.Abort.threads c0 (raT (Ly).lab pfxM) .svc) := by
    intro s c hAt
    obtain ⟨hs, hn, -, hpc, σ, hA, hD, hJ, h0, h8⟩ := id hAt
    have hcc : c = c0 := hJ.1
    subst hcc
    have hAc : Spike.Lib.A64.ThreadsAb.Ac (Ly).lab pfxM s :=
      Spike.Lib.A64.StubW.ac_stubA (by rw [hpc]; exact Spike.Lib.A64ConsumerA.ThreadsAcSt.memSvcT) hA hJ.2
    rw [← he7] at hpc
    have hP := hI.off s (by unfold pcOf; rw [hpc]; exact o7)
    have hown := Spike.Lib.A64.Rt.owned_off hR' hR8 hl8 hh8 hsub (hFO _ hD) fun k hk => by
      obtain ⟨j, hj, -⟩ := hA.slot k hk
      rw [hj]; rfl
    exact ⟨Spike.Lib.A64.StubW.sfactsAC_svcT hc (hc.place s hD) hP.1.noSite hP.1.noTake
      (Spike.Lib.A64.Rt.cellOf hI hsvcIn rfl hs hn hpc) (Spike.Lib.A64.Rt.next_same hI hpc q7) (fun _ => hown)
      (fun k a ha e => (hP.1.noAbort k a ha e).elim)
      (fun _ _ _ _ => Spike.Lib.A64.WakeWf.dtW_of_fd2 (by rw [hA.regs]; exact h0) (by rw [hA.regs]; exact h8))
      hAc (fun h => h.2), hP.2⟩
  have hT := Spike.Lib.A64.StubW.stubTW_sfactsAC (own := fun s _ => ownW hp i s) (frs := [])
    (Dt := Spike.Lib.A64.WakeWf.DtW) (pfx := pfxM) (Cl := WakeOD.ClW hp i) (p := Spike.Lib.WakeT1.wakeSrc)
    (rd := fun _ => True) (G := fun _ _ => True) (ar := WakeOD.arW hp i) (J := fun _ _ _ _ _ => False)
    (lsize := Spike.Lib.A64ConsumerA.updN (Spike.Lib.WakeLoadT.ls0T ls0) l n) (al := fun _ => none)
    (ms := msT)
    hI hprog hphs hR' hal' hlo'' hhi' hl8 hh8 hF hsub hfit hFO hc (fun s h => h.2)
    (fun a ha => by
      have e : (Spike.Lib.A64.PhRec.μ (Ly)).site .release = some 2165996 := by
        show codeOf Λ0.code.lo (Ly).prog "scc_rt_release_site" = _
        rw [hpW, hlo, ← codeT_eq]; decide +kernel
      rw [e] at ha; cases ha; rw [hex]; decide)
    (fun a ha => by
      rw [Spike.Lib.PlaceW.site_ofPlaceW hp i] at ha
      cases ha; rw [hex, hst]; decide)
    (fun k a ha => by
      have e : (Spike.Lib.A64.PhRec.μ (Ly)).abortAt k = codeOf Spike.Lib.A64.WakePh.lo wakeProg
          (Scc.Cert.Link.abortName k) := by
        show codeOf Λ0.code.lo (Ly).prog ((Ly).Λ.abortLbl k) = _
        rw [hpW, hlo, hΛ]
      rw [e, ← codeT_eq] at ha; rw [hex]
      cases k <;> first | (intro; rfl) | (rintro rfl; revert ha; decide +kernel))
    (fun s s' hpc hK => by
      have h1 : s.st.2 = _ := hK.1
      unfold pcOf at hpc
      rw [h1, hst, hex] at hpc
      exact absurd hpc (by decide))
    (fun _ _ _ => trivial) rfl
    (fun s c hAt => by
      obtain ⟨-, -, -, -, σ, hA, -, -, h0, h8⟩ := hAt
      exact Spike.Lib.A64.WakeWf.dtW_of_fd2 (by rw [hA.regs]; exact h0) (by rw [hA.regs]; exact h8))
  rw [hEnd]
  exact TPathW.ofStub hT hsvcT

end Inst

end Spike.Lib.WakeRefStub

/-- info: 'Spike.Lib.WakeRefStub.refAC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRefStub.refAC
