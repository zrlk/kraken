/-
**`SFactsAC` along the threads abort path below main's frame** (x86-64,
wake.w; the twin of `Spike/Lib/A64WakeRefAC.lean`): `X64WakeRefStub.RefAC`,
from `X64.StubW.stubTW_sfactsAC` at the instance `WakePh.instOk2bP`
(`own2b` through `ph2b`), the path's phase check `WakePh.abortPhTW`, in the
callee's region (`callee_of_pre`), with the `write` call's node built here
(as `stubTW_sfactsAC`'s own `hsysT`).

- `msT`: a memory side with the kernel `abi`, every state an abort site.
- `refAC`: `RefAC`, for a label `l` fresh in the start's labels.

**Where this differs from AArch64**: the callee's region is
`R.callee (-72 - 8) (-24) 16` at the frame condition `⟨-72, [(.rbp, 0)]⟩`,
its base 8-aligned from stack 0's 16-aligned top (`stacks_al`) rather than
from a `Pre` alignment conjunct; the `write` call is the stub's `syscall`
at `entry + 34` with `%rdi = 2`, `%rax = 1` (`dtW_of_fd2` on `UInt64`s);
its `Ac` membership needs the return address's position (`RaPos`, the
`raBPcs` class); the threads exit is at `4202965`, the release and take
sites at `4200317`, `4200277`; the parses are on `cellsOf asm`.
-/
import Spike.Lib.X64WakeRefLay
import Spike.Lib.X64WakeRefPh
import Spike.Lib.X64StubTAC

namespace Spike.Lib.X64.WakeRefStub

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region PlaceWX)
open Spike.Lib.X64 (DFrame CKept Abs NodeW)
open Spike.Lib.X64.WakeRefTP (TPathW)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.ThreadsAb (raT)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64.WakeH1Inv (endR)
open Scc.Cert.Rt.X64 (codeT_eq)
open SccCode (wakeCells)

/-- A memory side with the kernel `abi`, every state an abort site (the
memory side `stubTW_sfactsAC` reads only through `K` and `abortAt`). -/
def msT : Spike.Lib.MemSide isa where
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

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`RefAC`**: `stubTW_sfactsAC` at `instOk2bP` with the empty take range
`rSW`, the phase check `abortPhTW`, the source placed by `placedSE_stub`
(main's slots kept by the callee), the `write` call's tail `DtW`
(`%rdi = 2`, `%rax = 1`), for `l` fresh in the start's labels (`hl`). -/
theorem refAC {asm : Asm} (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (ls0 : Lsize) {l : WeakMem.AllocLabel} {b : Nat} (n : Nat)
    (hl : Spike.Lib.X64WakeLoadT.L0T (Ly).Λ l = none) : RefAC hp i ls0 l b n := by
  intro R m0 cP cA mT m1 σC c0 hpre hE
  obtain ⟨hR', hlo'', hhi''⟩ := callee_of_pre hp i hpre
  obtain ⟨hsrc, hcA, hmT, hR, hlo', hhi, hst0⟩ := hpre
  have hkc : (-72 - 8 : Int) < R.hi := by omega
  have hpW := Spike.Lib.X64.WakeSrcCtl.prog_W hp i hpa hwp
  have hlab := Spike.Lib.X64WakeOAb.hlab_W hp i hpa hwp hlo
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link i hp)
  have hEnd : endR hp i = (Ly).endPc := (endR_eq hp i hpa hwp).symm
  have hex : (Ly).lab Spike.Lib.X64.Abort.threads.exit = Int64.ofNat 4202965 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have hst : (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200277 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have hI := Spike.Lib.X64.WakePh.instOk2bP hpW hlo (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)
    (Spike.Lib.PlaceWX.site_ofPlaceWX hp i) (rS := rSW hp i)
  have hprog : Scc.Cert.Rt.X64.Abort.abortIn (Ly).prog = true := by
    rw [hpW]; exact SccCode.wake_abort
  have hphs := Spike.Lib.X64.WakePh.abortPhTW hΛ hlab
  have hF := Spike.Lib.X64.fstable_enter (kb := -72 - 8) (lo' := -24) (hi' := 16) (o := ⟨-72, [(.rbp, 0)]⟩)
    (m0 := m1) (σC := σC) hR (Spike.Lib.X64.FStable.dframe R m0) (by omega) (by decide) hkc (by omega)
    (by decide) (by decide) (by decide)
  have hsub : (rSW hp i).Sub (Ly).Λ.stackPool := ⟨Nat.le_refl _, by simp [rSW]⟩
  have hfit : (rSW hp i).lo + (rSW hp i).size ≤ 2 ^ 64 := by
    have := (Ly).pool_fit; simp only [rSW]; omega
  have hFO : ∀ m, (fun m => DFrame R m0 m ∧ CKept R (-72 - 8) (-24) 16 m1 m ∧ Abs R ⟨-72, [(.rbp, 0)]⟩ m1 σC) m →
      Spike.Lib.X64.Flow.Ret0.StackOff (rSW hp i) (R.callee (-72 - 8) (-24) 16) m := by
    intro m _ a _ ha
    simp only [rSW, Scc.Sem.Range.contains] at ha
    omega
  -- The callee's base is 8-aligned: `R`'s base is stack 0's 16-aligned top less `64`.
  have hR8 : (R.callee (-72 - 8) (-24) 16).base.toNat % 8 = 0 := by
    have hb := Region.callee_base (hi' := 16) hR (show R.lo ≤ -72 - 8 + -24 by omega) (by decide) hkc
    have hal := (Ly).stacks_al
    have : (((R.callee (-72 - 8) (-24) 16).base.toNat : Int)) % 8 = 0 := by rw [hb]; omega
    omega
  have hl8 : (R.callee (-72 - 8) (-24) 16).lo % 8 = 0 := by simp [Region.callee]
  have hh8 : (R.callee (-72 - 8) (-24) 16).hi % 8 = 0 := by simp [Region.callee]
  obtain ⟨hlc, hlm⟩ := Spike.Lib.X64.WakeRefSeg.lbl_of_toNat hl hcA hmT
  have hctl := Spike.Lib.X64.WakeSrcCtl.spawnSrc_ctl hsrc
  have hc0 : c0 = cP := hE.1
  have hc : Spike.Lib.X64.StubW.RefCtl (Ly).Λ Spike.Lib.X64WakeT1.wakeSrc (fun s _ => ownW hp i s)
      (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b)
      (fun m => DFrame R m0 m ∧ CKept R (-72 - 8) (-24) 16 m1 m ∧ Abs R ⟨-72, [(.rbp, 0)]⟩ m1 σC) c0 [] := {
    noRet := fun _ => hc0 ▸ hctl.1,
    cell := hc0 ▸ hctl.2.cell,
    place := fun s hFs => Spike.Lib.X64.WakeSrcCtl.placedSE_stub hsrc hR (by omega) hhi hE hFs
      (Spike.Lib.X64.DFrame.refl _ _) rfl hlc hlm,
    runOut := fun _ _ _ _ => rfl,
    runIn := fun _ _ _ _ => rfl,
    zero := hc0 ▸ hctl.2.zero }
  -- The `write` call's node (`stubTW_sfactsAC`'s `hsysT`, at this instance).
  have hsd := hprog
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hstb := hsd.1.2
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hstb
  obtain ⟨-, -, -, hsysIn, -⟩ := hstb
  have hph := hphs
  simp only [Spike.Lib.X64.StubW.abortPhThreadsOk, Spike.Lib.X64.StubW.phOne, Bool.and_eq_true, beq_iff_eq,
    and_assoc] at hph
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, o34, q34, -⟩ := hph
  have hoff8 : (R.callee (-72 - 8) (-24) 16).Off 8 := ⟨by decide, by simp [Region.callee], by simp [Region.callee]⟩
  have he34 : (Ly).lab Spike.Lib.X64.Abort.threads.entry + Int64.ofNat 34 =
      (Spike.Lib.X64.Abort.NT (Ly).lab Spike.Lib.X64.Abort.threads c0 (raT (Ly).lab ".Lwc_main") .sys).pc := rfl
  have hsysT : NodeW (fun s c => ACW hp i ls0 l b n s c) (Spike.Lib.X64.PhRec.K (Ly) (rSW hp i)) (Ly).exe
      (Ly).endPc (R.callee (-72 - 8) (-24) 16)
      (fun m => DFrame R m0 m ∧ CKept R (-72 - 8) (-24) 16 m1 m ∧ Abs R ⟨-72, [(.rbp, 0)]⟩ m1 σC)
      (Spike.Lib.X64.Abort.NT (Ly).lab Spike.Lib.X64.Abort.threads c0 (raT (Ly).lab ".Lwc_main") .sys) := by
    intro s c hAt
    obtain ⟨hs, hn, -, hpc, σ, hA, hD, hJ, h0, h1⟩ := id hAt
    have hcc : c = c0 := hJ.1
    subst hcc
    have hAc : Spike.Lib.X64.ThreadsAb.Ac (Ly).lab ".Lwc_main" s :=
      Spike.Lib.X64.StubW.ac_stubA (by rw [hpc]; exact Spike.Lib.X64ConsumerA.ThreadsAcSt.memSysT.1) hA hoff8
        (.inr (.inr ⟨by rw [hpc]; exact Spike.Lib.X64ConsumerA.ThreadsAcSt.memSysT.2, rfl⟩)) hJ.2
    rw [← he34] at hpc
    have hP := hI.off s (by unfold pcOf; rw [hpc]; exact o34)
    have hown := Spike.Lib.X64.Rt.owned_off hR' hR8 hl8 hh8 hsub (hFO _ hD) fun k hk => by
      obtain ⟨j, hj, -⟩ := hA.slot k hk
      rw [hj]; rfl
    rw [← hA.regs] at h0 h1
    exact ⟨Spike.Lib.X64.StubW.sfactsAC_svcT hc (hc.place s hD) hP.1.noSite hP.1.noTake
      (Spike.Lib.X64.Rt.cellOf hI hsysIn rfl hs hn hpc) (Spike.Lib.X64.Rt.next_same hI hpc q34) (fun _ => hown)
      (fun k a ha e => (hP.1.noAbort k a ha e).elim)
      (fun _ _ _ _ => Spike.Lib.X64.WakeWf.dtW_of_fd2 (UInt64.toBitVec_inj.mp h0) (UInt64.toBitVec_inj.mp h1))
      hAc (fun h => h.2), hP.2⟩
  have hT := Spike.Lib.X64.StubW.stubTW_sfactsAC (own := fun s _ => ownW hp i s) (frs := [])
    (Dt := Spike.Lib.X64.WakeWf.DtW) (pfx := ".Lwc_main") (Cl := Spike.Lib.X64.WakeOD.ClW hp i)
    (p := Spike.Lib.X64WakeT1.wakeSrc) (rd := fun _ => True) (G := fun _ _ => True)
    (ar := Spike.Lib.X64.WakeOD.arW hp i) (J := fun _ _ _ _ _ => False)
    (lsize := Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls0) l n) (al := fun _ => none)
    (ms := msT)
    hI hprog hphs hR' hR8 (by omega) (by omega) hl8 hh8 hF hsub hfit hFO hc (fun s h => h.2)
    (fun a ha => by
      have e : (Spike.Lib.X64.PhRec.μ (Ly)).site .release = some 4200317 := by
        show codeLabel Λ0.code.lo (Ly).prog "scc_rt_release_site" = _
        rw [hpW, hlo, ← codeT_eq]; decide +kernel
      rw [e] at ha; cases ha; rw [hex]; decide)
    (fun a ha => by
      rw [Spike.Lib.PlaceWX.site_ofPlaceWX hp i] at ha
      cases ha; rw [hex, hst]; decide)
    (fun k a ha => by
      have e : (Spike.Lib.X64.PhRec.μ (Ly)).abortAt k = codeLabel Spike.Lib.X64.WakePh.lo wakeCells
          (Scc.Cert.Link.abortName k) := by
        show codeLabel Λ0.code.lo (Ly).prog ((Ly).Λ.abortLbl k) = _
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
      obtain ⟨-, -, -, -, σ, hA, -, -, h0, h1⟩ := hAt
      rw [← hA.regs] at h0 h1
      exact Spike.Lib.X64.WakeWf.dtW_of_fd2 (UInt64.toBitVec_inj.mp h0) (UInt64.toBitVec_inj.mp h1))
  rw [hEnd]
  exact TPathW.ofStub hT hsysT

end Inst

end Spike.Lib.X64.WakeRefStub

/-- info: 'Spike.Lib.X64.WakeRefStub.refAC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.refAC
