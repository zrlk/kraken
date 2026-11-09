/-
**`SFactsAC` along hello.w's threads abort path below main's frame** (AArch64; part 4;
the hello twin of wake's `A64WakeRefAC`): `RefO.ACH`, from `Hello.StubW.stubTW_sfactsACG` at the
instance `instOk2bPH` (`own2bH` through `ph2bH`), the path's phase check `abortPhTH`, in the callee's region at
`-144` (`callee144`), the `write` call's node (`hsvcT`) as wake's, joined by `TPathW.ofStub`.

The source is placed off main's slots (`placedSE_stubH`, wake's `WakeSrcCtl.placedSE_stub`): `spawnTermH` reads
`c` and `p = ws ++ [c, me]`, so all five packet words are read at the slots `MSS` names (`-144`, `-128`, `-120`,
`-104`, `-112`), which the callee keeps (`placeVal_slot_kept144`); `PreH` places the slice's words (`SlRep`), the
box and main's thread id.

- `msTH`: a memory side with the kernel `abi`, every state an abort site (wake's `msT`).
- `placeVal_slot_kept144`: a slot of main's frame at or above `-144` read through the callee's frame.
- `placedSE_stubH`: the source placed at every state of the path.
- `refACH`: `ACH`.

No absolute address appears in a statement here.
-/
import Spike.Lib.A64HelloRefAb
import Spike.Lib.A64HelloStubTAC
import Spike.Lib.A64HelloSpawnPl

namespace Spike.Lib.A64.HelloPh.RefO

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (Region FragS Arena)
open Spike.Lib.A64.Flow (NodeW)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib.A64.Flow.Worker.Hello.Parent (oP)
open Spike.Lib.A64.Flow.Worker.Hello.SpawnFail (fES MSS)
open Spike.Lib.WakeRefTP (TPathW)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.ThreadsAb (raT)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH SlRep)
open Scc.Cert.Rt.A64 (codeT_eq)
open Scc.Cert.Rt.A64.Print (add4 add0)
open Scc.Cert.Link.A64 (codeOf)

/-- A memory side with the kernel `abi`, every state an abort site (the memory side `stubTW_sfactsACG` reads only
through `K` and `abortAt`; wake's `WakeRefStub.msT`). -/
def msTH : Spike.Lib.MemSide isaLSE2 where
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

/-- **A slot of main's frame at or above `-144`** read through the callee's frame at `-144` (offsets `[-48, 0]`):
the caller's abstract value (wake's `WakeSrcCtl.placeVal_slot_kept` at hello's frame). -/
theorem placeVal_slot_kept144 {R : Region} {o : Spike.Lib.A64.Flow.SO} {m1 m' : MachineData}
    {σC : Spike.Lib.A64.Flow.AS} {s : State} (hA : Spike.Lib.A64.Flow.Abs R o m1 σC)
    (hK : Spike.Lib.A64.Flow.CKept R (-144) (-48) 0 m1 m')
    (hD : Spike.Lib.A64.Flow.DFrame (R.callee (-144) (-48) 0) m' s.st.1) (hR : R.OK) (hlo : R.lo ≤ -144)
    (hhi : 0 ≤ R.hi) {k : Int} (hk : R.Off k) (hk' : -144 ≤ k) :
    placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σC.slot k).toNat := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  have hc : ¬ (R.callee (-144) (-48) 0).Off (k - -144) := fun ⟨_, _, h3⟩ => by
    simp only [Region.callee] at h3; omega
  have hf := Region.addr_toNat_of hR (k := -144) hlo (by omega)
  have hkn := R.addr_toNat hR hk
  have e := hD (R.addr k) (R.addr_fit hR hk) (.inr (by simp only [Region.callee]; omega))
  show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  simp [Scc.Sem.A64.privLoad, e, hK k hk hc, hj, hv]

/-- **main's source placed on the threads abort path** (wake's `WakeSrcCtl.placedSE_stub`): at the call `fES`'s
state `σC` (main's slots `MSS sl cA me`), in the callee's frame condition, the source `cP` at `SpawnSrcH l ws`
with the slice's words represented by `sl` (`hsl`), the box at `cA` (`hlc`) and main's id at `me` (`hlm`), is
placed at `lbl`. -/
theorem placedSE_stubH {Λ : Scc.Sem.Layout} {lbl : Lbl} {l : WeakMem.AllocLabel} {ws : List TermRun.Word}
    {cP c0 c : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {cA me : BitVec 64}
    {lab : Label → Int64} {R : Region} {m0 m1 m' : MachineData} {σC : Spike.Lib.A64.Flow.AS} {s : State}
    (hsrc : SpawnSrcH l ws cP) (hsl : SlRep lbl ws sl.1.toNat sl.2.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat)
    (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) (hE : (fES pfxM lab cP sl cA me).J σC c0)
    (hF : Spike.Lib.A64.Flow.DFrame R m0 m' ∧ Spike.Lib.A64.Flow.CKept R (-144) (-48) 0 m1 m' ∧
      Spike.Lib.A64.Flow.Abs R oP m1 σC)
    (hD : Spike.Lib.A64.Flow.DFrame (R.callee (-144) (-48) 0) m' s.st.1) (hc : c = c0)
    (hlc : lbl l = some cA.toNat) (hlm : lbl (Spike.Lib.WakeT1.mainTidLbl 2) = some me.toNat) :
    PlacedSE Λ lbl s c [] := by
  obtain ⟨hc0, -, -, h144, h128, h120, h104, h112⟩ := hE
  subst hc hc0
  have pv : ∀ k, k % 8 = 0 → -144 ≤ k → k ≤ -8 →
      placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σC.slot k).toNat := fun k h0 h1 h2 =>
    placeVal_slot_kept144 hF.2.2 hF.2.1 hD hR hlo hhi ⟨h0, by omega, by omega⟩ h1
  obtain ⟨lr, rfl, hl, -, e2, e3⟩ := hsl
  exact Spike.Lib.A64.HelloPh.SpawnPl.placedSE_spawnAtH _ _ _ _ _ hsrc
    ⟨_, pv (-144) (by decide) (by decide) (by decide), by decide, sl.1.toNat, by simp [Scc.Sem.wordAddr, hl], by
      rw [h144]; simp⟩
    ⟨_, pv (-128) (by decide) (by decide) (by decide), by decide, by rw [h128]; exact e2⟩
    ⟨_, pv (-120) (by decide) (by decide) (by decide), by decide, by rw [h120]; exact e3⟩
    ⟨_, pv (-104) (by decide) (by decide) (by decide), by rw [h104]; exact hlc⟩
    ⟨_, pv (-112) (by decide) (by decide) (by decide), by rw [h112]; exact hlm⟩

variable {L : RuntimeLayout} (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)

include hp hlo hlab hΛ in
/-- **`ACH`**: `stubTW_sfactsACG` at `instOk2bPH` with the empty take range `rSH`, the phase check `abortPhTH`, the
source placed by `placedSE_stubH`, the `write` call's tail `DtW` (`x0 = 2`), and the `write` call's node as wake's
`refAC`'s. -/
theorem refACH (lbl : Lbl) (l : WeakMem.AllocLabel) (ws : List TermRun.Word) (ar : Arena) (lsize : Lsize) :
    ACH L lbl l ws ar lsize := by
  intro R m0 cP sl cA me m1 σC c0 hpre hE
  obtain ⟨hsrc, hsl, hcA, hme, hR, hal, hlo', hhi, -⟩ := hpre
  obtain ⟨hR', hal', hlo'', hhi'⟩ := callee144 hR hal (by omega) hhi
  have hkc : (-144 : Int) < R.hi := by omega
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e16⟩ := ab_labsH hlab
  have hex : L.lab Spike.Lib.A64.Abort.threads.exit = Int64.ofNat 2168616 := e16
  have hst : L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL = Int64.ofNat 2165980 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have hI := instOk2bPH hp hlo (Spike.Lib.A64.Rt.Reserve.ntA L.lab) (siteH hp hlo hlab) (rS := rSH L)
  have hprog : Scc.Cert.Rt.A64.Abort.abortIn L.prog = true := by rw [hp]; exact SccCode.hello_abort
  have hphs := abortPhTH hΛ hlab
  have hF := Spike.Lib.A64.Flow.fstable_enter (kc := -144) (lo' := -48) (hi' := 0) (o := oP) (m0 := m1)
    (σC := σC) hR (Spike.Lib.A64.Flow.FStable.dframe R m0) (by omega) (by decide) hkc (by decide) (by decide)
    (by decide) (by decide)
  have hsub : (rSH L).Sub L.Λ.stackPool := ⟨Nat.le_refl _, by simp [rSH]⟩
  have hfit : (rSH L).lo + (rSH L).size ≤ 2 ^ 64 := by
    have := L.pool_fit; simp only [rSH]; omega
  have hFO : ∀ m, (fun m => Spike.Lib.A64.Flow.DFrame R m0 m ∧ Spike.Lib.A64.Flow.CKept R (-144) (-48) 0 m1 m ∧
      Spike.Lib.A64.Flow.Abs R oP m1 σC) m →
      Spike.Lib.A64.Flow.Ret0.StackOff (rSH L) (R.callee (-144) (-48) 0) m := by
    intro m _ a _ ha
    simp only [rSH, Scc.Sem.Range.contains] at ha
    omega
  have hctl := Spike.Lib.HelloH1A.spawnSrcH_ctl (p := Spike.Lib.HelloSrc.helloSrc) hsrc
  have hc0 : c0 = cP := hE.1
  have hc : Spike.Lib.A64.StubW.RefCtl L.Λ Spike.Lib.HelloSrc.helloSrc (fun s _ => ownWH L s) lbl
      (fun m => Spike.Lib.A64.Flow.DFrame R m0 m ∧ Spike.Lib.A64.Flow.CKept R (-144) (-48) 0 m1 m ∧
        Spike.Lib.A64.Flow.Abs R oP m1 σC) c0 [] := {
    noRet := fun _ => hc0 ▸ hctl.1,
    cell := hc0 ▸ hctl.2.cell,
    place := fun s hFs => placedSE_stubH hsrc hsl hR (by omega) hhi hE hFs
      (Spike.Lib.A64.Flow.DFrame.refl _ _) rfl hcA hme,
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
  have hR8 : (R.callee (-144) (-48) 0).base.toNat % 8 = 0 := by omega
  have hl8 : (R.callee (-144) (-48) 0).lo % 8 = 0 := by simp [Region.callee]
  have hh8 : (R.callee (-144) (-48) 0).hi % 8 = 0 := by simp [Region.callee]
  have he7 : L.lab Spike.Lib.A64.Abort.threads.entry + Int64.ofNat (4 * 7) =
      (Spike.Lib.A64.Abort.NT L.lab Spike.Lib.A64.Abort.threads c0 (raT L.lab pfxM) .svc).pc := by
    simp only [Spike.Lib.A64.Abort.NT, Spike.Lib.A64.Abort.pcSvc, add4, add0]
  have hsvcT : NodeW (fun s c => ACWH L lbl ar lsize s c) (Spike.Lib.A64.PhRec.K L (rSH L)) L.exe L.endPc
      (R.callee (-144) (-48) 0)
      (fun m => Spike.Lib.A64.Flow.DFrame R m0 m ∧ Spike.Lib.A64.Flow.CKept R (-144) (-48) 0 m1 m ∧
        Spike.Lib.A64.Flow.Abs R oP m1 σC)
      (Spike.Lib.A64.Abort.NT L.lab Spike.Lib.A64.Abort.threads c0 (raT L.lab pfxM) .svc) := by
    intro s c hAt
    obtain ⟨hs, hn, -, hpc, σ, hA, hD, hJ, h0, h8⟩ := id hAt
    have hcc : c = c0 := hJ.1
    subst hcc
    have hAc : Spike.Lib.A64.HelloWf.AcH L.lab pfxM s :=
      Spike.Lib.A64.Hello.StubW.ac_stubG (by rw [hpc]; exact Spike.Lib.A64ConsumerA.ThreadsAcSt.memSvcT) hA hJ.2
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
  have hT := Spike.Lib.A64.Hello.StubW.stubTW_sfactsACG (own := fun s _ => ownWH L s) (frs := [])
    (Dt := Spike.Lib.A64.WakeWf.DtW) (pfx := pfxM) (n := 25) (cl := ".clone13") (off := 112)
    (Cl := Spike.Lib.A64.HelloPh.ClH L) (p := Spike.Lib.HelloSrc.helloSrc)
    (rd := fun _ => True) (G := fun _ _ => True) (ar := ar) (J := fun _ _ _ _ _ => False)
    (lsize := lsize) (al := fun _ => none) (ms := msTH)
    hI hprog hphs hR' hal' hlo'' hhi' hl8 hh8 hF hsub hfit hFO hc (fun s h => h.2)
    (fun a ha => by
      have e : (Spike.Lib.A64.PhRec.μ L).site .release = some 2166036 := by
        show codeOf L.Λ.code.lo L.prog "scc_rt_release_site" = _
        rw [hp, hlo, ← codeT_eq]; decide +kernel
      rw [e] at ha; cases ha; rw [hex]; decide)
    (fun a ha => by
      rw [siteH hp hlo hlab] at ha
      cases ha; rw [hex, hst]; decide)
    (fun k a ha => by
      have e : (Spike.Lib.A64.PhRec.μ L).abortAt k = codeOf lo SccCode.helloProg (Scc.Cert.Link.abortName k) := by
        show codeOf L.Λ.code.lo L.prog (L.Λ.abortLbl k) = _
        rw [hp, hlo, hΛ]
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
  exact TPathW.ofStub hT hsvcT

end Spike.Lib.A64.HelloPh.RefO

/-- info: 'Spike.Lib.A64.HelloPh.RefO.placedSE_stubH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefO.placedSE_stubH

/-- info: 'Spike.Lib.A64.HelloPh.RefO.refACH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefO.refACH
