/-
**`SFactsAC` along hello.w's threads abort path below main's frame** (x86-64; the twin of
`Spike/Lib/A64HelloRefAC.lean`, the hello twin of wake's `X64WakeRefAC`): `RefO.ACH`, from
`Hello.StubW.stubTW_sfactsACG` at the instance `instOk2bPH` (`own2bH` through `ph2bH`), the path's phase check
`abortPhTH`, in the callee's region `R.callee (-136 - 8) (-24) 16` (`callee144`), the `write` call's node
(`hsysT`) as wake's, joined by `TPathW.ofStub`.

The source is placed off main's slots (`placedSE_stubH`, wake's `WakeSrcCtl.placedSE_stub`): `spawnTermH` reads
`c` and `p = ws ++ [c, me]`, so all five packet words are read at the slots `MSS` names (`-8`, `-24`, `-32`,
`-48`, `-40`), which the callee keeps (`placeVal_slot_kept144`); `PreH` places the slice's words (`SlRep`), the
box and main's thread id.

- `msTH`: a memory side with the kernel `abi`, every state an abort site (wake's `msT`).
- `placeVal_slot_kept144`: a slot of main's frame at or above `-128` read through the callee's frame.
- `placedSE_stubH`: the source placed at every state of the path.
- `refACH`: `ACH`.

No absolute address appears in a statement here.

## Differences from the AArch64 version

- The callee's region is `R.callee (-136 - 8) (-24) 16` at the frame condition `⟨-136, [(.rbp, 0)]⟩`
  (AArch64: `R.callee (-144) (-48) 0` at `oP`); main's slots kept are those at `-128` and above (AArch64: `-144`
  and above), and `MSS`'s slots are `%rbp` offsets `-8`, `-24`, `-32`, `-48`, `-40` (AArch64: `-144`, `-128`,
  `-120`, `-104`, `-112`).
- The callee's base is 8-aligned from `PreH`'s 16-aligned `R` (`Region.callee_base`); `stubTW_sfactsACG` takes
  it (`hR8`) and no `hal`.
- The `write` call is the stub's `syscall` at `entry + 34` with `%rdi = 2`, `%rax = 1` (`dtW_of_fd2` on
  `UInt64`s); its `Ac` membership needs the return address's position (`RaPos`, the `raBPcs` class), as wake's.
- `msTH` is on the x86-64 `isa` (AArch64: `isaLSE2`).
-/
import Spike.Lib.X64HelloRefAb
import Spike.Lib.X64HelloStubTAC
import Spike.Lib.X64HelloSpawnPl
import Spike.Lib.X64HelloH1ASrc

namespace Spike.Lib.X64.HelloPh.RefO

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region FragS Arena)
open Spike.Lib.X64 (AS SO NodeW DFrame CKept Abs)
open Spike.Lib.X64.Flow.Worker.Hello.SpawnFail (fES)
open Spike.Lib.X64.WakeRefTP (TPathW)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.ThreadsAb (raT)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloMainPreSrc (SpawnSrcH SlRep)
open Scc.Cert.Rt.X64 (codeT_eq)
open Scc.Sem.X64 (codeLabel)

/-- A memory side with the kernel `abi`, every state an abort site (the memory side `stubTW_sfactsACG` reads only
through `K` and `abortAt`; wake's `WakeRefStub.msT`). -/
def msTH : Spike.Lib.MemSide isa where
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

/-- **A slot of main's frame at or above `-128`** read through the callee's frame at `-144` (offsets
`[-24, 16]`): the caller's abstract value (wake's `WakeSrcCtl.placeVal_slot_kept` at hello's frame). -/
theorem placeVal_slot_kept144 {R : Region} {o : SO} {m1 m' : MachineData} {σC : AS} {s : State}
    (hA : Abs R o m1 σC) (hK : CKept R (-136 - 8) (-24) 16 m1 m')
    (hD : DFrame (R.callee (-136 - 8) (-24) 16) m' s.st.1) (hR : R.OK) (hlo : R.lo ≤ -168)
    (hhi : 16 ≤ R.hi) {k : Int} (hk : R.Off k) (hk' : -128 ≤ k) :
    placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σC.slot k).toNat := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  have hc : ¬ (R.callee (-136 - 8) (-24) 16).Off (k - (-136 - 8)) := fun ⟨_, _, h3⟩ => by
    simp only [Region.callee] at h3; omega
  have h144 := Region.addr_toNat_of hR (k := -136 - 8) (by omega) (by omega)
  have hkn := R.addr_toNat hR hk
  have e := hD (R.addr k) (R.addr_fit hR hk) (.inr (by simp only [Region.callee]; omega))
  show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  simp [Scc.Sem.X64.privLoad, e, hK k hk hc, hj, hv]

/-- **main's source placed on the threads abort path** (wake's `WakeSrcCtl.placedSE_stub`): at the call `fES`'s
state `σC` (main's slots `MSS sl cA me`), in the callee's frame condition, the source `cP` at `SpawnSrcH l ws`
with the slice's words represented by `sl` (`hsl`), the box at `cA` (`hlc`) and main's id at `me` (`hlm`), is
placed at `lbl`. -/
theorem placedSE_stubH {Λ : Scc.Sem.Layout} {lbl : Lbl} {l : WeakMem.AllocLabel} {ws : List TermRun.Word}
    {cP c0 c : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {cA me : BitVec 64}
    {lab : Label → Int64} {R : Region} {F : MachineData → Prop} {o : SO} {m1 m' : MachineData} {σC : AS}
    {s : State} (hsrc : SpawnSrcH l ws cP)
    (hsl : SlRep lbl ws sl.1.toNat sl.2.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat)
    (hR : R.OK) (hlo : R.lo ≤ -168) (hhi : 16 ≤ R.hi) (hE : (fES lab cP sl cA me).J σC c0)
    (hF : F m' ∧ CKept R (-136 - 8) (-24) 16 m1 m' ∧ Abs R o m1 σC)
    (hD : DFrame (R.callee (-136 - 8) (-24) 16) m' s.st.1) (hc : c = c0)
    (hlc : lbl l = some cA.toNat) (hlm : lbl (Spike.Lib.X64WakeSrcDefs.mainTidLbl 2) = some me.toNat) :
    PlacedSE Λ lbl s c [] := by
  obtain ⟨hc0, -, -, h8, h24, h32, h48, h40⟩ := hE
  subst hc hc0
  have pv : ∀ k, k % 8 = 0 → -128 ≤ k → k ≤ -8 →
      placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σC.slot k).toNat := fun k h0 h1 h2 =>
    placeVal_slot_kept144 hF.2.2 hF.2.1 hD hR hlo hhi ⟨h0, by omega, by omega⟩ h1
  obtain ⟨lr, rfl, hl, -, e2, e3⟩ := hsl
  exact Spike.Lib.X64.HelloPh.SpawnPl.placedSE_spawnAtH _ _ _ _ _ hsrc
    ⟨_, pv (-8) (by decide) (by decide) (by decide), by decide, sl.1.toNat, by simp [Scc.Sem.wordAddr, hl], by
      rw [h8]; simp⟩
    ⟨_, pv (-24) (by decide) (by decide) (by decide), by decide, by rw [h24]; exact e2⟩
    ⟨_, pv (-32) (by decide) (by decide) (by decide), by decide, by rw [h32]; exact e3⟩
    ⟨_, pv (-48) (by decide) (by decide) (by decide), by rw [h48]; exact hlc⟩
    ⟨_, pv (-40) (by decide) (by decide) (by decide), by rw [h40]; exact hlm⟩

variable {L : RuntimeLayout} (hp : L.prog = SccCode.helloCells) (hlo : L.Λ.code.lo = Spike.Lib.X64.HelloPh.lo)
  (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo SccCode.helloCells l = some x → L.lab l = Int64.ofNat x)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)

include hp hlo hlab hΛ in
/-- **`ACH`**: `stubTW_sfactsACG` at `instOk2bPH` with the empty take range `rSH`, the phase check `abortPhTH`, the
source placed by `placedSE_stubH`, the `write` call's tail `DtW` (`%rdi = 2`, `%rax = 1`), and the `write` call's
node as wake's `refAC`'s. -/
theorem refACH (lbl : Lbl) (l : WeakMem.AllocLabel) (ws : List TermRun.Word) (ar : Arena) (lsize : Lsize) :
    ACH L lbl l ws ar lsize := by
  intro R m0 cP sl cA me m1 σC c0 hpre hE
  obtain ⟨hR', hlo'', hhi''⟩ := callee_ofPreH hpre
  obtain ⟨hsrc, hsl, hcA, hme, hR, hal, hlo', hhi, -⟩ := hpre
  have hkc : (-136 - 8 : Int) < R.hi := by omega
  have hex : L.lab Spike.Lib.X64.Abort.threads.exit = Int64.ofNat 4203002 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have hst : L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200314 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have hI := Spike.Lib.X64.HelloPh.instOk2bPH hp hlo (Spike.Lib.X64.Rt.Reserve.ntA L.lab)
    (Spike.Lib.X64.HelloPh.siteH hp hlo hlab) (rS := rSH L)
  have hprog : Scc.Cert.Rt.X64.Abort.abortIn L.prog = true := by rw [hp]; exact SccCode.hello_abort
  have hphs := Spike.Lib.X64.HelloPh.abortPhTH hΛ hlab
  have hF := Spike.Lib.X64.fstable_enter (kb := -136 - 8) (lo' := -24) (hi' := 16) (o := ⟨-136, [(.rbp, 0)]⟩)
    (m0 := m1) (σC := σC) hR (Spike.Lib.X64.FStable.dframe R m0) (by omega) (by decide) hkc (by omega)
    (by decide) (by decide) (by decide)
  have hsub : (rSH L).Sub L.Λ.stackPool := ⟨Nat.le_refl _, by simp [rSH]⟩
  have hfit : (rSH L).lo + (rSH L).size ≤ 2 ^ 64 := by
    have := L.pool_fit; simp only [rSH]; omega
  have hFO : ∀ m, (fun m => DFrame R m0 m ∧ CKept R (-136 - 8) (-24) 16 m1 m ∧ Abs R ⟨-136, [(.rbp, 0)]⟩ m1 σC) m →
      Spike.Lib.X64.Flow.Ret0.StackOff (rSH L) (R.callee (-136 - 8) (-24) 16) m := by
    intro m _ a _ ha
    simp only [rSH, Scc.Sem.Range.contains] at ha
    omega
  -- The callee's base is 8-aligned: `R`'s base is 16-aligned.
  have hR8 : (R.callee (-136 - 8) (-24) 16).base.toNat % 8 = 0 := by
    have hb := Region.callee_base (hi' := 16) hR (show R.lo ≤ -136 - 8 + -24 by omega) (by decide) hkc
    have : (((R.callee (-136 - 8) (-24) 16).base.toNat : Int)) % 8 = 0 := by rw [hb]; omega
    omega
  have hl8 : (R.callee (-136 - 8) (-24) 16).lo % 8 = 0 := by simp [Region.callee]
  have hh8 : (R.callee (-136 - 8) (-24) 16).hi % 8 = 0 := by simp [Region.callee]
  have hctl := Spike.Lib.X64.HelloH1A.spawnSrcH_ctl (p := helloSrc) hsrc
  have hc0 : c0 = cP := hE.1
  have hc : Spike.Lib.X64.StubW.RefCtl L.Λ helloSrc (fun s _ => ownWH L s) lbl
      (fun m => DFrame R m0 m ∧ CKept R (-136 - 8) (-24) 16 m1 m ∧ Abs R ⟨-136, [(.rbp, 0)]⟩ m1 σC) c0 [] := {
    noRet := fun _ => hc0 ▸ hctl.1,
    cell := hc0 ▸ hctl.2.cell,
    place := fun s hFs => placedSE_stubH hsrc hsl hR (by omega) hhi hE hFs
      (Spike.Lib.X64.DFrame.refl _ _) rfl hcA hme,
    runOut := fun _ _ _ _ => rfl,
    runIn := fun _ _ _ _ => rfl,
    zero := hc0 ▸ hctl.2.zero }
  -- The `write` call's node (`stubTW_sfactsACG`'s own `hsysT`, at this instance).
  have hsd := hprog
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hstb := hsd.1.2
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hstb
  obtain ⟨-, -, -, hsysIn, -⟩ := hstb
  have hph := hphs
  simp only [Spike.Lib.X64.StubW.abortPhThreadsOk, Spike.Lib.X64.StubW.phOne, Bool.and_eq_true, beq_iff_eq,
    and_assoc] at hph
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, o34, q34, -⟩ := hph
  have hoff8 : (R.callee (-136 - 8) (-24) 16).Off 8 :=
    ⟨by decide, by simp [Region.callee], by simp [Region.callee]⟩
  have he34 : L.lab Spike.Lib.X64.Abort.threads.entry + Int64.ofNat 34 =
      (Spike.Lib.X64.Abort.NT L.lab Spike.Lib.X64.Abort.threads c0 (raT L.lab ".Lwc_main") .sys).pc := rfl
  have hsysT : NodeW (fun s c => ACWH L lbl ar lsize s c) (Spike.Lib.X64.PhRec.K L (rSH L)) L.exe L.endPc
      (R.callee (-136 - 8) (-24) 16)
      (fun m => DFrame R m0 m ∧ CKept R (-136 - 8) (-24) 16 m1 m ∧ Abs R ⟨-136, [(.rbp, 0)]⟩ m1 σC)
      (Spike.Lib.X64.Abort.NT L.lab Spike.Lib.X64.Abort.threads c0 (raT L.lab ".Lwc_main") .sys) := by
    intro s c hAt
    obtain ⟨hs, hn, -, hpc, σ, hA, hD, hJ, h0, h1⟩ := id hAt
    have hcc : c = c0 := hJ.1
    subst hcc
    have hAc : Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab ".Lwc_main" s :=
      Spike.Lib.X64.Hello.StubW.ac_stubG (by rw [hpc]; exact Spike.Lib.X64ConsumerA.ThreadsAcSt.memSysT.1) hA
        hoff8 (.inr (.inr ⟨by rw [hpc]; exact Spike.Lib.X64ConsumerA.ThreadsAcSt.memSysT.2, rfl⟩)) hJ.2
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
  have hT := Spike.Lib.X64.Hello.StubW.stubTW_sfactsACG (own := fun s _ => ownWH L s) (frs := [])
    (Dt := Spike.Lib.X64.WakeWf.DtW) (pfx := ".Lwc_main") (cl := ".x3") (n := 94) (st := ".x4") (off := -120)
    (Cl := Spike.Lib.X64.HelloPh.ClH L) (p := helloSrc) (rd := fun _ => True) (G := fun _ _ => True)
    (ar := ar) (J := fun _ _ _ _ _ => False) (lsize := lsize) (al := fun _ => none) (ms := msTH)
    hI hprog hphs hR' hR8 hlo'' hhi'' hl8 hh8 hF hsub hfit hFO hc (fun s h => h.2)
    (fun a ha => by
      have e : (Spike.Lib.X64.PhRec.μ L).site .release = some 4200354 := by
        show codeLabel L.Λ.code.lo L.prog "scc_rt_release_site" = _
        rw [hp, hlo, ← codeT_eq]; decide +kernel
      rw [e] at ha; cases ha; rw [hex]; decide)
    (fun a ha => by
      rw [Spike.Lib.X64.HelloPh.siteH hp hlo hlab] at ha
      cases ha; rw [hex, hst]; decide)
    (fun k a ha => by
      have e : (Spike.Lib.X64.PhRec.μ L).abortAt k = codeLabel Spike.Lib.X64.HelloPh.lo SccCode.helloCells
          (Scc.Cert.Link.abortName k) := by
        show codeLabel L.Λ.code.lo L.prog (L.Λ.abortLbl k) = _
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
      obtain ⟨-, -, -, -, σ, hA, -, -, h0, h1⟩ := hAt
      rw [← hA.regs] at h0 h1
      exact Spike.Lib.X64.WakeWf.dtW_of_fd2 (UInt64.toBitVec_inj.mp h0) (UInt64.toBitVec_inj.mp h1))
  exact TPathW.ofStub hT hsysT

end Spike.Lib.X64.HelloPh.RefO

/-- info: 'Spike.Lib.X64.HelloPh.RefO.placeVal_slot_kept144' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.placeVal_slot_kept144

/-- info: 'Spike.Lib.X64.HelloPh.RefO.placedSE_stubH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.placedSE_stubH

/-- info: 'Spike.Lib.X64.HelloPh.RefO.refACH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.refACH
