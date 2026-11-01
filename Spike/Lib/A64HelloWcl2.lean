/-
**hello.w's `wc_main` at its `clone`'s `svc` inside the root's third level `RootWX.W2H`** (AArch64;
the twin of `Spike/Lib/A64WakeWcl.lean` at helloProg, frame 144): `H1GAH.wcl` at the root's level
`W2H L (ntA L.lab) ar helloSrc Dt (ClH L) Ctx lbl lsize` and the clone fact `StackM (r1Of L.lab)`.

The `svc` is at `.sp6 + 4 · 25`; its source `SpawnSrcH l ws c` is placed at `wc_main`'s slots (`WcSp6.FrWH` in
`wcNSH`, `WcPl2.slots_absH`), given the frame's cell is the box's (`cA.toNat = b`) and the slice and main's word
are an entry state's (`FrMGH`), as wake's `WclA` (`cA.toNat = b`, `m.toNat = tcb0`).

- `svc_factsH`: the `svc`'s pc at the canonical base, its `ph2bH` phase `0`, off the sites; the resumption's
  phase `0`.
- `ab_resH`, `ab_offH`: the write abort's labels resolve; the resumption is off its pcs.
- `own_svc4H`: `ownGH` at the resumption's pc.
- `svc_clH`: a state at `wcNSH` is at the `svc` cell and on the clone path (`ClH`).
- `wcl_W2H`: `W2H` and `StackM` at `wcNSH` from the placement at the slots (`Hs`).
- `wcl_W2GJ1H`: the same at a ghost of `GJ1H` (`SpawnPl.hpl_GJ1H`).

The pcs are decided at the canonical base (`hlab`); no absolute address appears in a statement.
-/
import Spike.Lib.A64HelloWcPl2
import Spike.Lib.A64HelloWcW2

namespace Spike.Lib.A64.HelloPh.Wcl2

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf)
open Scc.Cert.Rt.A64 (codeT_eq blockAt okPcOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib (Arena FragS Ctl Region)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.Reserve (ntA)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (At svcDir)
open Spike.Lib.A64.Flow.WakeWc (MidG)
open Spike.Lib.A64.Flow.HelloWc (FrMGH)
open Spike.Lib.A64.HelloPh.WcSp6 (wcNSH)
open Spike.Lib.A64.HelloPh.RootWX (W2H)
open Spike.Lib.A64.HelloPh.Ti2 (SlotPH SlotSlH)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.A64.Flow.Ret0 (StackM)
open Spike.Lib.HelloHMid (SBH slWsH)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH)
open Spike.Lib.HelloSrc (helloSrc)

/-- **The `svc`'s pc** at the canonical base: its value, `ph2bH` `0`, off the sites; the resumption's `ph2bH`
`0`. -/
theorem svc_factsH : (Int64.ofNat 2169740 + Int64.ofNat (4 * 25)).toBitVec.toNat = 2169840 ∧
    Spike.Lib.A64.HelloPh.okC 2169840 = true ∧ Spike.Lib.A64.HelloPh.ph2bHC 2169844 = 0 := by decide +kernel

/-- The `svc` of `.sp6` in hello's program. -/
theorem hello_svc : blockAt SccCode.helloProg ".L22_wc_main.sp6" 25 [svcDir] = true := by decide +kernel

/-- The labels of the write abort's pcs resolve in hello's program. -/
theorem ab_resH : Spike.Lib.A64.AllocG.abLabs.all
    (fun x => (codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg x).isSome) = true := by decide +kernel

/-- **The clone's resumption is off the write abort's pcs** at the code labels. -/
theorem ab_offH : Int64.ofNat 2169740 + Int64.ofNat (4 * 25) + Int64.ofNat 4 ∉
    Spike.Lib.A64.WriteAb.abPcs (Spike.Lib.LowerA64.labC Spike.Lib.A64.HelloPh.lo SccCode.helloProg) := by
  decide +kernel

variable {L : RuntimeLayout}

/-- **`ownGH` at the clone's resumption** is `own2bH L a 0`. -/
theorem own_svc4H {a : BitVec 64}
    (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    {s : State} (hs : s.st.2 = L.lab ".L22_wc_main.sp6" + Int64.ofNat (4 * 25) + Int64.ofNat 4) :
    Spike.Lib.A64.HelloPh.ownGH L a s = Spike.Lib.A64.HelloPh.own2bH L a 0 := by
  have hp : pcOf s = 2169844 := by
    unfold pcOf; rw [hs, Spike.Lib.A64.HelloPh.WcSp4W.lab_sp6H hlab]; rfl
  obtain ⟨-, -, -, -, -, e6, e7, -, -⟩ := Spike.Lib.A64.HelloPh.labs_eqH hlab (L := L)
  have hg : Spike.Lib.A64.HelloPh.Good2bH L s :=
    .inr (.inl (by unfold Spike.Lib.A64.WakePh.inPc; rw [e6, e7, hp]; omega))
  rw [Spike.Lib.A64.HelloPh.ownGH_2b hlab hg, hp, Spike.Lib.A64.HelloPh.ph2bH_eq, svc_factsH.2.2]

/-- **A state at `wcNSH` is at the `svc` cell and on the clone path** (`ClH`: the clone's pc, a system call, a
`clone`). -/
theorem svc_clH (hp : L.prog = SccCode.helloProg) {R : Region} {F : MachineData → Prop} {c0 : Ctl}
    {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} {s : State} {c : Ctl}
    (hA : At L.exe L.endPc R F (wcNSH (_root_.Executable.labels L.exe).label c0 t k sl me cA fr) s c) :
    Kraken.Promising.Lower.A64.CellAt s svcDir 4 ∧ Spike.Lib.A64.HelloPh.ClH L s := by
  obtain ⟨hs, hn, -, hpc, σ, hAb, -, -, h0, -, h2, -, h4, h8, -⟩ := id hA
  have hc : Kraken.Promising.Lower.A64.CellAt s svcDir 4 :=
    Spike.Lib.A64.HelloPh.WcW.cell1H hp hello_svc hs hn hpc
  refine ⟨hc, Spike.Lib.A64.Flow.HelloWc.wcNSH_clonePc hA, Scc.Sem.A64.atSvc_of_cellAt hc, ?_⟩
  have hr := hAb.regs
  refine ⟨σ.regs.X1.toNat, σ.regs.X3.toNat, ?_⟩
  simp only [Scc.Sem.Kernel.decode, Scc.Sem.A64.abi, Scc.Sem.A64.xRegs, hr]
  have e8 : σ.regs.X8.toNat = 220 := by rw [← UInt64.toNat_toBitVec, h8]; rfl
  have e0 : σ.regs.X0.toNat = 855808 := by rw [← UInt64.toNat_toBitVec, h0]; rfl
  have e2 : σ.regs.X2.toNat = 0 := by rw [← UInt64.toNat_toBitVec, h2]; rfl
  have e4 : σ.regs.X4.toNat = 0 := by rw [← UInt64.toNat_toBitVec, h4]; rfl
  simp [e8, e0, e2, Scc.Sem.Kernel.Nrs.a64, Scc.Sem.Kernel.cloneFlags]
  exact ⟨e4, rfl⟩

section Wcl

variable {ar : Arena} {Dt : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize} {R : Region}
  {F : MachineData → Prop} {J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop} {l : WeakMem.AllocLabel} {b : Nat}
  {ws : List TermRun.Word}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = Spike.Lib.A64.HelloPh.lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

set_option maxHeartbeats 800000 in
/-- **`H1GAH.wcl` at the root's level** (wake's `wcl_W1`): at the clone's `svc` (`wcNSH`), the frame's cell the
box's (`hcA`) and its slice and main's word an entry state's (`hFr`), the source at `SpawnSrcH l ws`, `W2H` at no
frames (its placement by `Hs` at the slots, as `SpawnPl.hpl_GJ1H`) and the clone fact `StackM`. -/
theorem wcl_W2H (hRlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (Hs : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      PlacedSE L.Λ lbl s c0 [])
    {t k : BitVec 64} :
    ∀ s c sl me cA fr, At L.exe L.endPc R F (wcNSH L.lab c t k sl me cA fr) s c →
      SpawnSrcH l ws c → cA.toNat = b → FrMGH J1 fr sl me → StackM (r1Of L.lab) s.st.1 →
      W2H L (ntA L.lab) ar helloSrc Dt (Spike.Lib.A64.HelloPh.ClH L) Ctx lbl lsize s c [] ∧
        StackM (r1Of L.lab) s.st.1 := by
  intro s c sl me cA fr hA hsrc hcA hFr hSM
  obtain ⟨hc, hCl⟩ := svc_clH hp hA
  obtain ⟨-, -, -, hpc, σ, hAb, -, hJ⟩ := id hA
  have hFW := hJ.2.2.2.2.2.2.2.2.2.2.2.2.2
  change s.st.2 = L.lab ".L22_wc_main.sp6" + Int64.ofNat (4 * 25) at hpc
  have e6 := Spike.Lib.A64.HelloPh.WcSp4W.lab_sp6H hlab (L := L)
  have hP : pcOf s = 2169840 := by unfold pcOf; rw [hpc, e6, svc_factsH.1]
  have hpo := ((Spike.Lib.A64.HelloPh.instOkH hp hlo (ntA L.lab) (fun _ => False) hsite (rS := ⟨0, 0⟩)).off s
    (by rw [Spike.Lib.A64.HelloPh.okPc_eq hΛ, hP]; exact svc_factsH.2.1)).1
  have hsys := hCl.2.1
  have hS := Spike.Lib.A64Consumer.sfacts_svcAt (Λ := L.Λ) (lbl := fun _ => none) (rS := ⟨0, 0⟩)
    (μ := Spike.Lib.A64.PhRec.μ L) (own := fun _ => Spike.Lib.A64.HelloPh.own2bH L (ntA L.lab) 0)
    (Tk := fun _ => False) (Dt := Dt) (c := Spike.Lib.A64Consumer.c0) (s := s)
    Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hpo.noSite hpo.noTake hc (fun _ => ⟨rfl, Iff.rfl⟩) (fun h => h.elim)
    (fun k a ha e => (hpo.noAbort k a ha e).elim)
    (fun _ _ _ hw => by obtain ⟨_, _, hd'⟩ := hCl.2.2; rw [hd'] at hw; cases hw)
  have hst := hS.toSt.toSt2.congr (own' := Spike.Lib.A64.HelloPh.ownGH L (ntA L.lab))
    (Spike.Lib.A64.HelloPh.WcSp4W.own_sp6H hlab (k := 25) (by decide) hpc)
    (fun s' h => own_svc4H hlab (by
      rw [Spike.Lib.A64.WakePh.keep_pc hc (Spike.Lib.A64.WakePh.keep_svc hsys h), hpc]))
  have hab4 : L.lab ".L22_wc_main.sp6" + Int64.ofNat (4 * 25) + Int64.ofNat 4 ∉
      Spike.Lib.A64.WriteAb.abPcs L.lab := by
    rw [Spike.Lib.A64.AllocG.abPcs_congr (Spike.Lib.A64.HelloWf.lab_labCH hlab ab_resH), e6]; exact ab_offH
  have hnw : ∀ L', ¬ Spike.Lib.A64ConsumerA.WrAt s L' := fun L' hL => by
    rcases hL with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [Kraken.Promising.Lower.A64.exec_svc hc] at h <;> cases h
  have hctl := Spike.Lib.HelloH1A.spawnSrcH_ctl (p := helloSrc) hsrc
  have hpl : PlacedSE L.Λ lbl s c [] := by
    have hs := WcPl2.slots_absH hRlo hhi hAb
    obtain ⟨h144, -, h128, h120, h112, h104, -, -⟩ := hFW
    rw [h104, h112, h144, h128, h120, hcA] at hs
    exact Hs c sl me cA fr ⟨⟨l, b, ⟨rfl, rfl, hsrc⟩, hcA⟩, hFr⟩ s hs
  refine ⟨⟨rfl, Spike.Lib.A64.WakeWf.Wf.intro hst
    ⟨fun _ h => (by rw [hsys] at h; cases h), fun _ _ call hdc s' hs' hab => ?_,
      fun _ a ha e => (hpo.noTake a ha e).elim⟩
    ⟨fun _ h => (by rw [hsys] at h; cases h), fun _ _ hncl => (hncl hCl).elim,
      fun _ a ha e => (hpo.noTake a ha e).elim⟩
    (fun _ h => h.2) (fun _ => hctl.1) hpl (fun _ _ _ L' hL => (hnw L' hL).elim)
    (fun hL => (hnw _ hL).elim) hctl.2 (Spike.Lib.A64.WakeWf.abortWf_of_off hpo.noAbort)⟩, hSM⟩
  obtain ⟨r, -, rfl⟩ := (Scc.Sem.A64.mem_certSuccs_svc hc hdc).mp hs'
  exact (Spike.Lib.A64.WriteAb.not_ab_of_pc (show s.st.2 + Int64.ofNat 4 ∉ _ by rw [hpc]; exact hab4) hab).elim

/-- **`H1GAH.wcl` at a ghost of `GJ1H`** (rodata's label `lr`, the box's `l'` fresh at `lbl1`, main's id at the
TCB): `wcl_W2H` at the twice extended placement `upd lbl1 l' b'` (`SpawnPl.hpl_GJ1H`). -/
theorem wcl_W2GJ1H (hRlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) {lbl1 : Lbl} {lr l' : WeakMem.AllocLabel} {b' : Nat}
    {F' : MachineData → Prop} {tp : UInt64} (hl' : lbl1 l' = none)
    (hmt : lbl1 (Spike.Lib.WakeT1.mainTidLbl 2) = some (L.pinA.toNat + 8))
    (hG : Spike.Lib.HelloH2G.GJ1H L lbl1 lr R F' J1 tp) {t k : BitVec 64} :
    ∀ s c sl me cA fr, At L.exe L.endPc R F (wcNSH L.lab c t k sl me cA fr) s c →
      SpawnSrcH l' (slWsH lr) c → cA.toNat = b' → FrMGH J1 fr sl me → StackM (r1Of L.lab) s.st.1 →
      W2H L (ntA L.lab) ar helloSrc Dt (Spike.Lib.A64.HelloPh.ClH L) Ctx (Spike.Lib.A64ConsumerA.upd lbl1 l' b')
        lsize s c [] ∧ StackM (r1Of L.lab) s.st.1 :=
  wcl_W2H hp hlo hΛ hlab hsite hRlo hhi (SpawnPl.hpl_GJ1H hl' hmt hG)

end Wcl

end Spike.Lib.A64.HelloPh.Wcl2

/-! ## Axioms -/

/-- info: 'Spike.Lib.A64.HelloPh.Wcl2.own_svc4H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Wcl2.own_svc4H

/-- info: 'Spike.Lib.A64.HelloPh.Wcl2.svc_clH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Wcl2.svc_clH

/-- info: 'Spike.Lib.A64.HelloPh.Wcl2.wcl_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Wcl2.wcl_W2H

/-- info: 'Spike.Lib.A64.HelloPh.Wcl2.wcl_W2GJ1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Wcl2.wcl_W2GJ1H
