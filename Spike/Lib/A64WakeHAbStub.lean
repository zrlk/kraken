/-
**wake.w's heap abort path inside `W0`** (AArch64): the obligations of
`Spike.Lib.A64.Flow.WakeWc.WcHAbStub` (`Spike/Lib/A64WakeHAb.lean`) at
wake's level before the allocation (`WakeWf.W0` at `ownG`, the write tail
`WakeWf.DtW`, no outside moves), from the components of `WakeWf.Wf` at every
node of `Abort.Disp.HPathW`:

- the state's facts at `ownG` (`hpathW_habG`), both abort phases
  (`WakeWf.hpathW_ph`), the per-state facts `X0` in `scc_rt_abort`'s code
  (`abPH`'s `AbP`);
- the source's control unmoved (`c = c0`), so the control's facts, the
  frames' placement and the heap abort's obligation are the caller's;
- no write to the arena or the counter (`AllocG.blkW_noWr`, the `svc`s);
- the abort sites: every node off them but the exit call, which is the heap
  abort's site with exit status `101` (`nodeW_exAbWf`).

- `lab_ne`: two labels' pcs differ, decided on `codeT` (no address in the
  text).
- `hpathW_hC`, `hpathW_hN`, `hpathW_hAb`, `hpathW_hX`: the components.
- `hpathW_hab0`: `HPathW` inside `W0`.
- `wc_heapAbStub`: `WcHAbStub` at `W0` (`stubHRW_of_code` in the callee
  region at `-240`).
-/
import Spike.Lib.A64WakeHAbWf
import Spike.Lib.A64WakeHAb
import Spike.Lib.A64WakeWfHPA
import Spike.Lib.A64AbortHeapRWCode

namespace Spike.Lib.A64.WakePh

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq blockAt okPcOf)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Cert.Rt.A64.Print (add4 add0)
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Spike.Lib (Arena FragS Frag Region HeapAbortOblA)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64ConsumerA (SFactsSt2 WrAt)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.Abort (NT)
open Spike.Lib.A64.Abort.Disp (DN HPathW)
open Spike.Lib.A64.WakeWf (DtW Wf W0 NoWrC AbortWf RunWf)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)

set_option linter.unusedSimpArgs false

variable {L : RuntimeLayout} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}

/-- **A path obligation inside a weaker fragment.** -/
theorem HPathW.map {W₁ W₂ : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    (h : HPathW W₁ K exe endPc R F c0 ra) (hw : ∀ s c, W₁ s c → W₂ s c) : HPathW W₂ K exe endPc R F c0 ra := by
  have hb : ∀ {n : ND} {blk : List Directive}, BlkW W₁ K exe endPc R F n blk → BlkW W₂ K exe endPc R F n blk :=
    fun h s σ c he hn hd hp hA hF hJ k hk m hA' hD =>
      ⟨hw _ c (h s σ c he hn hd hp hA hF hJ k hk m hA' hD).1, (h s σ c he hn hd hp hA hF hJ k hk m hA' hD).2⟩
  have hn : ∀ {n : ND}, NodeW W₁ K exe endPc R F n → NodeW W₂ K exe endPc R F n :=
    fun h s c hA => ⟨hw s c (h s c hA).1, (h s c hA).2⟩
  exact ⟨hb h.de, hb h.dt1, hb h.dj1, hb h.dt2, hb h.dg2, hb h.se, hn h.sn1, hn h.sn1b, hb h.sn2, hn h.ssvc,
    hb h.sn5, hn h.sex⟩

/-- **The source's control is the caller's** at every node of the path. -/
theorem hpathW_hC {exe : _root_.Executable} {endPc : Int64} :
    HPathW (fun _ c => c = c0) (fun _ _ => False) exe endPc R F c0 ra := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | exact Spike.Lib.A64.WakeWf.blkW_ofJ fun _ _ h => h.1
    | exact Spike.Lib.A64.WakeWf.nodeW_ofJ fun _ _ h => h.1
    | exact Spike.Lib.A64.WakeWf.nodeW_ofJ fun _ _ h => h.1.1

section Inst

variable (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
include hp hlo hlab

omit hp hlo in
/-- **Two labels' pcs differ** when their code addresses do (`hd`, decided on
`codeT` with no address in the text), the first resolved (`hs`). -/
theorem lab_ne {l l' : Label}
    (hd : codeT lo wakeProg l' ≠ (codeT lo wakeProg l).map fun y => (Int64.ofNat y).toBitVec.toNat)
    (hs : (codeT lo wakeProg l).isSome = true) {x : Nat} (hx : codeOf lo wakeProg l' = some x) :
    (L.lab l).toBitVec.toNat ≠ x := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
  rw [codeT_eq] at hy hd
  rw [hlab _ _ hy]
  intro h
  exact hd (by rw [hx, hy, Option.map_some, h])

/-- **No write to the arena or the counter** at every node of the path: its
blocks are silent (`AllocG.blkW_noWr`), its other nodes an `adrp`, an `add`
and two `svc`s. -/
theorem hpathW_hN {ar : Arena} {p : Prog} {L0 : Lbl} {ls0 : Lsize} {Ctx : FragS isaLSE2}
    {fs : List TermRun.Frame} (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -48)
    (hhi : 0 ≤ R.hi) :
    HPathW (NoWrC ar p L0 ls0 Ctx fs) (fun _ _ => False) L.exe L.endPc R F c0 ra := by
  have hI := instOkW hp hlo a (fun _ => False) (siteW hp hlo hlab) (rS := ⟨0, 0⟩)
  have hsd := abortIn_wake
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hcode := Scc.Cert.Rt.A64.Abort.code_stub (c0 := c0) L.lays rfl (hp ▸ hsd.1.1.1.1.2)
  have hst := hsd.1.1.1.1.2
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hb0, hn1, hn1b, hb1, hsvcIn, hb2, -, -, -⟩ := hst
  simp only [Scc.Cert.Rt.A64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, -, hg2, -⟩ := hdi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Spike.Lib.A64.WakeWf.blkW_noWrC (Spike.Lib.A64.AllocG.blkW_noWr hI (hp ▸ hd0)
      (by simp only [DN.nd2R, add0]) Abort.Disp.d0_ok hR hal (by omega) (by omega))
  · exact Spike.Lib.A64.WakeWf.blkW_noWrC (Spike.Lib.A64.AllocG.blkW_noWr hI (hp ▸ ht1)
      (by simp only [DN.nd2R, add0]) Abort.Disp.t1_ok hR hal (by omega) (by omega))
  · exact Spike.Lib.A64.WakeWf.blkW_noWrC (Spike.Lib.A64.AllocG.blkW_noWr hI (hp ▸ hj1)
      (by simp only [DN.nd2R, add4, add0]) Abort.Disp.j1_ok hR hal (by omega) (by omega))
  · exact Spike.Lib.A64.WakeWf.blkW_noWrC (Spike.Lib.A64.AllocG.blkW_noWr hI (hp ▸ ht2)
      (by simp only [DN.nd2R, add0]) Abort.Disp.t2_ok hR hal (by omega) (by omega))
  · exact Spike.Lib.A64.WakeWf.blkW_noWrC (Spike.Lib.A64.AllocG.blkW_noWr hI (hp ▸ hg2)
      (by simp only [DN.nd2R, add0]) Abort.Disp.g2_ok hR hal (by omega) (by omega))
  · exact Spike.Lib.A64.WakeWf.blkW_noWrC (Spike.Lib.A64.AllocG.blkW_noWr hI (hp ▸ hb0)
      (by simp only [NT, add0]) Abort.b0_ok hR hal (by omega) (by omega))
  · exact Spike.Lib.A64.WakeWf.nodeW_noWrC (Spike.Lib.A64.AllocG.nodeW_noWr_si (si := .adrp .X9 Abort.heap.msg)
      hI (hp ▸ hn1) rfl (by simp only [NT, add0]))
  · exact Spike.Lib.A64.WakeWf.nodeW_noWrC
      (Spike.Lib.A64.AllocG.nodeW_noWr_si (si := .addLo12 .X9 .X9 Abort.heap.msg) hI (hp ▸ hn1b) rfl
        (by simp only [NT, add4, add0]))
  · exact Spike.Lib.A64.WakeWf.blkW_noWrC (Spike.Lib.A64.AllocG.blkW_noWr hI (hp ▸ hb1)
      (by simp only [NT, add4, add0]) Abort.b1Heap_ok hR hal (by omega) (by omega))
  · exact Spike.Lib.A64.WakeWf.nodeW_noWrC (Spike.Lib.A64.WakeWf.nodeW_noWr_svc
      (Scc.Cert.Rt.A64.Print.code_field L.lays rfl (hp ▸ hsvcIn) (by simp only [NT, Abort.pcSvc, add4, add0])))
  · exact Spike.Lib.A64.WakeWf.blkW_noWrC (Spike.Lib.A64.AllocG.blkW_noWr hI (hp ▸ hb2)
      (by simp only [NT, Abort.pcSvc, add4, add0]) Abort.b2_ok hR hal (by omega) (by omega))
  · exact Spike.Lib.A64.WakeWf.nodeW_noWrC (Spike.Lib.A64.WakeWf.nodeW_noWr_svc
      fun s hs hn => by rw [Abort.NT_pc]; exact hcode.ex s hs hn)

/-- **The exit call is the heap abort's site** with exit status `101`
(`x8 = 94`, `x0 = 101`), the caller's heap abort obligation (`hobl`) at the
source's unmoved control. -/
theorem nodeW_exAbWf {ar : Arena} {Ab Ac : State → Prop} {fs : List TermRun.Frame}
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hobl : HeapAbortOblA ar.cells ar.ctr c0) :
    NodeW (fun s c => AbortWf ar (Spike.Lib.A64.PhRec.μ L) Ab Ac s c fs) (fun _ _ => False) L.exe L.endPc R F
      (NT L.lab Abort.heap c0 ra .ex) := by
  rintro s c ⟨-, -, -, hpc, σ, hA, -, hJ⟩
  have hd : Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup σ.regs.X0.toNat) := by
    rw [← Spike.Lib.A64.Flow.svcCall_exitGroup (by rw [hJ.2.1]; rfl), Spike.Lib.A64.Flow.svcCall, ← hA.regs]; rfl
  refine ⟨fun k x hx hpcs => ⟨?_, fun v hv => ?_⟩, fun _ h => h⟩
  · have hx' : codeOf lo wakeProg (Scc.Cert.Link.abortName k) = some x := by
      have h' : codeOf L.Λ.code.lo L.prog (L.Λ.abortLbl k) = some x := hx
      rwa [hp, hlo, hΛ] at h'
    have hpx : (L.lab Abort.heap.exit).toBitVec.toNat = x := by rw [← hpcs]; unfold pcOf; rw [hpc]; rfl
    cases k
    · exact absurd hpx (lab_ne hlab (by decide +kernel) (by decide +kernel) hx')
    · exact .inr (.inr (.inl ⟨rfl, by rw [hJ.1.1]; exact hobl⟩))
    · exact absurd hpx (lab_ne hlab (by decide +kernel) (by decide +kernel) hx')
    · exact absurd hpx (lab_ne hlab (by decide +kernel) (by decide +kernel) hx')
    · exact absurd hpx (lab_ne hlab (by decide +kernel) (by decide +kernel) hx')
  · rw [hd] at hv
    cases hv
    rw [hJ.2.2]
    rfl

/-- **The abort sites at every node of the path**: off them but at the exit
call (`nodeW_exAbWf`), by the path's phase checks (`abortPhHW`). -/
theorem hpathW_hAb {ar : Arena} {Ab Ac : State → Prop} {fs : List TermRun.Frame} (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hobl : HeapAbortOblA ar.cells ar.ctr c0) :
    HPathW (fun s c => AbortWf ar (Spike.Lib.A64.PhRec.μ L) Ab Ac s c fs) (fun _ _ => False) L.exe L.endPc R F
      c0 ra := by
  have hI := instOkW hp hlo a (fun _ => False) (siteW hp hlo hlab) (rS := ⟨0, 0⟩)
  have hphs := abortPhHW (Λ := L.Λ) (lab := L.lab) hΛ hlab
  simp only [Spike.Lib.A64.StubW.abortPhHeapOk, Spike.Lib.A64.StubW.phOne, Bool.and_eq_true, beq_iff_eq,
    and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pg2, pb0, o1, -, o1b, -, pb1, o7, -, pb2, -⟩ := hphs
  have hb : ∀ {n : ND} {blk : List Directive} {lo' hi' : Int} {l : Label} {k : Nat},
      L.lab l + Int64.ofNat (4 * k) = n.pc → Spike.Lib.A64.Flow.okBlk lo' hi' n.o blk = true →
      Spike.Lib.A64Consumer.blkPh (okPcOf lo wakeProg L.Λ) phW (fun _ => false) L.lab
        (L.lab l + Int64.ofNat (4 * k)) 0 blk = true →
      Spike.Lib.A64Consumer.noRetBlk blk = true →
      BlkW (fun s c => AbortWf ar (Spike.Lib.A64.PhRec.μ L) Ab Ac s c fs) (fun _ _ => False) L.exe L.endPc R F
        n blk := fun he hok hph hnr =>
    Spike.Lib.A64.WakeWf.blkW_abortWf (Spike.Lib.A64.WakeWf.hpcOf hI hok (he ▸ hph) hnr)
  have hn : ∀ {n : ND} {q : Int64}, n.pc = q → okPcOf lo wakeProg L.Λ q.toBitVec.toNat = true →
      NodeW (fun s c => AbortWf ar (Spike.Lib.A64.PhRec.μ L) Ab Ac s c fs) (fun _ _ => False) L.exe L.endPc R F
        n := fun hq hok =>
    Spike.Lib.A64.WakeWf.nodeW_abortWf_off fun j x hx => by
      rw [hq]
      exact Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hok)
        (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hb (by simp only [DN.nd2R, add0]) Abort.Disp.d0_ok pd0 rfl
  · exact hb (by simp only [DN.nd2R, add0]) Abort.Disp.t1_ok pt1 rfl
  · exact hb (by simp only [DN.nd2R, add4, add0]) Abort.Disp.j1_ok pj1 rfl
  · exact hb (by simp only [DN.nd2R, add0]) Abort.Disp.t2_ok pt2 rfl
  · exact hb (by simp only [DN.nd2R, add0]) Abort.Disp.g2_ok pg2 rfl
  · exact hb (by simp only [NT, add0]) Abort.b0_ok pb0 rfl
  · exact hn (by simp only [NT, add0]) o1
  · exact hn (by simp only [NT, add4, add0]) o1b
  · exact hb (by simp only [NT, add4, add0]) Abort.b1Heap_ok pb1 rfl
  · exact hn (by simp only [NT, Abort.pcSvc, add4, add0]) o7
  · exact hb (by simp only [NT, Abort.pcSvc, add4, add0]) Abort.b2_ok pb2 rfl
  · exact nodeW_exAbWf hp hlo hlab hΛ hobl

omit hp hlo in
/-- **The path's states are in `scc_rt_abort`'s code** (`abPH`'s `AbP`). -/
theorem hpathW_hX (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) :
    HPathW (fun s _ => inPc L "scc_rt_abort" "scc_rt_thr_worker" s) (fun _ _ => False) L.exe L.endPc R F
      c0 ra := by
  have hsd := abortIn_wake
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  obtain ⟨e1, e2, -, -, -, -, -, -, -, e10, -, -, -, -, -⟩ := abH_labs hlab
  have hP := abPH (μ := Spike.Lib.A64.PhRec.μ L) (F := F) (c0 := c0) (ra := ra) hlab hR hal hlo' hhi
    (fun a' ha => by
      have h' : codeOf L.Λ.code.lo L.prog "scc_rt_take_site" = some a' := ha
      rw [hp, hlo, e10] at h'
      cases h'
      rw [e1, e2]; decide)
    (Scc.Cert.Rt.A64.Abort.code_disp L.lays rfl (hp ▸ hsd.2))
    (Scc.Cert.Rt.A64.Abort.code_stub L.lays rfl (hp ▸ hsd.1.1.1.1.2))
  exact HPathW.map (W₁ := AbW L R ra (Spike.Lib.A64.PhRec.μ L))
    ⟨hP.de, hP.dt1, hP.dj1, hP.dt2, hP.dg2, hP.se, hP.sn1, hP.sn1b, hP.sn2, hP.ssvc, hP.sn5, hP.sex⟩
    fun _ _ h => h.1.1

/-- **The heap path inside `W0`** at `ownG`, the write tail `DtW`, the
frames `fs` (`[]` or `[frM]`, `hfs`), from a caller with the return address
past `scc_rt_alloc`'s full branch (`hra`): the components of `Wf` at every
node, the control's facts, its frames' placement and the heap abort's
obligation at the caller's control `c0` (`hc0`, `hpl`, `hobl`), the clone
path's global clause (`hcl`), the per-state facts `X0` in `scc_rt_abort`'s
code (`hX0`). -/
theorem hpathW_hab0 {ar : Arena} {p : Prog} {Cl : State → Prop} {Ctx : FragS isaLSE2} {L0 : Lbl} {ls0 : Lsize}
    {frM : TermRun.Frame} {X0 : State → Prop} {fs : List TermRun.Frame} (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hra : ra = (L.lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec)
    (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hc0 : (fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) (hpl : ∀ s, PlacedSE L.Λ L0 s c0 fs)
    (hobl : HeapAbortOblA ar.cells ar.ctr c0) (hX0 : ∀ s, inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    HPathW (fun s c => W0 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) ar p DtW (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.A64.ThreadsAb.Ac L.lab pfxM) Ctx L0 ls0 frM X0 s c fs) (fun _ _ => False) L.exe L.endPc R F
      c0 ra := by
  have hsite := siteW hp hlo hlab
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, e12, e13, e14, -⟩ := abH_labs hlab
  have hG := hpathW_habG hp hlo hsite (Λ := L.Λ) (F := F) (c0 := c0) (ra := ra) a hΛ hlab hR hal hlo' hhi
    (fun h => absurd (hra.symm.trans h) (by rw [e12, e13]; decide)) (by rw [hra, e12, e14]; decide)
  have hPh := Spike.Lib.A64.WakeWf.hpathW_ph (Cl := Cl) (F := F) (c0 := c0) (ra := ra)
    (instOkW hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)) (hp ▸ abortIn_wake)
    (abortPhHW (Λ := L.Λ) (lab := L.lab) hΛ hlab) hlab hR hal hlo' hhi
    (fun a' ha => by
      have h' : codeOf L.Λ.code.lo L.prog "scc_rt_take_site" = some a' := ha
      rw [hp, hlo] at h'
      exact lab_ne hlab (by decide +kernel) (by decide +kernel) h')
    (hra ▸ Spike.Lib.A64.WakeWf.hra_alloc hlab)
  have hN := hpathW_hN (ar := ar) (p := p) (L0 := L0) (ls0 := ls0) (Ctx := Ctx) (fs := fs) (F := F) (c0 := c0)
    (ra := ra) hp hlo hlab a hR hal hlo' hhi
  have hAb := hpathW_hAb (ar := ar) (Ab := Spike.Lib.A64.WriteAb.Ab L.lab)
    (Ac := Spike.Lib.A64.ThreadsAb.Ac L.lab pfxM) (fs := fs) (R := R) (F := F) (ra := ra) hp hlo hlab a hΛ hobl
  have hX := hpathW_hX (F := F) (c0 := c0) (ra := ra) hlab hR hal hlo' hhi hp hlo
  have h1 := HPathW.and hG hPh fun s c h₁ h₂ => And.intro h₁ h₂
  have h2 := HPathW.and h1 hpathW_hC fun s c h₁ h₂ => And.intro h₁ h₂
  have h3 := HPathW.and h2 hN fun s c h₁ h₂ => And.intro h₁ h₂
  have h4 := HPathW.and h3 hAb fun s c h₁ h₂ => And.intro h₁ h₂
  refine HPathW.and h4 hX fun s c h hx => ?_
  obtain ⟨⟨⟨⟨hst, hab, hac⟩, hc⟩, hw⟩, habt⟩ := h
  subst hc
  exact ⟨hfs, hX0 s hx, Wf.intro hst hab hac hcl hc0.1 (hpl s) hw.1 hw.2 hc0.2 habt⟩

end Inst

open Spike.Lib.A64.Flow.WakeWc (WcHAbStub wX) in
/-- **`WcHAbStub` at wake's level before the allocation** (`W0` at `ownG`,
no outside moves): `stubHRW_of_code` in the region below `-240` at each
caller's state of `wX .abort`, whose control has the control's facts, its
frames placed and the heap abort's obligation (`hctl`); the exit call at an
abort site of the memory side (`hab`). -/
theorem wc_heapAbStub {ar : Arena} {p : Prog} {Cl : State → Prop} {Ctx : FragS isaLSE2} {L0 : Lbl}
    {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop} {fs : List TermRun.Frame}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {J0 : Spike.Lib.A64.Flow.AS → Ctl → Prop}
    (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hF : Spike.Lib.A64.Flow.FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -288)
    (hhi : 0 ≤ R.hi) (hK : (ms fs).K = some abi) (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hctl : ∀ σC c0, (wX (ms fs) L.lab J0 .abort).J σC c0 →
      ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧ (∀ s, PlacedSE L.Λ L0 s c0 fs) ∧
        HeapAbortOblA ar.cells ar.ctr c0)
    (hab : ∀ s : State, s.st.2 = L.lab "scc_rt_abort_heap_exit" → (ms fs).abortAt s)
    (hX0 : ∀ s, inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    WcHAbStub (W0 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) ar p DtW (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.A64.ThreadsAb.Ac L.lab pfxM) Ctx L0 ls0 frM X0) (fun _ _ => False) p lbl ms L.exe L.endPc R F
      fs J0 := by
  intro m0 σC c0 hJ
  obtain ⟨hc0, hpl, hobl⟩ := hctl σC c0 hJ
  have hkc : (-240 : Int) < R.hi := by omega
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ -240 + -48 by omega) (by decide) hkc
  have hal' : (R.callee (-240) (-48) 0).base.toNat % 16 = 0 := by
    have : (((R.callee (-240) (-48) 0).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
    omega
  exact Spike.Lib.A64.StubW.stubHRW_of_code L.lays rfl (hp ▸ abortIn_wake) hK
    (Spike.Lib.A64.Flow.fstable_enter hR hF (by omega) (by decide) hkc (by decide) (by omega) (by decide)
      (by decide))
    (hpathW_hab0 hp hlo hlab a hΛ (Region.callee_ok hR (by omega) (by decide) hkc (by omega)) hal'
      (by simp [Region.callee]) (by simp [Region.callee]) rfl hfs hcl hc0 hpl hobl hX0)
    fun s _ ⟨_, _, _, hpc, _⟩ => hab s hpc

end Spike.Lib.A64.WakePh

/-- info: 'Spike.Lib.A64.WakePh.hpathW_hab0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.hpathW_hab0

/-- info: 'Spike.Lib.A64.WakePh.wc_heapAbStub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.wc_heapAbStub
