/-
**hello.w's heap abort from `wc_main`'s box allocation inside `W0`, under the take move** (AArch64;
the twin of `A64WakeHAb`, `A64WakeHAbStub` and `A64WakeHAbStubK` at `SccCode.helloProg`):
the allocator's full exit `HelloWc.wXH .abort` jumps to `scc_rt_abort` with `x0 = 2` at `-304` in `wc_main`'s
region (frame `144` plus the allocator's `160`, wake's at `-240`); the dispatcher and `scc_rt_abort_heap` run in
the region below it and do not return. Their states are inside hello's level before the allocation
(`WakeWf.W0` at `ownGH`, the write tail `DtW`, hello's threads abort phase `HelloWf.AcH … pfxM`).

Program independent and reused: `Abort.Disp.seg_jabort2RW`, `StubW.stubHRW_of_code`, `WakePh.HPathW.map`,
`hpathW_hC`, `HAbStubK.hpathW_K`, `WakeWf.Wf.intro`, `blkW_noWrC`, `nodeW_noWrC`, `nodeW_noWr_svc`,
`blkW_abortWf`, `nodeW_abortWf_off`, `hpcOf`, `AllocG.blkW_noWr`, `nodeW_noWr_si`, `Flow.fstable_enter`.

- `WcHAbStubH`, `wc_heapAb_segWSH`: the heap abort path's obligations below `-304`, and the heap abort's segment
  with no return (`wc_heapAb_segWS` at `wXH`, `R.lo ≤ -352`).
- `lab_neH`, `hpathW_hNH`, `nodeW_exAbWfH`, `hpathW_hAbH`, `hpathW_hXH`: the path's components.
- `hpathW_hab0H`: `HPathW` inside `W0` at `ownGH`/`AcH`.
- `abort_offH`, `x0WH_abort`: `scc_rt_abort`'s code is off the clone and the take site, so `X0WH` holds there.
- `wc_heapAbStubKH`: `WcHAbStubH` under `PhRec.K`.
-/
import Spike.Lib.A64HelloHAbWf
import Spike.Lib.A64HelloWfHPA
import Spike.Lib.A64HelloWcPre
import Spike.Lib.A64HelloStartGlue
import Spike.Lib.A64WakeHAbStubK

namespace Spike.Lib.A64.HelloPh.HAbStub

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq blockAt okPcOf)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Cert.Rt.A64.Print (add4 add0)
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Spike.Lib (Arena FragS Frag Region HeapAbortOblA SegWS)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.Abort (NT)
open Spike.Lib.A64.Abort.Disp (DN HPathW)
open Spike.Lib.A64.WakeWf (DtW Wf W0 NoWrC AbortWf RunWf)
open Spike.Lib.A64.Flow.HelloWc (wXH)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib.A64.HelloPh (lo ownGH instOkH abH_labsH abPHH abortPhHH hpathW_habGH)

set_option linter.unusedSimpArgs false

/-! ## The heap abort's segment -/

section Tail

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The heap abort's obligations** in `wc_main`'s region `R` under `F`, at the frames `fs`: the heap abort
path's below `-304` (`wXH .abort`'s offset) for every caller's state and source control of the node. -/
def WcHAbStubH (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (J1 : Flow.AS → Ctl → Prop) : Prop :=
  ∀ m0 σC c0, (wXH (ms fs) (_root_.Executable.labels exe).label J1 .abort).J σC c0 →
    Abort.Disp.StubHRW (fun s c => W s c fs) K p lbl (ms fs) exe endPc (R.callee (-304) (-48) 0)
      (fun m => F m ∧ Flow.CKept R (-304) (-48) 0 m0 m ∧ Flow.Abs R ⟨-304, []⟩ m0 σC) c0
      ((_root_.Executable.labels exe).label ".L2_scc_rt_alloc.4_full" + 8).toBitVec

/-- **The heap abort does not return**: from `wXH .abort` in `wc_main`'s region at the frames `fs`, into any
fragment (`seg_jabort2RW` at `-304`; the return address `x30` is `wXH .abort`'s). -/
theorem wc_heapAb_segWSH {W : FragS isaLSE2} {K : State → State → Prop} {fs : List TermRun.Frame}
    {J1 : Flow.AS → Ctl → Prop}
    (hF : Flow.FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -352) (hhi : 0 ≤ R.hi)
    (hK : (ms fs).K = some Scc.Sem.A64.abi) (hstub : WcHAbStubH W K p lbl ms exe endPc R F fs J1)
    (Q : FragS isaLSE2) :
    SegWS W K p lbl ms ((At exe endPc R F (wXH (ms fs) (_root_.Executable.labels exe).label J1 .abort)).at fs) Q :=
  SegWS.liftS_noret fs (Abort.Disp.seg_jabort2RW (Q := fun _ _ => False)
    (nC := wXH (ms fs) (_root_.Executable.labels exe).label J1 .abort) rfl
    (fun σ c h => by show σ.regs.X0.toBitVec.toNat = 2; rw [h.1]; rfl) (fun σ c h => h.2.1)
    hF hR hal (by show R.lo ≤ -304 - 48; omega) (by show (-304 : Int) < R.hi; omega)
    (by show (-304 : Int) % 16 = 0; decide) hK hstub) (fun _ _ h => h) Q

end Tail

/-! ## The path's components -/

variable {L : RuntimeLayout} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}

section Inst

variable (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
include hp hlo hlab

omit hp hlo in
/-- **Two labels' pcs differ** when their code addresses do (`hd`, decided on `codeT` with no address in the
text), the first resolved (`hs`). -/
theorem lab_neH {l l' : Label}
    (hd : codeT lo SccCode.helloProg l' ≠ (codeT lo SccCode.helloProg l).map fun y => (Int64.ofNat y).toBitVec.toNat)
    (hs : (codeT lo SccCode.helloProg l).isSome = true) {x : Nat} (hx : codeOf lo SccCode.helloProg l' = some x) :
    (L.lab l).toBitVec.toNat ≠ x := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
  rw [codeT_eq] at hy hd
  rw [hlab _ _ hy]
  intro h
  exact hd (by rw [hx, hy, Option.map_some, h])

/-- **No write to the arena or the counter** at every node of the path. -/
theorem hpathW_hNH {ar : Arena} {p : Prog} {L0 : Lbl} {ls0 : Lsize} {Ctx : FragS isaLSE2}
    {fs : List TermRun.Frame} (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -48)
    (hhi : 0 ≤ R.hi) :
    HPathW (NoWrC ar p L0 ls0 Ctx fs) (fun _ _ => False) L.exe L.endPc R F c0 ra := by
  have hI := instOkH hp hlo a (fun _ => False) (Spike.Lib.A64.HelloPh.siteH hp hlo hlab) (rS := ⟨0, 0⟩)
  have hsd := SccCode.hello_abort
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

/-- **The exit call is the heap abort's site** with exit status `101`, the caller's heap abort obligation
(`hobl`) at the source's unmoved control. -/
theorem nodeW_exAbWfH {ar : Arena} {Ab Ac : State → Prop} {fs : List TermRun.Frame}
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hobl : HeapAbortOblA ar.cells ar.ctr c0) :
    NodeW (fun s c => AbortWf ar (Spike.Lib.A64.PhRec.μ L) Ab Ac s c fs) (fun _ _ => False) L.exe L.endPc R F
      (NT L.lab Abort.heap c0 ra .ex) := by
  rintro s c ⟨-, -, -, hpc, σ, hA, -, hJ⟩
  have hd : Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup σ.regs.X0.toNat) := by
    rw [← Spike.Lib.A64.Flow.svcCall_exitGroup (by rw [hJ.2.1]; rfl), Spike.Lib.A64.Flow.svcCall, ← hA.regs]; rfl
  refine ⟨fun k x hx hpcs => ⟨?_, fun v hv => ?_⟩, fun _ h => h⟩
  · have hx' : codeOf lo SccCode.helloProg (Scc.Cert.Link.abortName k) = some x := by
      have h' : codeOf L.Λ.code.lo L.prog (L.Λ.abortLbl k) = some x := hx
      rwa [hp, hlo, hΛ] at h'
    have hpx : (L.lab Abort.heap.exit).toBitVec.toNat = x := by rw [← hpcs]; unfold pcOf; rw [hpc]; rfl
    cases k
    · exact absurd hpx (lab_neH hlab (by decide +kernel) (by decide +kernel) hx')
    · exact .inr (.inr (.inl ⟨rfl, by rw [hJ.1.1]; exact hobl⟩))
    · exact absurd hpx (lab_neH hlab (by decide +kernel) (by decide +kernel) hx')
    · exact absurd hpx (lab_neH hlab (by decide +kernel) (by decide +kernel) hx')
    · exact absurd hpx (lab_neH hlab (by decide +kernel) (by decide +kernel) hx')
  · rw [hd] at hv
    cases hv
    rw [hJ.2.2]
    rfl

/-- **The abort sites at every node of the path**: off them but at the exit call (`nodeW_exAbWfH`), by the
path's phase checks (`abortPhHH`). -/
theorem hpathW_hAbH {ar : Arena} {Ab Ac : State → Prop} {fs : List TermRun.Frame}
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hobl : HeapAbortOblA ar.cells ar.ctr c0) :
    HPathW (fun s c => AbortWf ar (Spike.Lib.A64.PhRec.μ L) Ab Ac s c fs) (fun _ _ => False) L.exe L.endPc R F
      c0 ra := by
  have hI := instOkH hp hlo 0 (fun _ => False) (Spike.Lib.A64.HelloPh.siteH hp hlo hlab) (rS := ⟨0, 0⟩)
  have hphs := abortPhHH (Λ := L.Λ) (lab := L.lab) hΛ hlab
  simp only [Spike.Lib.A64.StubW.abortPhHeapOk, Spike.Lib.A64.StubW.phOne, Bool.and_eq_true, beq_iff_eq,
    and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pg2, pb0, o1, -, o1b, -, pb1, o7, -, pb2, -⟩ := hphs
  have hb : ∀ {n : ND} {blk : List Directive} {lo' hi' : Int} {l : Label} {k : Nat},
      L.lab l + Int64.ofNat (4 * k) = n.pc → Spike.Lib.A64.Flow.okBlk lo' hi' n.o blk = true →
      Spike.Lib.A64Consumer.blkPh (okPcOf lo SccCode.helloProg L.Λ) Spike.Lib.A64.HelloPh.phH (fun _ => false)
        L.lab (L.lab l + Int64.ofNat (4 * k)) 0 blk = true →
      Spike.Lib.A64Consumer.noRetBlk blk = true →
      BlkW (fun s c => AbortWf ar (Spike.Lib.A64.PhRec.μ L) Ab Ac s c fs) (fun _ _ => False) L.exe L.endPc R F
        n blk := fun he hok hph hnr =>
    Spike.Lib.A64.WakeWf.blkW_abortWf (Spike.Lib.A64.WakeWf.hpcOf hI hok (he ▸ hph) hnr)
  have hn : ∀ {n : ND} {q : Int64}, n.pc = q → okPcOf lo SccCode.helloProg L.Λ q.toBitVec.toNat = true →
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
  · exact nodeW_exAbWfH hp hlo hlab hΛ hobl

omit hp hlo in
/-- **The path's states are in `scc_rt_abort`'s code** (`abPHH`'s `AbP`). -/
theorem hpathW_hXH (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) :
    HPathW (fun s _ => Spike.Lib.A64.WakePh.inPc L "scc_rt_abort" "scc_rt_thr_worker" s) (fun _ _ => False)
      L.exe L.endPc R F c0 ra := by
  have hsd := SccCode.hello_abort
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  obtain ⟨e1, e2, -, -, -, -, -, -, -, e10, -, -, -, -, -⟩ := abH_labsH hlab
  have hP := abPHH (μ := Spike.Lib.A64.PhRec.μ L) (F := F) (c0 := c0) (ra := ra) hlab hR hal hlo' hhi
    (fun a' ha => by
      have h' : codeOf L.Λ.code.lo L.prog "scc_rt_take_site" = some a' := ha
      rw [hp, hlo, e10] at h'
      cases h'
      rw [e1, e2]; decide)
    (Scc.Cert.Rt.A64.Abort.code_disp L.lays rfl (hp ▸ hsd.2))
    (Scc.Cert.Rt.A64.Abort.code_stub L.lays rfl (hp ▸ hsd.1.1.1.1.2))
  exact Spike.Lib.A64.WakePh.HPathW.map (W₁ := Spike.Lib.A64.WakePh.AbW L R ra (Spike.Lib.A64.PhRec.μ L))
    ⟨hP.de, hP.dt1, hP.dj1, hP.dt2, hP.dg2, hP.se, hP.sn1, hP.sn1b, hP.sn2, hP.ssvc, hP.sn5, hP.sex⟩
    fun _ _ h => h.1.1

/-- **The heap path inside `W0`** at `ownGH`, `AcH`, the write tail `DtW`, the frames `fs` (`[]` or `[frM]`,
`hfs`), from a caller with the return address past `scc_rt_alloc`'s full branch (`hra`): the components of `Wf`
at every node, the control's facts, its frames' placement and the heap abort's obligation at the caller's
control `c0` (`hc0`, `hpl`, `hobl`), the clone path's global clause (`hcl`), the per-state facts `X0` in
`scc_rt_abort`'s code (`hX0`). -/
theorem hpathW_hab0H {ar : Arena} {p : Prog} {Cl : State → Prop} {Ctx : FragS isaLSE2} {L0 : Lbl} {ls0 : Lsize}
    {frM : TermRun.Frame} {X0 : State → Prop} {fs : List TermRun.Frame} (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hra : ra = (L.lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec)
    (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hc0 : (fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) (hpl : ∀ s, PlacedSE L.Λ L0 s c0 fs)
    (hobl : HeapAbortOblA ar.cells ar.ctr c0)
    (hX0 : ∀ s, Spike.Lib.A64.WakePh.inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    HPathW (fun s c => W0 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) ar p DtW (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.A64.HelloWf.AcH L.lab pfxM) Ctx L0 ls0 frM X0 s c fs) (fun _ _ => False) L.exe L.endPc R F
      c0 ra := by
  have hsite := Spike.Lib.A64.HelloPh.siteH hp hlo hlab
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, e12, e13, e14, -⟩ := abH_labsH hlab
  have hG := hpathW_habGH hp hlo hsite (Λ := L.Λ) (F := F) (c0 := c0) (ra := ra) a hΛ hlab hR hal hlo' hhi
    (fun h => absurd (hra.symm.trans h) (by rw [e12, e13]; decide)) (by rw [hra, e12, e14]; decide)
  have hPh := Spike.Lib.A64.HelloWf.hpathW_phH (Cl := Cl) (F := F) (c0 := c0) (ra := ra)
    (instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)) (hp ▸ SccCode.hello_abort)
    (abortPhHH (Λ := L.Λ) (lab := L.lab) hΛ hlab) hlab hR hal hlo' hhi
    (fun a' ha => by
      have h' : codeOf L.Λ.code.lo L.prog "scc_rt_take_site" = some a' := ha
      rw [hp, hlo] at h'
      exact lab_neH hlab (by decide +kernel) (by decide +kernel) h')
    (hra ▸ Spike.Lib.A64.HelloWf.hra_allocH hlab)
  have hN := hpathW_hNH (ar := ar) (p := p) (L0 := L0) (ls0 := ls0) (Ctx := Ctx) (fs := fs) (F := F) (c0 := c0)
    (ra := ra) hp hlo hlab a hR hal hlo' hhi
  have hAb := hpathW_hAbH (ar := ar) (Ab := Spike.Lib.A64.WriteAb.Ab L.lab)
    (Ac := Spike.Lib.A64.HelloWf.AcH L.lab pfxM) (fs := fs) (R := R) (F := F) (ra := ra) hp hlo hlab hΛ hobl
  have hX := hpathW_hXH (F := F) (c0 := c0) (ra := ra) hlab hR hal hlo' hhi hp hlo
  have h1 := Spike.Lib.A64.Abort.Disp.HPathW.and hG hPh fun s c h₁ h₂ => And.intro h₁ h₂
  have h2 := Spike.Lib.A64.Abort.Disp.HPathW.and h1 Spike.Lib.A64.WakePh.hpathW_hC
    fun s c h₁ h₂ => And.intro h₁ h₂
  have h3 := Spike.Lib.A64.Abort.Disp.HPathW.and h2 hN fun s c h₁ h₂ => And.intro h₁ h₂
  have h4 := Spike.Lib.A64.Abort.Disp.HPathW.and h3 hAb fun s c h₁ h₂ => And.intro h₁ h₂
  refine Spike.Lib.A64.Abort.Disp.HPathW.and h4 hX fun s c h hx => ?_
  obtain ⟨⟨⟨⟨hst, hab, hac⟩, hc⟩, hw⟩, habt⟩ := h
  subst hc
  exact ⟨hfs, hX0 s hx, Spike.Lib.A64.WakeWf.Wf.intro hst hab hac hcl hc0.1 (hpl s) hw.1 hw.2 hc0.2 habt⟩

/-! ## Under the take move -/

omit hp hlo in
/-- **`scc_rt_abort`'s code is off hello's clone and the take site.** -/
theorem abort_offH (s : State) (h : Spike.Lib.A64.WakePh.inPc L "scc_rt_abort" "scc_rt_thr_worker" s) :
    pcOf s ≠ Spike.Lib.HelloPreA.clonePcH L ∧
      pcOf s ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  obtain ⟨e1, e2, -, -, -, -, -, -, -, -, -, -, -, -, e15⟩ := abH_labsH hlab
  have hsite : (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat = 2165976 := by
    rw [hlab _ 2165976 (by rw [← codeT_eq]; decide +kernel)]; decide
  have hcl : Spike.Lib.HelloPreA.clonePcH L = 2169840 := by
    show (L.lab (".L22_wc_main" ++ ".sp6") + Int64.ofNat (4 * 25)).toBitVec.toNat = 2169840
    rw [show (".L22_wc_main" ++ ".sp6" : String) = ".L22_wc_main.sp6" from rfl, e15]; decide
  obtain ⟨h1, h2⟩ := h
  rw [e1] at h1
  rw [e2] at h2
  have h1' : 2168032 ≤ pcOf s := by simpa using h1
  have h2' : pcOf s < 2168596 := by simpa using h2
  rw [hcl, hsite]
  omega

omit hp hlo in
/-- **`X0WH` in `scc_rt_abort`'s code**, at any take address `a` resolving to the site. -/
theorem x0WH_abort {a : Int64}
    (ha : a.toBitVec.toNat = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    ∀ s, Spike.Lib.A64.WakePh.inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0WH L a s := fun s h =>
  ⟨(abort_offH hlab s h).1, fun he => absurd (he.trans ha) (abort_offH hlab s h).2⟩

/-- **`WcHAbStubH` under the take move** (at `PhRec.K L rS`): the path inside `W0` at `ownGH`/`AcH` and in
`scc_rt_abort`'s code (`hpathW_hXH`), whose pcs are off the take site. -/
theorem wc_heapAbStubKH {R : Region} {F : MachineData → Prop} {ar : Arena} {p : Prog} {Cl : State → Prop}
    {Ctx : FragS isaLSE2} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop}
    {fs : List TermRun.Frame} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop} {rS : Scc.Sem.Range} (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hF : Spike.Lib.A64.Flow.FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -352)
    (hhi : 0 ≤ R.hi) (hK : (ms fs).K = some abi) (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hctl : ∀ σC c0, (wXH (ms fs) L.lab J1 .abort).J σC c0 →
      ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧ (∀ s, PlacedSE L.Λ L0 s c0 fs) ∧
        HeapAbortOblA ar.cells ar.ctr c0)
    (hab : ∀ s : State, s.st.2 = L.lab "scc_rt_abort_heap_exit" → (ms fs).abortAt s)
    (hX0 : ∀ s, Spike.Lib.A64.WakePh.inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    WcHAbStubH (W0 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) ar p DtW (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.A64.HelloWf.AcH L.lab pfxM) Ctx L0 ls0 frM X0) (Spike.Lib.A64.PhRec.K L rS) p lbl ms L.exe
      L.endPc R F fs J1 := by
  intro m0 σC c0 hJ
  obtain ⟨hc0, hpl, hobl⟩ := hctl σC c0 hJ
  have hkc : (-304 : Int) < R.hi := by omega
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ -304 + -48 by omega) (by decide) hkc
  have hal' : (R.callee (-304) (-48) 0).base.toNat % 16 = 0 := by
    have : (((R.callee (-304) (-48) 0).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
    omega
  have hR' := Region.callee_ok (hi' := 0) hR (show R.lo ≤ -304 + -48 by omega) (by decide) hkc (by omega)
  have h0 := hpathW_hab0H (ar := ar) (p := p) (Cl := Cl) (Ctx := Ctx) (L0 := L0) (ls0 := ls0) (frM := frM)
    (X0 := X0) (F := fun m => F m ∧ Spike.Lib.A64.Flow.CKept R (-304) (-48) 0 m0 m ∧
      Spike.Lib.A64.Flow.Abs R ⟨-304, []⟩ m0 σC) hp hlo hlab a hΛ hR' hal'
    (by simp [Region.callee]) (by simp [Region.callee]) rfl hfs hcl hc0 hpl hobl hX0
  have hX := hpathW_hXH (F := fun m => F m ∧ Spike.Lib.A64.Flow.CKept R (-304) (-48) 0 m0 m ∧
      Spike.Lib.A64.Flow.Abs R ⟨-304, []⟩ m0 σC) (c0 := c0)
    (ra := (L.lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec) hlab hR' hal' (by simp [Region.callee])
    (by simp [Region.callee]) hp hlo
  have hpath := Spike.Lib.A64.WakePh.HPathW.map (Spike.Lib.A64.WakePh.HAbStubK.hpathW_K
    (K := Spike.Lib.A64.PhRec.K L rS)
    (Spike.Lib.A64.Abort.Disp.HPathW.and h0 hX fun _ _ h₁ h₂ => And.intro h₁ h₂)
    fun s _ h s' hk => (abort_offH hlab s h.2).2 (congrArg (fun x : Int64 => x.toBitVec.toNat) hk.1))
    fun _ _ h => h.1
  exact Spike.Lib.A64.StubW.stubHRW_of_code L.lays rfl (hp ▸ SccCode.hello_abort) hK
    (Spike.Lib.A64.Flow.fstable_enter hR hF (by omega) (by decide) hkc (by decide) (by omega) (by decide)
      (by decide)) hpath fun s _ ⟨_, _, _, hpc, _⟩ => hab s hpc

end Inst

end Spike.Lib.A64.HelloPh.HAbStub

/-- info: 'Spike.Lib.A64.HelloPh.HAbStub.wc_heapAb_segWSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HAbStub.wc_heapAb_segWSH

/-- info: 'Spike.Lib.A64.HelloPh.HAbStub.hpathW_hab0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HAbStub.hpathW_hab0H

/-- info: 'Spike.Lib.A64.HelloPh.HAbStub.x0WH_abort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HAbStub.x0WH_abort

/-- info: 'Spike.Lib.A64.HelloPh.HAbStub.wc_heapAbStubKH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HAbStub.wc_heapAbStubKH
