/-
**hello.w's heap abort from `wc_main`'s box allocation inside `W0`** (x86-64; the twin of
`Spike/Lib/A64HelloHAbStub.lean`, at the template of `X64WakeHAbStub` and `X64WakeHAbStubK` at
`SccCode.helloCells`): the allocator's full exit jumps to `scc_rt_abort(2)`; the dispatcher and
`scc_rt_abort_heap` run in the region below it and do not return. Their states are inside hello's level
before the allocation (`WakeWf.W0` at `ownGH`, the write tail `DtW`, hello's threads abort phase
`Hello.ThreadsAb.AcH … pfxM`), from the components of `WakeWf.Wf` at every node of `Abort.Disp.HPathW`.

Program independent and reused: `WakePh.HPathW.map`, `WakePh.hpathW_hC`, `WakeWf.Wf.intro`, `blkW_noWrC`,
`nodeW_noWrC`, `nodeW_noWr_svc`, `blkW_abortWf`, `abortWf_of_off`, `hpcOf`, `AllocG.blkW_noWr`,
`AllocG.nodeW_noWr_si`.

- `hpathW_hNH`, `nodeW_exAbWfH`, `hpathW_hAbH`, `hpathW_hXH`: the path's components.
- `hpathW_hab0H`: `HPathW` inside `W0` at `ownGH`/`AcH`.
- `abort_offH`, `x0WH_abort`: `scc_rt_abort`'s code is off the clone and the take site, so `X0WH` holds there.

Unlike AArch64, the stub's `leaq` is one node (no `n1b`, so `HPathW` has 11 obligations), the `write` and
exit calls are `syscall`s (the exit status in `%rdi`); the exit call's site is told apart from the other
abort sites on the resolved exit address (`abH_labsH`, `4202798`), as `X64WakeHAbStub.nodeW_exAbWf`, so
A64's `lab_neH` has no twin; the region is `[-24, 16)` with no alignment premise; the return address is
`.Lscc_rt_alloc.full + 12` (A64's `.L2_scc_rt_alloc.4_full + 8`) and `ownGH`'s two return points are
`.Lscc_rt_alloc_tcb.x0`, `.Lwc_main.x5` (A64's `.sp13`, `.sp11`); the clone is the `syscall` at
`.Lwc_main.x3 + 94` (`clone_inCvH`).

Not twinned (unreachable from the AArch64 root `hello_linkedA`, so twins only live constants):
`WcHAbStubH`, `wc_heapAb_segWSH`, `wc_heapAbStubKH`.
-/
import Spike.Lib.X64HelloHAbWf
import Spike.Lib.X64HelloWfHPA
import Spike.Lib.X64HelloStartGlue
import Spike.Lib.X64HelloStartWfL
import Spike.Lib.X64HelloStart
import Spike.Lib.X64WakeHAbStub

namespace Spike.Lib.X64.HelloPh.HAbStub

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq okPcOf code_field)
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (helloCells)
open Spike.Lib (Arena FragS Frag Region HeapAbortOblA)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND BlkW NodeW okBlk)
open Spike.Lib.X64.Abort (NT)
open Spike.Lib.X64.Abort.Disp (HPathW)
open Spike.Lib.X64.WakeWf (DtW W0 NoWrC AbortWf RunWf)
open Spike.Lib.X64.WakePh (inPc)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.StartWf (pfxM)
open Spike.Lib.X64.HelloPh (lo ownGH instOkH siteH abH_labsH ab_labsH abPHH abortPhHH hpathW_habGH)
open Spike.Lib.X64.HelloPh.WcW (cvH clone_inCvH lab_cvH)
open Spike.Lib.X64.Flow (ofNat_zero')

set_option linter.unusedSimpArgs false

variable {L : RuntimeLayout} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}

section Inst

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
include hp hlo hlab

/-- **No write to the arena or the counter** at every node of the path: its blocks are silent
(`AllocG.blkW_noWr`), its other nodes a `leaq` and two `syscall`s. -/
theorem hpathW_hNH {ar : Arena} {p : Prog} {L0 : Lbl} {ls0 : Lsize} {Ctx : FragS isa}
    {fs : List TermRun.Frame} (a : BitVec 64) (hR : R.OK) (hlo' : R.lo ≤ -24) (hhi : 16 ≤ R.hi) :
    HPathW (NoWrC ar p L0 ls0 Ctx fs) (fun _ _ => False) L.exe L.endPc R F c0 ra := by
  have hI := instOkH hp hlo a (fun _ => False) (siteH hp hlo hlab) (rS := ⟨0, 0⟩)
  have hsd := SccCode.hello_abort
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, -, hg2, -⟩ := hdi
  have hst := hsd.1.1.1.1.2
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hx0, hn1, hx1, hsysIn, hx2, hx, -, -⟩ := hst
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hd0)
      (ofNat_zero' _) Abort.Disp.d0_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact ht1)
      (ofNat_zero' _) Abort.Disp.t1_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hj1)
      rfl Abort.Disp.j1_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact ht2)
      (ofNat_zero' _) Abort.Disp.t2_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hg2)
      (ofNat_zero' _) Abort.Disp.g2_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hx0)
      (ofNat_zero' _) Abort.x0_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.nodeW_noWrC (Spike.Lib.X64.AllocG.nodeW_noWr_si hI (by rw [hp]; exact hn1) rfl
      (ofNat_zero' _).symm)
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hx1)
      rfl Abort.x1Heap_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.nodeW_noWrC (Spike.Lib.X64.WakeWf.nodeW_noWr_svc
      (code_field L.lays rfl (by rw [hp]; exact hsysIn) rfl))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hx2)
      rfl Abort.x2_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.nodeW_noWrC (Spike.Lib.X64.WakeWf.nodeW_noWr_svc
      (code_field L.lays rfl (by rw [hp]; exact hx) (ofNat_zero' _)))

/-- **The exit call is the heap abort's site** with exit status `101` (`%rax = 231`, `%rdi = 101`), the
caller's heap abort obligation (`hobl`) at the source's unmoved control. -/
theorem nodeW_exAbWfH {ar : Arena} {Ab Ac : State → Prop} {fs : List TermRun.Frame}
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hobl : HeapAbortOblA ar.cells ar.ctr c0) :
    NodeW (fun s c => AbortWf ar (Spike.Lib.X64.PhRec.μ L) Ab Ac s c fs) (fun _ _ => False) L.exe L.endPc R F
      (NT L.lab Abort.heap c0 ra .ex) := by
  rintro s c ⟨-, -, -, hpc, σ, hA, -, hJ⟩
  obtain ⟨⟨hc, -⟩, h231, h101⟩ := hJ
  have hr : s.st.1.regs.rax.toNat = 231 := by
    rw [← hA.regs] at h231
    simp only [Reg64s.get64] at h231
    rw [← UInt64.toNat_toBitVec, h231]; rfl
  have hrdi : s.st.1.regs.rdi.toNat = 101 := by
    rw [← hA.regs] at h101
    simp only [Reg64s.get64] at h101
    rw [← UInt64.toNat_toBitVec, h101]; rfl
  have hd : Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup s.st.1.regs.rdi.toNat) := by
    rw [← Spike.Lib.X64.syscallCall_exitGroup hr]; rfl
  have e : ∀ k, (Spike.Lib.X64.PhRec.μ L).abortAt k = codeLabel lo helloCells (Scc.Cert.Link.abortName k) :=
    fun k => by show codeLabel L.Λ.code.lo L.prog (L.Λ.abortLbl k) = _; rw [hp, hlo, hΛ]
  obtain ⟨-, h2⟩ := abH_labsH hlab
  have hc' : c = c0 := hc
  refine ⟨fun k x hx hpcs => ⟨?_, fun v hv => ?_⟩, fun _ h => h⟩
  · have hpx : x = 4202798 := by
      rw [← hpcs]; unfold pcOf; rw [hpc]; simp only [NT, Abort.N, Abort.heap, h2]; decide
    subst hpx
    rw [e, ← codeT_eq] at hx
    cases k <;> first
      | exact absurd hx (by decide +kernel)
      | exact .inr (.inr (.inl ⟨rfl, by rw [hc']; exact hobl⟩))
  · rw [hd] at hv; cases hv; rw [hrdi]; rfl

/-- **The abort sites at every node of the path**: off them but at the exit call (`nodeW_exAbWfH`), by the
path's phase checks (`abortPhHH`). -/
theorem hpathW_hAbH {ar : Arena} {Ab Ac : State → Prop} {fs : List TermRun.Frame}
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hobl : HeapAbortOblA ar.cells ar.ctr c0) :
    HPathW (fun s c => AbortWf ar (Spike.Lib.X64.PhRec.μ L) Ab Ac s c fs) (fun _ _ => False) L.exe L.endPc R F
      c0 ra := by
  have hI := instOkH hp hlo 0 (fun _ => False) (siteH hp hlo hlab) (rS := ⟨0, 0⟩)
  have hphs := abortPhHH (Λ := L.Λ) (lab := L.lab) hΛ hlab
  simp only [Spike.Lib.X64.StubW.abortPhHeapOk, Spike.Lib.X64.StubW.phOne, Bool.and_eq_true, beq_iff_eq,
    and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pg2, px0, o1, -, px1, o34, -, px2, -⟩ := hphs
  have hb : ∀ {n : ND} {blk : List (Directive × Nat)} {lo' hi' : Int} {l : Label} {k : Nat},
      L.lab l + Int64.ofNat k = n.pc → okBlk lo' hi' n.o blk = true →
      Spike.Lib.X64Consumer.blkPh (okPcOf lo helloCells L.Λ) Spike.Lib.X64.HelloPh.phH (fun _ => false) L.lab
        (L.lab l + Int64.ofNat k) 0 blk = true →
      Spike.Lib.X64Consumer.noRetBlk blk = true →
      BlkW (fun s c => AbortWf ar (Spike.Lib.X64.PhRec.μ L) Ab Ac s c fs) (fun _ _ => False) L.exe L.endPc R F
        n blk := fun he hok hph hnr =>
    Spike.Lib.X64.WakeWf.blkW_abortWf (Spike.Lib.X64.WakeWf.hpcOf hI hok (he ▸ hph) hnr)
  have hn : ∀ {n : ND} {q : Int64}, n.pc = q → okPcOf lo helloCells L.Λ q.toBitVec.toNat = true →
      NodeW (fun s c => AbortWf ar (Spike.Lib.X64.PhRec.μ L) Ab Ac s c fs) (fun _ _ => False) L.exe L.endPc R F
        n := by
    intro n q hq hok
    rintro s c ⟨-, -, -, hpc, -⟩
    have hP := (hI.off s (by unfold pcOf; rw [hpc, hq]; exact hok)).1
    exact ⟨Spike.Lib.X64.WakeWf.abortWf_of_off hP.noAbort, fun _ h => h⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hb (ofNat_zero' _) Abort.Disp.d0_ok pd0 (by decide)
  · exact hb (ofNat_zero' _) Abort.Disp.t1_ok pt1 (by decide)
  · exact hb rfl Abort.Disp.j1_ok pj1 (by decide)
  · exact hb (ofNat_zero' _) Abort.Disp.t2_ok pt2 (by decide)
  · exact hb (ofNat_zero' _) Abort.Disp.g2_ok pg2 (by decide)
  · exact hb (ofNat_zero' _) Abort.x0_ok px0 (by decide)
  · exact hn (ofNat_zero' _).symm o1
  · exact hb rfl Abort.x1Heap_ok px1 (by decide)
  · exact hn rfl o34
  · exact hb rfl Abort.x2_ok px2 (by decide)
  · exact nodeW_exAbWfH hp hlo hlab hΛ hobl

/-- **The path's states are in `scc_rt_abort`'s code** (`abPHH`'s `AbP`). -/
theorem hpathW_hXH (hR : R.OK) (hlo' : R.lo ≤ -24) (hhi : 16 ≤ R.hi) :
    HPathW (fun s _ => inPc L "scc_rt_abort" "scc_rt_thr_worker" s) (fun _ _ => False) L.exe L.endPc R F
      c0 ra := by
  have hsd := SccCode.hello_abort
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  obtain ⟨e1, e2, -⟩ := ab_labsH hlab
  have hP := abPHH (μ := Spike.Lib.X64.PhRec.μ L) (F := F) (c0 := c0) (ra := ra) hlab hR hlo' hhi
    (fun a' ha => by
      have e : L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200314 :=
        hlab _ _ (by rw [← codeT_eq]; decide +kernel)
      rw [siteH hp hlo hlab] at ha; cases ha
      rw [e, e1, e2]; decide)
    (Scc.Cert.Rt.X64.Abort.code_disp L.lays rfl (by rw [hp]; exact hsd.2))
    (Scc.Cert.Rt.X64.Abort.code_stub L.lays rfl (by rw [hp]; exact hsd.1.1.1.1.2))
  exact Spike.Lib.X64.WakePh.HPathW.map (W₁ := Spike.Lib.X64.WakePh.AbW L R ra (Spike.Lib.X64.PhRec.μ L))
    ⟨hP.de, hP.dt1, hP.dj1, hP.dt2, hP.dg2, hP.se, hP.sn1, hP.sn2, hP.ssvc, hP.sn5, hP.sex⟩
    fun _ _ h => h.1.1

/-- **The heap path inside `W0`** at `ownGH`, `AcH`, the write tail `DtW`, the frames `fs` (`[]` or `[frM]`,
`hfs`), from a caller with the return address past `scc_rt_alloc`'s full branch (`hra`): the components of `Wf`
at every node, the control's facts, its frames' placement and the heap abort's obligation at the caller's
control `c0` (`hc0`, `hpl`, `hobl`), the clone path's global clause (`hcl`), the per-state facts `X0` in
`scc_rt_abort`'s code (`hX0`). -/
theorem hpathW_hab0H {ar : Arena} {p : Prog} {Cl : State → Prop} {Ctx : FragS isa} {L0 : Lbl} {ls0 : Lsize}
    {frM : TermRun.Frame} {X0 : State → Prop} {fs : List TermRun.Frame} (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hR : R.OK) (hlo' : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hra : ra = (L.lab Spike.Lib.X64.Alloc.fullL + 12).toBitVec) (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hc0 : (fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) (hpl : ∀ s, PlacedSE L.Λ L0 s c0 fs)
    (hobl : HeapAbortOblA ar.cells ar.ctr c0) (hX0 : ∀ s, inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    HPathW (fun s c => W0 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) ar p DtW (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab pfxM) Ctx L0 ls0 frM X0 s c fs) (fun _ _ => False) L.exe L.endPc
      R F c0 ra := by
  have hsite := siteH hp hlo hlab
  have ef : L.lab Spike.Lib.X64.Alloc.fullL = Int64.ofNat 4198788 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have e6 : L.lab ".Lscc_rt_alloc_tcb.x0" = Int64.ofNat 4199282 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have e27 : L.lab ".Lwc_main.x5" = Int64.ofNat 4203947 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have es : L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200314 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  obtain ⟨-, h2⟩ := abH_labsH hlab
  have hG := hpathW_habGH hp hlo hsite (Λ := L.Λ) (F := F) (c0 := c0) (ra := ra) a hΛ hlab hR hlo' hhi
    (fun h => absurd (hra.symm.trans h) (by rw [ef, e6]; decide)) (by rw [hra, ef, e27]; decide)
  have hPh := Spike.Lib.X64.HelloWf.hpathW_phH (Cl := Cl) (F := F) (c0 := c0) (ra := ra)
    (instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)) (by rw [hp]; exact SccCode.hello_abort)
    (abortPhHH (Λ := L.Λ) (lab := L.lab) hΛ hlab) hlab hR hlo' hhi
    (fun a' ha => by rw [hsite] at ha; cases ha; simp only [Abort.heap, h2, es]; decide)
    (by rw [hra]; exact Spike.Lib.X64.HelloWf.hra_allocH hlab)
  have hN := hpathW_hNH (ar := ar) (p := p) (L0 := L0) (ls0 := ls0) (Ctx := Ctx) (fs := fs) (F := F) (c0 := c0)
    (ra := ra) hp hlo hlab a hR hlo' hhi
  have hAb := hpathW_hAbH (ar := ar) (Ab := Spike.Lib.X64.WriteAb.Ab L.lab)
    (Ac := Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab pfxM) (fs := fs) (R := R) (F := F) (ra := ra) hp hlo hlab hΛ
    hobl
  have hX := hpathW_hXH (F := F) (c0 := c0) (ra := ra) hp hlo hlab hR hlo' hhi
  have h1 := Abort.Disp.HPathW.and hG hPh fun s c h₁ h₂ => And.intro h₁ h₂
  have h2' := Abort.Disp.HPathW.and h1 Spike.Lib.X64.WakePh.hpathW_hC fun s c h₁ h₂ => And.intro h₁ h₂
  have h3 := Abort.Disp.HPathW.and h2' hN fun s c h₁ h₂ => And.intro h₁ h₂
  have h4 := Abort.Disp.HPathW.and h3 hAb fun s c h₁ h₂ => And.intro h₁ h₂
  refine Abort.Disp.HPathW.and h4 hX fun s c h hx => ?_
  obtain ⟨⟨⟨⟨hst, hab, hac⟩, hc⟩, hw⟩, habt⟩ := h
  subst hc
  exact ⟨hfs, hX0 s hx, Spike.Lib.X64.WakeWf.Wf.intro hst hab hac hcl hc0.1 (hpl s) hw.1 hw.2 hc0.2 habt⟩

end Inst

/-! ## Off the clone and the take site -/

section Off

variable (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
include hlab

/-- **`scc_rt_abort`'s code is off hello's clone and the take site.** -/
theorem abort_offH (s : State) (h : inPc L "scc_rt_abort" "scc_rt_thr_worker" s) :
    pcOf s ≠ Spike.Lib.X64HelloPreA.clonePcH L ∧
      pcOf s ≠ (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  have lc : ∀ l, (codeLabel lo helloCells l).isSome = true ∧ cvH l < 2 ^ 64 →
      (L.lab l).toBitVec.toNat = cvH l := fun l h => lab_cvH hlab h.1 h.2
  obtain ⟨h1, h2⟩ := h
  rw [lc _ (by unfold cvH; rw [← codeT_eq]; decide +kernel)] at h1
  rw [lc _ (by unfold cvH; rw [← codeT_eq]; decide +kernel)] at h2
  have hc := clone_inCvH
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hs, hb⟩, -⟩ := hc
  have e : Spike.Lib.X64HelloPreA.clonePcH L = cvH ".Lwc_main.x3" + 94 := by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
    have ey : cvH ".Lwc_main.x3" = y := by simp [cvH, hy]
    rw [ey] at hb ⊢
    show (L.lab ".Lwc_main.x3" + 94).toBitVec.toNat = y + 94
    rw [hlab _ y hy]
    show (BitVec.ofNat 64 y + BitVec.ofNat 64 94).toNat = y + 94
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hcl : ¬ (cvH "scc_rt_abort" ≤ cvH ".Lwc_main.x3" + 94 ∧
      cvH ".Lwc_main.x3" + 94 < cvH "scc_rt_thr_worker") := by
    unfold cvH; rw [← codeT_eq]; decide +kernel
  have hst := lc Spike.Lib.X64.Flow.Ret0.StackTake.siteL (by unfold cvH; rw [← codeT_eq]; decide +kernel)
  have hsi : ¬ (cvH "scc_rt_abort" ≤ cvH Spike.Lib.X64.Flow.Ret0.StackTake.siteL ∧
      cvH Spike.Lib.X64.Flow.Ret0.StackTake.siteL < cvH "scc_rt_thr_worker") := by
    unfold cvH; rw [← codeT_eq]; decide +kernel
  refine ⟨fun he => hcl ?_, fun he => hsi ?_⟩
  · rw [← e, ← he]; exact ⟨h1, h2⟩
  · rw [← hst, ← he]; exact ⟨h1, h2⟩

/-- **`X0WH` in `scc_rt_abort`'s code**, at any take address `a` resolving to the site. -/
theorem x0WH_abort {a : Int64}
    (ha : a.toBitVec.toNat = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    ∀ s, inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0WH L a s := fun s h =>
  ⟨(abort_offH hlab s h).1, fun he => absurd (he.trans ha) (abort_offH hlab s h).2⟩

end Off

end Spike.Lib.X64.HelloPh.HAbStub

/-- info: 'Spike.Lib.X64.HelloPh.HAbStub.hpathW_hab0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HAbStub.hpathW_hab0H

/-- info: 'Spike.Lib.X64.HelloPh.HAbStub.x0WH_abort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HAbStub.x0WH_abort
