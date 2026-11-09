/-
**wake.w's heap abort path inside `W0`** (x86-64; the twin of
`Spike/Lib/A64WakeHAbStub.lean`): the obligations of
`Spike.Lib.X64.Flow.WakeWc.WcHAbStub` (`Spike/Lib/X64WakeHAb.lean`) at
wake's level before the allocation (`WakeWf.W0` at `ownG`, the write tail
`WakeWf.DtW`, no outside moves), from the components of `WakeWf.Wf` at every
node of `Abort.Disp.HPathW`:

- the state's facts at `ownG` (`hpathW_habG`), both abort phases
  (`WakeWf.hpathW_ph`), the per-state facts `X0` in `scc_rt_abort`'s code
  (`abPH`'s `AbP`);
- the source's control unmoved (`c = c0`), so the control's facts, the
  frames' placement and the heap abort's obligation are the caller's;
- no write to the arena or the counter (`AllocG.blkW_noWr`, the
  `syscall`s);
- the abort sites: every node off them but the exit call, which is the heap
  abort's site with exit status `101` (`nodeW_exAbWf`).

- `HPathW.map`, `hpathW_hC`, `hpathW_hN`, `hpathW_hAb`, `hpathW_hX`: the
  components.
- `hpathW_hab0`: `HPathW` inside `W0`.
- `wc_heapAbStub`: `WcHAbStub` at `W0` (`stubHRW_of_code` in the callee
  region `[-24, 16)` below `-240`).

**Where this differs from AArch64**: the stub's `leaq` is one node (no
`n1b`), the `write` and exit calls are `syscall`s (`nodeW_noWr_svc`; the
exit status in `%rdi`); the labels' pcs are compared on the resolved
addresses (`abH_labs`, the sites at `4200277`, `4200317`; A64's `lab_ne`);
the region is `[-24, 16)` with no alignment premise; the return address is
`raAb` (`.Lscc_rt_alloc.full + 12`, A64's `.L2_scc_rt_alloc.4_full + 8`) and
`ownG`'s two return points `.Lscc_rt_alloc_tcb.x0`, `.Lwc_main.x5` (A64's
`.sp13`, `.sp11`); `wc_heapAbStub`'s region is `R.callee (-240 - 8) (-24)
16`, so `R` needs `[-272, -232)` (A64's `R.lo ≤ -288`, `0 ≤ R.hi`, `hal`).
-/
import Spike.Lib.X64WakeHAbWf
import Spike.Lib.X64WakeHAb
import Spike.Lib.X64AbortHeapRWCode
import Spike.Lib.X64WakeWfG
import Spike.Lib.X64WakeStartEWF

namespace Spike.Lib.X64.WakePh

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq blockAtB okPcOf code_field)
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (wakeCells)
open Spike.Lib (Arena FragS Frag Region HeapAbortOblA)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64ConsumerA (SFactsSt2 WrAt)
open Spike.Lib.X64 (ND BlkW NodeW At okBlk)
open Spike.Lib.X64.Abort (NT)
open Spike.Lib.X64.Abort.Disp (DN HPathW)
open Spike.Lib.X64.WakeWf (DtW Wf W0 NoWrC AbortWf RunWf)
open Spike.Lib.X64.WakePh.StartWf (pfxM)
open Spike.Lib.X64.Flow (ofNat_zero')

set_option linter.unusedSimpArgs false

variable {L : RuntimeLayout} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}

/-- **A path obligation inside a weaker fragment.** -/
theorem HPathW.map {W₁ W₂ : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    (h : HPathW W₁ K exe endPc R F c0 ra) (hw : ∀ s c, W₁ s c → W₂ s c) : HPathW W₂ K exe endPc R F c0 ra := by
  have hb : ∀ {n : ND} {blk : List (Directive × Nat)}, BlkW W₁ K exe endPc R F n blk →
      BlkW W₂ K exe endPc R F n blk :=
    fun h s σ c he hn hd hp hA hF hJ k hk m hA' hD =>
      ⟨hw _ c (h s σ c he hn hd hp hA hF hJ k hk m hA' hD).1, (h s σ c he hn hd hp hA hF hJ k hk m hA' hD).2⟩
  have hn : ∀ {n : ND}, NodeW W₁ K exe endPc R F n → NodeW W₂ K exe endPc R F n :=
    fun h s c hA => ⟨hw s c (h s c hA).1, (h s c hA).2⟩
  exact ⟨hb h.de, hb h.dt1, hb h.dj1, hb h.dt2, hb h.dg2, hb h.se, hn h.sn1, hb h.sn2, hn h.ssys, hb h.sn5,
    hn h.sex⟩

/-- **The source's control is the caller's** at every node of the path. -/
theorem hpathW_hC {exe : _root_.Executable} {endPc : Int64} :
    HPathW (fun _ c => c = c0) (fun _ _ => False) exe endPc R F c0 ra := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | exact Spike.Lib.X64.WakeWf.blkW_ofJ fun _ _ h => h.1
    | exact Spike.Lib.X64.WakeWf.nodeW_ofJ fun _ _ h => h.1
    | exact Spike.Lib.X64.WakeWf.nodeW_ofJ fun _ _ h => h.1.1

section Inst

variable (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
include hp hlo hsite hlab

/-- **No write to the arena or the counter** at every node of the path: its
blocks are silent (`AllocG.blkW_noWr`), its other nodes a `leaq` and two
`syscall`s. -/
theorem hpathW_hN {ar : Arena} {p : Prog} {L0 : Lbl} {ls0 : Lsize} {Ctx : FragS isa}
    {fs : List TermRun.Frame} (a : BitVec 64) (hR : R.OK) (hlo' : R.lo ≤ -24) (hhi : 16 ≤ R.hi) :
    HPathW (NoWrC ar p L0 ls0 Ctx fs) (fun _ _ => False) L.exe L.endPc R F c0 ra := by
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hsd := SccCode.wake_abort
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

omit hsite in
/-- **The exit call is the heap abort's site** with exit status `101`
(`%rax = 231`, `%rdi = 101`), the caller's heap abort obligation (`hobl`) at
the source's unmoved control. -/
theorem nodeW_exAbWf {ar : Arena} {Ab Ac : State → Prop} {fs : List TermRun.Frame}
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
  have e : ∀ k, (Spike.Lib.X64.PhRec.μ L).abortAt k = codeLabel lo wakeCells (Scc.Cert.Link.abortName k) :=
    fun k => by show codeLabel L.Λ.code.lo L.prog (L.Λ.abortLbl k) = _; rw [hp, hlo, hΛ]
  obtain ⟨-, h2⟩ := abH_labs hlab
  have hc' : c = c0 := hc
  refine ⟨fun k x hx hpcs => ⟨?_, fun v hv => ?_⟩, fun _ h => h⟩
  · have hpx : x = 4202761 := by
      rw [← hpcs]; unfold pcOf; rw [hpc]; simp only [NT, Abort.N, Abort.heap, h2]; decide
    subst hpx
    rw [e, ← codeT_eq] at hx
    cases k <;> first
      | exact absurd hx (by decide +kernel)
      | exact .inr (.inr (.inl ⟨rfl, by rw [hc']; exact hobl⟩))
  · rw [hd] at hv; cases hv; rw [hrdi]; rfl

omit hsite hlab in
/-- **A node at a pc off the sites** has `AbortWf` at every frame list. -/
theorem nodeW_abortWf_ok {ar : Arena} {Ab Ac : State → Prop} {fs : List TermRun.Frame} (a : BitVec 64)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) {n : ND} {q : Int64}
    (hq : n.pc = q) (hok : okPcOf lo wakeCells L.Λ q.toBitVec.toNat = true) :
    NodeW (fun s c => AbortWf ar (Spike.Lib.X64.PhRec.μ L) Ab Ac s c fs) (fun _ _ => False) L.exe L.endPc R F n := by
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  rintro s c ⟨-, -, -, hpc, -⟩
  have hP := (hI.off s (by unfold pcOf; rw [hpc, hq]; exact hok)).1
  exact ⟨Spike.Lib.X64.WakeWf.abortWf_of_off hP.noAbort, fun _ h => h⟩

/-- **The abort sites at every node of the path**: off them but at the exit
call (`nodeW_exAbWf`), by the path's phase checks (`abortPhHW`). -/
theorem hpathW_hAb {ar : Arena} {Ab Ac : State → Prop} {fs : List TermRun.Frame} (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hobl : HeapAbortOblA ar.cells ar.ctr c0) :
    HPathW (fun s c => AbortWf ar (Spike.Lib.X64.PhRec.μ L) Ab Ac s c fs) (fun _ _ => False) L.exe L.endPc R F
      c0 ra := by
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hphs := abortPhHW (Λ := L.Λ) (lab := L.lab) hΛ hlab
  simp only [Spike.Lib.X64.StubW.abortPhHeapOk, Spike.Lib.X64.StubW.phOne, Bool.and_eq_true, beq_iff_eq,
    and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pg2, px0, o1, -, px1, o34, -, px2, -⟩ := hphs
  have hb : ∀ {n : ND} {blk : List (Directive × Nat)} {lo' hi' : Int} {l : Label} {k : Nat},
      L.lab l + Int64.ofNat k = n.pc → okBlk lo' hi' n.o blk = true →
      Spike.Lib.X64Consumer.blkPh (okPcOf lo wakeCells L.Λ) phW (fun _ => false) L.lab
        (L.lab l + Int64.ofNat k) 0 blk = true →
      Spike.Lib.X64Consumer.noRetBlk blk = true →
      BlkW (fun s c => AbortWf ar (Spike.Lib.X64.PhRec.μ L) Ab Ac s c fs) (fun _ _ => False) L.exe L.endPc R F
        n blk := fun he hok hph hnr =>
    Spike.Lib.X64.WakeWf.blkW_abortWf (Spike.Lib.X64.WakeWf.hpcOf hI hok (he ▸ hph) hnr)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hb (ofNat_zero' _) Abort.Disp.d0_ok pd0 (by decide)
  · exact hb (ofNat_zero' _) Abort.Disp.t1_ok pt1 (by decide)
  · exact hb rfl Abort.Disp.j1_ok pj1 (by decide)
  · exact hb (ofNat_zero' _) Abort.Disp.t2_ok pt2 (by decide)
  · exact hb (ofNat_zero' _) Abort.Disp.g2_ok pg2 (by decide)
  · exact hb (ofNat_zero' _) Abort.x0_ok px0 (by decide)
  · exact nodeW_abortWf_ok hp hlo a hsite (ofNat_zero' _).symm o1
  · exact hb rfl Abort.x1Heap_ok px1 (by decide)
  · exact nodeW_abortWf_ok hp hlo a hsite rfl o34
  · exact hb rfl Abort.x2_ok px2 (by decide)
  · exact nodeW_exAbWf hp hlo hlab hΛ hobl

/-- **`AbP` at every node of the path** in wake's layout (`abPH` with the
take site resolved and the code of the dispatcher and the heap stub). -/
theorem abPH_wake {μ' : Marks} (hsite' : μ'.site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hR : R.OK) (hlo' : R.lo ≤ -24) (hhi : 16 ≤ R.hi) : AbPH L μ' L.endPc R F c0 ra := by
  have hsd := SccCode.wake_abort
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  obtain ⟨e1, e2, -⟩ := ab_labs hlab
  exact abPH hlab hR hlo' hhi
    (fun a' ha => by
      have e : L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200277 :=
        hlab _ _ (by rw [← codeT_eq]; decide +kernel)
      rw [hsite'] at ha; cases ha
      rw [e, e1, e2]; decide)
    (Scc.Cert.Rt.X64.Abort.code_disp L.lays rfl (by rw [hp]; exact hsd.2))
    (Scc.Cert.Rt.X64.Abort.code_stub L.lays rfl (by rw [hp]; exact hsd.1.1.1.1.2))

/-- **The path's states are in `scc_rt_abort`'s code** (`abPH`'s `AbP`). -/
theorem hpathW_hX (hR : R.OK) (hlo' : R.lo ≤ -24) (hhi : 16 ≤ R.hi) :
    HPathW (fun s _ => inPc L "scc_rt_abort" "scc_rt_thr_worker" s) (fun _ _ => False) L.exe L.endPc R F
      c0 ra := by
  have hP := abPH_wake hp hlo hsite hlab (μ' := Spike.Lib.X64.PhRec.μ L) (F := F) (c0 := c0) (ra := ra) hsite
    hR hlo' hhi
  exact HPathW.map (W₁ := AbW L R ra (Spike.Lib.X64.PhRec.μ L))
    ⟨hP.de, hP.dt1, hP.dj1, hP.dt2, hP.dg2, hP.se, hP.sn1, hP.sn2, hP.ssvc, hP.sn5, hP.sex⟩
    fun _ _ h => h.1.1

/-- **The heap path inside `W0`** at `ownG`, the write tail `DtW`, the
frames `fs` (`[]` or `[frM]`, `hfs`), from a caller with the return address
past `scc_rt_alloc`'s full branch (`hra`): the components of `Wf` at every
node, the control's facts, its frames' placement and the heap abort's
obligation at the caller's control `c0` (`hc0`, `hpl`, `hobl`), the clone
path's global clause (`hcl`), the per-state facts `X0` in `scc_rt_abort`'s
code (`hX0`). -/
theorem hpathW_hab0 {ar : Arena} {p : Prog} {Cl : State → Prop} {Ctx : FragS isa} {L0 : Lbl} {ls0 : Lsize}
    {frM : TermRun.Frame} {X0 : State → Prop} {fs : List TermRun.Frame} (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hR : R.OK) (hlo' : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hra : ra = Spike.Lib.X64.Flow.WakeWc.raAb L.lab) (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hc0 : (fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) (hpl : ∀ s, PlacedSE L.Λ L0 s c0 fs)
    (hobl : HeapAbortOblA ar.cells ar.ctr c0) (hX0 : ∀ s, inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    HPathW (fun s c => W0 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) ar p DtW
      (Spike.Lib.X64.WriteAb.Ab L.lab) Cl (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx L0 ls0 frM X0 s c fs)
      (fun _ _ => False) L.exe L.endPc R F c0 ra := by
  have ef : L.lab ".Lscc_rt_alloc.full" = Int64.ofNat 4198751 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have e5 : L.lab ".Lscc_rt_alloc_tcb.x0" = Int64.ofNat 4199245 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have e23 : L.lab ".Lwc_main.x5" = Int64.ofNat 4203522 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have es : L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200277 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  obtain ⟨-, h2⟩ := abH_labs hlab
  have hG := hpathW_habG hp hlo hsite (Λ := L.Λ) (F := F) (c0 := c0) (ra := ra) a hΛ hlab hR hlo' hhi
    (fun h => absurd (hra.symm.trans h) (by rw [Spike.Lib.X64.Flow.WakeWc.raAb, ef, e5]; decide))
    (by rw [hra, Spike.Lib.X64.Flow.WakeWc.raAb, ef, e23]; decide)
  have hPh := Spike.Lib.X64.WakeWf.hpathW_ph (Cl := Cl) (F := F) (c0 := c0) (ra := ra)
    (instOkW hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)) (by rw [hp]; exact SccCode.wake_abort)
    (abortPhHW (Λ := L.Λ) (lab := L.lab) hΛ hlab) hlab hR hlo' hhi
    (fun a' ha => by rw [hsite] at ha; cases ha; simp only [Abort.heap, h2, es]; decide)
    (by rw [hra]; exact Spike.Lib.X64.WakeWf.hra_alloc hlab)
  have hN := hpathW_hN (ar := ar) (p := p) (L0 := L0) (ls0 := ls0) (Ctx := Ctx) (fs := fs) (F := F) (c0 := c0)
    (ra := ra) hp hlo hsite hlab a hR hlo' hhi
  have hAb := hpathW_hAb (ar := ar) (Ab := Spike.Lib.X64.WriteAb.Ab L.lab)
    (Ac := Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) (fs := fs) (R := R) (F := F) (ra := ra) hp hlo hsite hlab a hΛ
    hobl
  have hX := hpathW_hX (F := F) (c0 := c0) (ra := ra) hp hlo hsite hlab hR hlo' hhi
  have h1 := Abort.Disp.HPathW.and hG hPh fun s c h₁ h₂ => And.intro h₁ h₂
  have h2' := Abort.Disp.HPathW.and h1 hpathW_hC fun s c h₁ h₂ => And.intro h₁ h₂
  have h3 := Abort.Disp.HPathW.and h2' hN fun s c h₁ h₂ => And.intro h₁ h₂
  have h4 := Abort.Disp.HPathW.and h3 hAb fun s c h₁ h₂ => And.intro h₁ h₂
  refine Abort.Disp.HPathW.and h4 hX fun s c h hx => ?_
  obtain ⟨⟨⟨⟨hst, hab, hac⟩, hc⟩, hw⟩, habt⟩ := h
  subst hc
  exact ⟨hfs, hX0 s hx, Spike.Lib.X64.WakeWf.Wf.intro hst hab hac hcl hc0.1 (hpl s) hw.1 hw.2 hc0.2 habt⟩

end Inst

open Spike.Lib.X64.Flow.WakeWc (WcHAbStub wX) in
/-- **`WcHAbStub` at wake's level before the allocation** (`W0` at `ownG`,
no outside moves): `stubHRW_of_code` in the region `[-24, 16)` below
`-240` at each caller's state of `wX .abort`, whose control has the
control's facts, its frames placed and the heap abort's obligation
(`hctl`); the exit call at an abort site of the memory side (`hab`). -/
theorem wc_heapAbStub {ar : Arena} {p : Prog} {Cl : State → Prop} {Ctx : FragS isa} {L0 : Lbl}
    {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop} {fs : List TermRun.Frame}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
    {J0 : Spike.Lib.X64.AS → Ctl → Prop}
    (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hF : Spike.Lib.X64.FStable R F) (hR : R.OK) (hlo' : R.lo ≤ -272) (hhi : -232 ≤ R.hi)
    (hK : (ms fs).K = some abi) (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hctl : ∀ σC c0, (wX (ms fs) L.lab R J0 .abort).J σC c0 →
      ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧ (∀ s, PlacedSE L.Λ L0 s c0 fs) ∧
        HeapAbortOblA ar.cells ar.ctr c0)
    (hab : ∀ s : State, s.st.2 = L.lab "scc_rt_abort_heap_exit" → (ms fs).abortAt s)
    (hX0 : ∀ s, inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    WcHAbStub (W0 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) ar p DtW (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx L0 ls0 frM X0) (fun _ _ => False) p lbl ms L.exe L.endPc R F
      fs J0 := by
  intro m0 σC c0 hJ
  obtain ⟨hc0, hpl, hobl⟩ := hctl σC c0 hJ
  have hR' : (R.callee (-240 - 8) (-24) 16).OK :=
    Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)
  exact Spike.Lib.X64.StubW.stubHRW_of_code L.lays rfl (by rw [hp]; exact SccCode.wake_abort) hK
    (Spike.Lib.X64.fstable_enter hR hF (by omega) (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide))
    (hpathW_hab0 hp hlo (siteW hp hlo hlab) hlab a hΛ hR'
      (by simp [Region.callee]) (by simp [Region.callee]) rfl hfs hcl hc0 hpl hobl hX0)
    fun s _ ⟨_, _, _, hpc, _⟩ => hab s hpc

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.hpathW_hab0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.hpathW_hab0

/-- info: 'Spike.Lib.X64.WakePh.wc_heapAbStub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.wc_heapAbStub
