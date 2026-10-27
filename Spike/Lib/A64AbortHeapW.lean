/-
**The heap abort path on AArch64 inside `W`**: `scc_rt_abort(2)` (the
allocator's jump when the arena is full) through the dispatcher to
`scc_rt_abort_heap`, which does not return (`Spike/Lib/A64AbortW.lean` for
the overflow code).

- `seg_heapW`: `scc_rt_abort_heap` (`seg_stubW`);
- `Disp.DN.nd2`, `Disp.seg_disp2W`: the dispatcher at the heap code `2`
  (the first test not taken, the second taken, every other node dead), to
  the heap stub's entry;
- `Disp.StubHW`: the path's obligations for one source control;
  `Disp.seg_abort2W`: the dispatcher then the stub;
- `Disp.seg_jabort2W`: from a node at `scc_rt_abort` with `x0 = 2` at any
  `sp` offset of a region, the dispatcher in the region below it
  (`at_enter`).
-/
import Spike.Lib.A64AbortW
import Spike.Lib.SegCommon

namespace Spike.Lib.A64.Abort

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

set_option linter.unusedSimpArgs false

section Stubs

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {Q : Frag isaLSE2}

/-- **`scc_rt_abort_heap` inside `W` does not return.** -/
theorem seg_heapW {W : Frag isaLSE2} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code heap c0 b1Heap exe endPc) (hK : ms.K = some Scc.Sem.A64.abi)
    (hWe : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .e) b0)
    (hWn1 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .n1))
    (hWn1b : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .n1b))
    (hWn2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .n2) b1Heap)
    (hWn5 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .n5) b2)
    (hWex : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .ex))
    (hsvc : SegW W K p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .svc))
      (At exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .n5)))
    (hab : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .ex) s c →
      ms.abortAt s) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .e)) Q :=
  seg_stubW heap (by simp [b1Heap]) b1Heap_ok (by arg_hit b1Heap_run)
    hF hR hal hlo hhi hcode hK hWe hWn1 hWn1b hWn2 hWn5 hWex hsvc hab

end Stubs

namespace Disp

section Spec

variable (lab : Label → Int64) (c0 : Ctl)

/-- **The nodes at the heap code**: the entry with `x0 = 2`, the first test
(not taken) and its jump to the second, the second test with `2` stored,
its taken jump; every other node dead. -/
def DN.nd2 : DN → ND
  | .e => ⟨lab "scc_rt_abort", oE, fun σ c => c = c0 ∧ σ.regs.X0.toBitVec.toNat = 2⟩
  | .t1 => ⟨lab ".L12_scc_rt_abort.0_entry", oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 2⟩
  | .j1 => ⟨lab ".L12_scc_rt_abort.0_entry" + 4 + 4 + 4 + 4, oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 2⟩
  | .t2 => ⟨lab ".L12_scc_rt_abort.2_next1", oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 2⟩
  | .g2 => ⟨lab ".L12_scc_rt_abort.3_is2", oD, fun _ c => c = c0⟩
  | i => ⟨(DN.nd lab c0 i).pc, oD, fun _ _ => False⟩

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}

/-- **`scc_rt_abort(2)` inside `W` is one segment** from its entry to the
heap stub's entry. -/
theorem seg_disp2W {W : Frag isaLSE2} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code c0 exe endPc)
    (hWe : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .e) d0)
    (hWt1 : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .t1) t1)
    (hWj1 : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .j1) j1)
    (hWt2 : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .t2) t2)
    (hWg2 : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .g2) g2) :
    SegW W K p lbl ms (At exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .e))
      (At exe endPc R F (DX.nd (_root_.Executable.labels exe).label c0 .heap)) := by
  refine (fn_segW (N := DN.nd2 (_root_.Executable.labels exe).label c0)
    (E := fun (_ : Unit) => DX.nd (_root_.Executable.labels exe).label c0 .heap) (fun i => ?_) DN.e).mono_post
    fun _ _ ⟨_, h⟩ => h
  · have hentry := hcode.hentry
    cases i
    case e =>
      refine seg_ndW (by simp [d0]) d0_ok hF hR hal (by omega) hhi
        (fun s he hn => hcode.e s he hn) hWe fun σ c hJ => ⟨c, .refl c, ?_⟩
      rw [DN.nd2, d0_run]
      refine .inl ⟨DN.t1, ?_, rfl, ?_⟩ <;> simp_all [DN.nd2, upd_apply]
    case t1 =>
      refine seg_ndW (by simp [t1]) t1_ok hF hR hal (by omega) hhi
        (fun s he hn => hcode.t1 s he hn) hWt1 fun σ c hJ => ⟨c, .refl c, ?_⟩
      rw [DN.nd2, t1_run]
      split
      · next h =>
        exfalso
        obtain ⟨-, h2⟩ := hJ
        have e : σ.slot (-32) = 2#64 := BitVec.eq_of_toNat_eq (by simpa using h2)
        rw [e] at h
        revert h; decide
      · refine .inl ⟨DN.j1, ?_, rfl, ?_⟩ <;> simp_all [DN.nd2]
    case j1 =>
      refine seg_ndW (by simp [j1]) j1_ok hF hR hal (by omega) hhi
        (fun s he hn => hcode.j1 s he hn) hWj1 fun σ c hJ => ⟨c, .refl c, ?_⟩
      rw [DN.nd2, j1_run]
      refine .inl ⟨DN.t2, ?_, rfl, ?_⟩ <;> simp_all [DN.nd2, DN.nd]
    case t2 =>
      refine seg_ndW (by simp [t2]) t2_ok hF hR hal (by omega) hhi
        (fun s he hn => hcode.t2 s he hn) hWt2 fun σ c hJ => ⟨c, .refl c, ?_⟩
      rw [DN.nd2, t2_run]
      split
      · refine .inl ⟨DN.g2, ?_, rfl, ?_⟩ <;> simp_all [DN.nd2]
      · next h =>
        exfalso
        obtain ⟨-, h2⟩ := hJ
        have e : σ.slot (-32) = 2#64 := BitVec.eq_of_toNat_eq (by simpa using h2)
        rw [e] at h
        revert h; decide
    case g2 =>
      refine seg_ndW (by simp [g2]) g2_ok hF hR hal (by omega) hhi
        (fun s he hn => hcode.g2 s he hn) hWg2 fun σ c hJ => ⟨c, .refl c, ?_⟩
      rw [DN.nd2, g2_run]
      refine .inr ⟨(), ?_, rfl, ?_⟩ <;>
        simp_all [DN.nd2, DX.nd, DX.stub, Abort.N, Abort.heap]
    all_goals exact dead_ndW fun _ _ h => h

/-- **The heap abort path's obligations for one source control `c0`** in
the dispatcher's region `R` and frame condition `F`: the dispatcher's and
the heap stub's code, their nodes' states inside `W` (moved by no `K`), the
stub's `write` call a segment inside `W`, and its exit call at an abort
site. -/
structure StubHW (W : Frag isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (c0 : Ctl) : Prop where
  dcode : Code c0 exe endPc
  de : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .e) d0
  dt1 : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .t1) t1
  dj1 : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .j1) j1
  dt2 : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .t2) t2
  dg2 : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .g2) g2
  scode : Abort.Code heap c0 b1Heap exe endPc
  se : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label heap c0 .e) b0
  sn1 : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label heap c0 .n1)
  sn1b : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label heap c0 .n1b)
  sn2 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label heap c0 .n2) b1Heap
  sn5 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label heap c0 .n5) b2
  sex : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label heap c0 .ex)
  svc : SegW W K p lbl ms (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label heap c0 .svc))
    (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label heap c0 .n5))
  ab : ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label heap c0 .ex) s c → ms.abortAt s

/-- **`scc_rt_abort(2)` inside `W` does not return**: the dispatcher at the
heap code (`seg_disp2W`) then `scc_rt_abort_heap` (`seg_heapW`). -/
theorem seg_abort2W {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi) (hs : StubHW W K p lbl ms exe endPc R F c0) :
    SegW W K p lbl ms (At exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .e)) Q :=
  (seg_disp2W hF hR hal hlo hhi hs.dcode hs.de hs.dt1 hs.dj1 hs.dt2 hs.dg2).seq
    (seg_heapW hF hR hal hlo hhi hs.scode hK hs.se hs.sn1 hs.sn1b hs.sn2 hs.sn5 hs.sex hs.svc hs.ab)

/-- **A jump to `scc_rt_abort` with `x0 = 2` inside `W` does not return**:
from a node `nC` at `scc_rt_abort` (`sp` at `nC.o.sp` in `R`, `x0 = 2` in
every state of its invariant) a segment to any fragment, the dispatcher
running in the region below `nC.o.sp` (`at_enter`), given the heap abort
path's obligations there for each caller's state `m0`, `σC` and source
control of `nC` (`hstub`). -/
theorem seg_jabort2W {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hX0 : ∀ σ c, nC.J σ c → σ.regs.X0.toBitVec.toNat = 2)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ nC.o.sp - 48)
    (hkc : nC.o.sp < R.hi) (h16 : nC.o.sp % 16 = 0) (hK : ms.K = some Scc.Sem.A64.abi)
    (hstub : ∀ m0 σC c0, nC.J σC c0 → StubHW W K p lbl ms exe endPc (R.callee nC.o.sp (-48) 0)
      (fun m => F m ∧ CKept R nC.o.sp (-48) 0 m0 m ∧ Abs R nC.o m0 σC) c0) :
    SegW W K p lbl ms (At exe endPc R F nC) Q := by
  have hP : ∀ s c, At exe endPc R F nC s c → ∃ g : MachineData × AS × Ctl,
      (fun s c => At exe endPc (R.callee nC.o.sp (-48) 0)
        (fun m => F m ∧ CKept R nC.o.sp (-48) 0 g.1 m ∧ Abs R nC.o g.1 g.2.1)
        (DN.nd2 (_root_.Executable.labels exe).label g.2.2 .e) s c ∧ nC.J g.2.1 g.2.2) s c := by
    intro s c h
    obtain ⟨m0, σC, he, hn, hdc, hpc', σ, hA, hD, -, rfl, hJ⟩ :=
      at_enter (lo' := -48) (hi' := 0) (by omega) hkc (by decide) (by omega) h
    exact ⟨(m0, σC, c), ⟨he, hn, hdc, hpc'.trans hpc, enter nC.o.sp σC, hA, hD, rfl, hX0 σC c hJ⟩, hJ⟩
  refine (SegW.exists_pre fun g => SegW.of_imp fun hJ => ?_).mono_pre hP
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ nC.o.sp + -48 by omega) (by decide) hkc
  have hal' : (R.callee nC.o.sp (-48) 0).base.toNat % 16 = 0 := by
    have : (((R.callee nC.o.sp (-48) 0).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
    omega
  exact seg_abort2W (fstable_enter hR hF (by omega) (by decide) hkc (by decide) (by omega) (by decide) (by decide))
    (Region.callee_ok hR (by omega) (by decide) hkc (by omega)) hal' (by simp [Region.callee])
    (by simp [Region.callee]) hK (hstub g.1 g.2.1 g.2.2 hJ)

end Proof

end Disp

end Spike.Lib.A64.Abort
