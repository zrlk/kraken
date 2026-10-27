/-
**The write abort path on AArch64 inside `W`**: `scc_rt_abort(4)` (`print`'s
jump when the `write` system call fails) through the dispatcher to
`scc_rt_abort_write`, which does not return (`Spike/Lib/A64AbortHeapW.lean`
for the heap code).

- `seg_writeW`: `scc_rt_abort_write` (`seg_stubW`);
- `Disp.DN.nd4`, `Disp.seg_disp4W`: the dispatcher at the write code `4`
  (the first three tests not taken, the fourth taken, every other node
  dead), to the write stub's entry;
- `Disp.StubWW`: the path's obligations for one source control;
  `Disp.seg_abort4W`: the dispatcher then the stub;
- `Disp.seg_jabort4W`: from a node at `scc_rt_abort` with `x0 = 4` at any
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

/-- **`scc_rt_abort_write` inside `W` does not return.** -/
theorem seg_writeW {W : Frag isaLSE2} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code write c0 b1Write exe endPc) (hK : ms.K = some Scc.Sem.A64.abi)
    (hWe : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label write c0 .e) b0)
    (hWn1 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label write c0 .n1))
    (hWn1b : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label write c0 .n1b))
    (hWn2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label write c0 .n2) b1Write)
    (hWn5 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label write c0 .n5) b2)
    (hWex : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label write c0 .ex))
    (hsvc : SegW W K p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label write c0 .svc))
      (At exe endPc R F (N (_root_.Executable.labels exe).label write c0 .n5)))
    (hab : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label write c0 .ex) s c →
      ms.abortAt s) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label write c0 .e)) Q :=
  seg_stubW write (by simp [b1Write]) b1Write_ok (by arg_hit b1Write_run)
    hF hR hal hlo hhi hcode hK hWe hWn1 hWn1b hWn2 hWn5 hWex hsvc hab

end Stubs

namespace Disp

section Spec

variable (lab : Label → Int64) (c0 : Ctl)

/-- **The nodes at the write code**: the entry with `x0 = 4`, the first
three tests (not taken) with `4` stored and their jumps to the next, the
fourth test, its taken jump; every other node dead. -/
def DN.nd4 : DN → ND
  | .e => ⟨lab "scc_rt_abort", oE, fun σ c => c = c0 ∧ σ.regs.X0.toBitVec.toNat = 4⟩
  | .t1 => ⟨lab ".L12_scc_rt_abort.0_entry", oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 4⟩
  | .j1 => ⟨lab ".L12_scc_rt_abort.0_entry" + 4 + 4 + 4 + 4, oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 4⟩
  | .t2 => ⟨lab ".L12_scc_rt_abort.2_next1", oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 4⟩
  | .j2 => ⟨lab ".L12_scc_rt_abort.2_next1" + 4 + 4 + 4 + 4, oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 4⟩
  | .t3 => ⟨lab ".L12_scc_rt_abort.4_next3", oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 4⟩
  | .j3 => ⟨lab ".L12_scc_rt_abort.4_next3" + 4 + 4 + 4 + 4, oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 4⟩
  | .t4 => ⟨lab ".L12_scc_rt_abort.6_next5", oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 4⟩
  | .g4 => ⟨lab ".L12_scc_rt_abort.7_is6", oD, fun _ c => c = c0⟩
  | i => ⟨(DN.nd lab c0 i).pc, oD, fun _ _ => False⟩

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}

set_option hygiene false in
/-- A dispatcher node of `seg_disp4W`: the block, its `okBlk`, its code and
its `W` obligation; the edge is left. -/
macro "wnode " b:ident ok:ident f:ident hw:ident : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hal (by omega) hhi
    (fun s he hn => hcode.$f s he hn) $hw fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A test with `4` stored: the branch against it contradicts the stored code. -/
macro "wnot" : tactic =>
  `(tactic| (exfalso
             obtain ⟨-, h4⟩ := hJ
             have e : σ.slot (-32) = 4#64 := BitVec.eq_of_toNat_eq (by simpa using h4)
             rw [e] at h
             revert h; decide))

/-- **`scc_rt_abort(4)` inside `W` is one segment** from its entry to the
write stub's entry. -/
theorem seg_disp4W {W : Frag isaLSE2} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code c0 exe endPc)
    (hWe : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .e) d0)
    (hWt1 : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .t1) t1)
    (hWj1 : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .j1) j1)
    (hWt2 : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .t2) t2)
    (hWj2 : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .j2) j2)
    (hWt3 : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .t3) t3)
    (hWj3 : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .j3) j3)
    (hWt4 : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .t4) t4)
    (hWg4 : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .g4) g4) :
    SegW W K p lbl ms (At exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .e))
      (At exe endPc R F (DX.nd (_root_.Executable.labels exe).label c0 .write)) := by
  refine (fn_segW (N := DN.nd4 (_root_.Executable.labels exe).label c0)
    (E := fun (_ : Unit) => DX.nd (_root_.Executable.labels exe).label c0 .write) (fun i => ?_) DN.e).mono_post
    fun _ _ ⟨_, h⟩ => h
  · have hentry := hcode.hentry
    cases i
    case e =>
      wnode d0 d0_ok e hWe
      rw [DN.nd4, d0_run]
      refine .inl ⟨DN.t1, ?_, rfl, ?_⟩ <;> simp_all [DN.nd4, upd_apply]
    case t1 =>
      wnode t1 t1_ok t1 hWt1
      rw [DN.nd4, t1_run]
      split
      · next h => wnot
      · refine .inl ⟨DN.j1, ?_, rfl, ?_⟩ <;> simp_all [DN.nd4]
    case j1 =>
      wnode j1 j1_ok j1 hWj1
      rw [DN.nd4, j1_run]
      refine .inl ⟨DN.t2, ?_, rfl, ?_⟩ <;> simp_all [DN.nd4, DN.nd]
    case t2 =>
      wnode t2 t2_ok t2 hWt2
      rw [DN.nd4, t2_run]
      split
      · next h => wnot
      · refine .inl ⟨DN.j2, ?_, rfl, ?_⟩ <;> simp_all [DN.nd4]
    case j2 =>
      wnode j2 j2_ok j2 hWj2
      rw [DN.nd4, j2_run]
      refine .inl ⟨DN.t3, ?_, rfl, ?_⟩ <;> simp_all [DN.nd4, DN.nd]
    case t3 =>
      wnode t3 t3_ok t3 hWt3
      rw [DN.nd4, t3_run]
      split
      · next h => wnot
      · refine .inl ⟨DN.j3, ?_, rfl, ?_⟩ <;> simp_all [DN.nd4]
    case j3 =>
      wnode j3 j3_ok j3 hWj3
      rw [DN.nd4, j3_run]
      refine .inl ⟨DN.t4, ?_, rfl, ?_⟩ <;> simp_all [DN.nd4, DN.nd]
    case t4 =>
      wnode t4 t4_ok t4 hWt4
      rw [DN.nd4, t4_run]
      split
      · refine .inl ⟨DN.g4, ?_, rfl, ?_⟩ <;> simp_all [DN.nd4]
      · next h => wnot
    case g4 =>
      wnode g4 g4_ok g4 hWg4
      rw [DN.nd4, g4_run]
      refine .inr ⟨(), ?_, rfl, ?_⟩ <;>
        simp_all [DN.nd4, DX.nd, DX.stub, Abort.N, Abort.write]
    all_goals exact dead_ndW fun _ _ h => h

/-- **The write abort path's obligations for one source control `c0`** in
the dispatcher's region `R` and frame condition `F`: the dispatcher's and
the write stub's code, their nodes' states inside `W` (moved by no `K`), the
stub's `write` call a segment inside `W`, and its exit call at an abort
site. -/
structure StubWW (W : Frag isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (c0 : Ctl) : Prop where
  dcode : Code c0 exe endPc
  de : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .e) d0
  dt1 : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .t1) t1
  dj1 : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .j1) j1
  dt2 : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .t2) t2
  dj2 : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .j2) j2
  dt3 : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .t3) t3
  dj3 : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .j3) j3
  dt4 : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .t4) t4
  dg4 : BlkW W K exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .g4) g4
  scode : Abort.Code write c0 b1Write exe endPc
  se : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .e) b0
  sn1 : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .n1)
  sn1b : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .n1b)
  sn2 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .n2) b1Write
  sn5 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .n5) b2
  sex : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .ex)
  svc : SegW W K p lbl ms (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .svc))
    (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .n5))
  ab : ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .ex) s c → ms.abortAt s

/-- **`scc_rt_abort(4)` inside `W` does not return**: the dispatcher at the
write code (`seg_disp4W`) then `scc_rt_abort_write` (`seg_writeW`). -/
theorem seg_abort4W {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi) (hs : StubWW W K p lbl ms exe endPc R F c0) :
    SegW W K p lbl ms (At exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .e)) Q :=
  (seg_disp4W hF hR hal hlo hhi hs.dcode hs.de hs.dt1 hs.dj1 hs.dt2 hs.dj2 hs.dt3 hs.dj3 hs.dt4 hs.dg4).seq
    (seg_writeW hF hR hal hlo hhi hs.scode hK hs.se hs.sn1 hs.sn1b hs.sn2 hs.sn5 hs.sex hs.svc hs.ab)

/-- **A jump to `scc_rt_abort` with `x0 = 4` inside `W` does not return**:
from a node `nC` at `scc_rt_abort` (`sp` at `nC.o.sp` in `R`, `x0 = 4` in
every state of its invariant) a segment to any fragment, the dispatcher
running in the region below `nC.o.sp` (`at_enter`), given the write abort
path's obligations there for each caller's state `m0`, `σC` and source
control of `nC` (`hstub`). -/
theorem seg_jabort4W {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hX0 : ∀ σ c, nC.J σ c → σ.regs.X0.toBitVec.toNat = 4)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ nC.o.sp - 48)
    (hkc : nC.o.sp < R.hi) (h16 : nC.o.sp % 16 = 0) (hK : ms.K = some Scc.Sem.A64.abi)
    (hstub : ∀ m0 σC c0, nC.J σC c0 → StubWW W K p lbl ms exe endPc (R.callee nC.o.sp (-48) 0)
      (fun m => F m ∧ CKept R nC.o.sp (-48) 0 m0 m ∧ Abs R nC.o m0 σC) c0) :
    SegW W K p lbl ms (At exe endPc R F nC) Q := by
  have hP : ∀ s c, At exe endPc R F nC s c → ∃ g : MachineData × AS × Ctl,
      (fun s c => At exe endPc (R.callee nC.o.sp (-48) 0)
        (fun m => F m ∧ CKept R nC.o.sp (-48) 0 g.1 m ∧ Abs R nC.o g.1 g.2.1)
        (DN.nd4 (_root_.Executable.labels exe).label g.2.2 .e) s c ∧ nC.J g.2.1 g.2.2) s c := by
    intro s c h
    obtain ⟨m0, σC, he, hn, hdc, hpc', σ, hA, hD, -, rfl, hJ⟩ :=
      at_enter (lo' := -48) (hi' := 0) (by omega) hkc (by decide) (by omega) h
    exact ⟨(m0, σC, c), ⟨he, hn, hdc, hpc'.trans hpc, enter nC.o.sp σC, hA, hD, rfl, hX0 σC c hJ⟩, hJ⟩
  refine (SegW.exists_pre fun g => SegW.of_imp fun hJ => ?_).mono_pre hP
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ nC.o.sp + -48 by omega) (by decide) hkc
  have hal' : (R.callee nC.o.sp (-48) 0).base.toNat % 16 = 0 := by
    have : (((R.callee nC.o.sp (-48) 0).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
    omega
  exact seg_abort4W (fstable_enter hR hF (by omega) (by decide) hkc (by decide) (by omega) (by decide) (by decide))
    (Region.callee_ok hR (by omega) (by decide) hkc (by omega)) hal' (by simp [Region.callee])
    (by simp [Region.callee]) hK (hstub g.1 g.2.1 g.2.2 hJ)

end Proof

end Disp

end Spike.Lib.A64.Abort
