/-
**The heap abort path on AArch64 inside `W` with the return address**:
`Spike/Lib/A64AbortHeapW.lean`'s path with `x30 = ra` carried through, as
`Spike/Lib/A64AbortThreadsW.lean` does for the threads code (a caller's
instance chosen by its return address, e.g. wake.w's `ownG`, reads it at
every node).

- `seg_heapRW`: `scc_rt_abort_heap` over `NT ra` (`seg_stubRW`);
- `Disp.DN.nd2R`, `Disp.seg_disp2RW`: the dispatcher at the heap code `2`
  with `x30 = ra` throughout, saved at `slot (-8)` after the prologue;
- `Disp.StubHRW`: the path's obligations for one source control;
  `Disp.seg_abort2RW`: the dispatcher then the stub;
- `Disp.seg_jabort2RW`: from a node at `scc_rt_abort` with `x0 = 2` and
  `x30 = ra`, the dispatcher in the region below it (`at_enter`).

Concrete k=2 copy of the k=5 machinery; to be generalised over k with it.
-/
import Spike.Lib.A64AbortHeapW
import Spike.Lib.A64AbortThreadsW

namespace Spike.Lib.A64.Abort

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

set_option linter.unusedSimpArgs false

section Stubs

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {Q : Frag isaLSE2}
  {ra : BitVec 64}

/-- **`scc_rt_abort_heap` inside `W` does not return**, with the return
address `ra` in `x30` throughout. -/
theorem seg_heapRW {W : Frag isaLSE2} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code heap c0 b1Heap exe endPc) (hK : ms.K = some Scc.Sem.A64.abi)
    (hWe : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .e) b0)
    (hWn1 : NodeW W K exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .n1))
    (hWn1b : NodeW W K exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .n1b))
    (hWn2 : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .n2) b1Heap)
    (hWn5 : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .n5) b2)
    (hWex : NodeW W K exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .ex))
    (hsvc : SegW W K p lbl ms
      (At exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .svc))
      (At exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .n5)))
    (hab : ∀ s c, At exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .ex) s c →
      ms.abortAt s) :
    SegW W K p lbl ms (At exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .e)) Q :=
  seg_stubRW heap (by simp [b1Heap]) b1Heap_ok
    (by intro σ c hJ; rw [NT, b1Heap_run]; refine ⟨?_, rfl, ?_⟩ <;> simp_all [NT, JR, JI, upd_apply])
    hF hR hal hlo hhi hcode hK hWe hWn1 hWn1b hWn2 hWn5 hWex hsvc hab

end Stubs

namespace Disp

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (ra : BitVec 64)

/-- **The nodes at the heap code with the return address**: `DN.nd2`'s,
`x30 = ra` throughout and saved at `slot (-8)` after the prologue. -/
def DN.nd2R : DN → ND
  | .e => ⟨lab "scc_rt_abort", oE, fun σ c => c = c0 ∧ σ.regs.X0.toBitVec.toNat = 2 ∧ σ.regs.X30.toBitVec = ra⟩
  | .t1 => ⟨lab ".L12_scc_rt_abort.0_entry", oD, fun σ c =>
      c = c0 ∧ (σ.slot (-32)).toNat = 2 ∧ σ.slot (-8) = ra ∧ σ.regs.X30.toBitVec = ra⟩
  | .j1 => ⟨lab ".L12_scc_rt_abort.0_entry" + 4 + 4 + 4 + 4, oD, fun σ c =>
      c = c0 ∧ (σ.slot (-32)).toNat = 2 ∧ σ.slot (-8) = ra ∧ σ.regs.X30.toBitVec = ra⟩
  | .t2 => ⟨lab ".L12_scc_rt_abort.2_next1", oD, fun σ c =>
      c = c0 ∧ (σ.slot (-32)).toNat = 2 ∧ σ.slot (-8) = ra ∧ σ.regs.X30.toBitVec = ra⟩
  | .g2 => ⟨lab ".L12_scc_rt_abort.3_is2", oD, fun σ c => c = c0 ∧ σ.slot (-8) = ra ∧ σ.regs.X30.toBitVec = ra⟩
  | i => ⟨(DN.nd lab c0 i).pc, oD, fun _ _ => False⟩

/-- **The dispatcher's exit to the heap stub** with the return address. -/
abbrev DX.nhr : ND := Abort.NT lab Abort.heap c0 ra .e

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {ra : BitVec 64}

set_option hygiene false in
/-- A test with `2` stored: the branch against it contradicts the stored code. -/
local macro "tnot2" : tactic =>
  `(tactic| (exfalso
             obtain ⟨-, h4, -⟩ := hJ
             have e : σ.slot (-32) = 2#64 := BitVec.eq_of_toNat_eq (by simpa using h4)
             rw [e] at h
             revert h; decide))

/-- **`scc_rt_abort(2)` inside `W` with the return address is one segment**
from its entry to the heap stub's entry. -/
theorem seg_disp2RW {W : Frag isaLSE2} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code c0 exe endPc)
    (hWe : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .e) d0)
    (hWt1 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .t1) t1)
    (hWj1 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .j1) j1)
    (hWt2 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .t2) t2)
    (hWg2 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .g2) g2) :
    SegW W K p lbl ms (At exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .e))
      (At exe endPc R F (DX.nhr (_root_.Executable.labels exe).label c0 ra)) := by
  refine (fn_segW (N := DN.nd2R (_root_.Executable.labels exe).label c0 ra)
    (E := fun (_ : Unit) => DX.nhr (_root_.Executable.labels exe).label c0 ra) (fun i => ?_) DN.e).mono_post
    fun _ _ ⟨_, h⟩ => h
  · have hentry := hcode.hentry
    cases i
    case e =>
      tnode d0 d0_ok e hWe
      rw [DN.nd2R, d0_run]
      refine .inl ⟨DN.t1, ?_, rfl, ?_⟩ <;> simp_all [DN.nd2R, upd_apply]
    case t1 =>
      tnode t1 t1_ok t1 hWt1
      rw [DN.nd2R, t1_run]
      split
      · next h => tnot2
      · refine .inl ⟨DN.j1, ?_, rfl, ?_⟩ <;> simp_all [DN.nd2R]
    case j1 =>
      tnode j1 j1_ok j1 hWj1
      rw [DN.nd2R, j1_run]
      refine .inl ⟨DN.t2, ?_, rfl, ?_⟩ <;> simp_all [DN.nd2R, DN.nd]
    case t2 =>
      tnode t2 t2_ok t2 hWt2
      rw [DN.nd2R, t2_run]
      split
      · refine .inl ⟨DN.g2, ?_, rfl, ?_⟩ <;> simp_all [DN.nd2R]
      · next h => tnot2
    case g2 =>
      tnode g2 g2_ok g2 hWg2
      rw [DN.nd2R, g2_run]
      refine .inr ⟨(), ?_, rfl, ?_⟩ <;>
        simp_all [DN.nd2R, DX.nhr, Abort.NT, Abort.heap]
    all_goals exact dead_ndW fun _ _ h => h

/-- **The heap abort path's obligations with the return address** for one
source control `c0` in the dispatcher's region `R` and frame condition `F`
(`StubHW` over `DN.nd2R` and `NT ra`). -/
structure StubHRW (W : Frag isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (c0 : Ctl) (ra : BitVec 64) : Prop where
  dcode : Code c0 exe endPc
  de : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .e) d0
  dt1 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .t1) t1
  dj1 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .j1) j1
  dt2 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .t2) t2
  dg2 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .g2) g2
  scode : Abort.Code heap c0 b1Heap exe endPc
  se : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .e) b0
  sn1 : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .n1)
  sn1b : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .n1b)
  sn2 : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .n2) b1Heap
  sn5 : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .n5) b2
  sex : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .ex)
  svc : SegW W K p lbl ms (At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .svc))
    (At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .n5))
  ab : ∀ s c, At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .ex) s c → ms.abortAt s

/-- **`scc_rt_abort(2)` with the return address inside `W` does not
return**: `seg_disp2RW` then `seg_heapRW`. -/
theorem seg_abort2RW {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi) (hs : StubHRW W K p lbl ms exe endPc R F c0 ra) :
    SegW W K p lbl ms (At exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .e)) Q :=
  (seg_disp2RW hF hR hal hlo hhi hs.dcode hs.de hs.dt1 hs.dj1 hs.dt2 hs.dg2).seq
    (seg_heapRW hF hR hal hlo hhi hs.scode hK hs.se hs.sn1 hs.sn1b hs.sn2 hs.sn5 hs.sex hs.svc hs.ab)

/-- **A jump to `scc_rt_abort` with `x0 = 2` and `x30 = ra` inside `W` does
not return** (`seg_jabort2W` with the return address): the dispatcher in
the region below `nC.o.sp`, given the path's obligations there for each
caller's state and source control of `nC` (`hstub`). -/
theorem seg_jabort2RW {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hX0 : ∀ σ c, nC.J σ c → σ.regs.X0.toBitVec.toNat = 2)
    (hX30 : ∀ σ c, nC.J σ c → σ.regs.X30.toBitVec = ra)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ nC.o.sp - 48)
    (hkc : nC.o.sp < R.hi) (h16 : nC.o.sp % 16 = 0) (hK : ms.K = some Scc.Sem.A64.abi)
    (hstub : ∀ m0 σC c0, nC.J σC c0 → StubHRW W K p lbl ms exe endPc (R.callee nC.o.sp (-48) 0)
      (fun m => F m ∧ CKept R nC.o.sp (-48) 0 m0 m ∧ Abs R nC.o m0 σC) c0 ra) :
    SegW W K p lbl ms (At exe endPc R F nC) Q := by
  have hP : ∀ s c, At exe endPc R F nC s c → ∃ g : MachineData × AS × Ctl,
      (fun s c => At exe endPc (R.callee nC.o.sp (-48) 0)
        (fun m => F m ∧ CKept R nC.o.sp (-48) 0 g.1 m ∧ Abs R nC.o g.1 g.2.1)
        (DN.nd2R (_root_.Executable.labels exe).label g.2.2 ra .e) s c ∧ nC.J g.2.1 g.2.2) s c := by
    intro s c h
    obtain ⟨m0, σC, he, hn, hdc, hpc', σ, hA, hD, -, rfl, hJ⟩ :=
      at_enter (lo' := -48) (hi' := 0) (by omega) hkc (by decide) (by omega) h
    exact ⟨(m0, σC, c), ⟨he, hn, hdc, hpc'.trans hpc, enter nC.o.sp σC, hA, hD, rfl, hX0 σC c hJ, hX30 σC c hJ⟩,
      hJ⟩
  refine (SegW.exists_pre fun g => SegW.of_imp fun hJ => ?_).mono_pre hP
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ nC.o.sp + -48 by omega) (by decide) hkc
  have hal' : (R.callee nC.o.sp (-48) 0).base.toNat % 16 = 0 := by
    have : (((R.callee nC.o.sp (-48) 0).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
    omega
  exact seg_abort2RW (fstable_enter hR hF (by omega) (by decide) hkc (by decide) (by omega) (by decide) (by decide))
    (Region.callee_ok hR (by omega) (by decide) hkc (by omega)) hal' (by simp [Region.callee])
    (by simp [Region.callee]) hK (hstub g.1 g.2.1 g.2.2 hJ)

/-- **The path's node obligations** inside `W` (`StubHRW`'s nodes, the
`write` call's node `ssvc` among them; no code, no segment). -/
structure HPathW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (c0 : Ctl) (ra : BitVec 64) : Prop where
  de : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .e) d0
  dt1 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .t1) t1
  dj1 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .j1) j1
  dt2 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .t2) t2
  dg2 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .g2) g2
  se : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .e) b0
  sn1 : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .n1)
  sn1b : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .n1b)
  sn2 : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .n2) b1Heap
  ssvc : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .svc)
  sn5 : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .n5) b2
  sex : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .ex)

/-- **Two path obligations into one**: one inside `W₁` not moved by `K`,
one inside `W₂`, `W₁ ∧ W₂` inside `W`. -/
theorem HPathW.and {W W₁ W₂ : Frag isaLSE2} {K : State → State → Prop}
    (h₁ : HPathW W₁ K exe endPc R F c0 ra) (h₂ : HPathW W₂ (fun _ _ => False) exe endPc R F c0 ra)
    (hw : ∀ s c, W₁ s c → W₂ s c → W s c) : HPathW W K exe endPc R F c0 ra := by
  have hb : ∀ {n : ND} {blk : List Directive}, BlkW W₁ K exe endPc R F n blk →
      BlkW W₂ (fun _ _ => False) exe endPc R F n blk → BlkW W K exe endPc R F n blk :=
    fun h₁ h₂ s σ c he hn hd hp hA hF hJ k hk m hA' hD =>
      ⟨hw _ c (h₁ s σ c he hn hd hp hA hF hJ k hk m hA' hD).1 (h₂ s σ c he hn hd hp hA hF hJ k hk m hA' hD).1,
        (h₁ s σ c he hn hd hp hA hF hJ k hk m hA' hD).2⟩
  have hn : ∀ {n : ND}, NodeW W₁ K exe endPc R F n → NodeW W₂ (fun _ _ => False) exe endPc R F n →
      NodeW W K exe endPc R F n :=
    fun h₁ h₂ s c hA => ⟨hw s c (h₁ s c hA).1 (h₂ s c hA).1, (h₁ s c hA).2⟩
  exact ⟨hb h₁.de h₂.de, hb h₁.dt1 h₂.dt1, hb h₁.dj1 h₂.dj1, hb h₁.dt2 h₂.dt2, hb h₁.dg2 h₂.dg2,
    hb h₁.se h₂.se, hn h₁.sn1 h₂.sn1, hn h₁.sn1b h₂.sn1b, hb h₁.sn2 h₂.sn2, hn h₁.ssvc h₂.ssvc,
    hb h₁.sn5 h₂.sn5, hn h₁.sex h₂.sex⟩

end Proof

end Disp

end Spike.Lib.A64.Abort

/-- info: 'Spike.Lib.A64.Abort.Disp.seg_jabort2RW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Abort.Disp.seg_jabort2RW
