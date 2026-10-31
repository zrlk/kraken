/-
**The heap abort path on x64 inside `W` with the return address** (the
twin of `Spike/Lib/A64AbortHeapRW.lean`): `Spike/Lib/X64AbortHeapW.lean`'s
path with the return address `ra` carried through, as
`Spike/Lib/X64AbortThreadsW.lean` does for the threads code (a caller's
instance chosen by its return address, e.g. wake.w's `ownG`, reads it at
every node).

- `seg_heapRW`: `scc_rt_abort_heap` over `NT ra` (`seg_stubRW`);
- `Disp.DN.nd2R`, `Disp.seg_disp2RW`: the dispatcher at the heap code `2`
  with `slot 8 = ra` throughout;
- `Disp.StubHRW`: the path's obligations for one source control;
  `Disp.seg_abort2RW`: the dispatcher then the stub;
- `Disp.seg_jabort2RW`: from a node at `scc_rt_abort` with `%rdi = 2` and
  `ra` pushed at `nC.o.sp`, the dispatcher in the callee's region
  `[-24, 16)` below it (`at_enter`);
- `Disp.HPathW`, `Disp.HPathW.and`: the path's node obligations alone, and
  their conjunction over two fragments.

Where x86-64 differs from AArch64 (all forced by the ISA):
- `ra` is not a register (A64's `x30`, saved at `slot (-8)` by the
  prologue) but the region's word at offset `8` (`slot 8`), which neither
  the dispatcher nor the stub writes; so `DN.nd2R` states `slot 8 = ra` at
  every node and `seg_jabort2RW` takes `hra : σ.slot nC.o.sp = ra` instead
  of `hX30`;
- no alignment premise (`hal`): the x64 callee region is `[-24, 16)` at the
  frame base `nC.o.sp - 8`, needing only `nC.o.sp % 8 = 0`;
- the stub's `leaq` is one instruction (A64's `adrp`/`add` pair, nodes
  `n1`, `n1b`), so `StubHRW`/`HPathW` have no `sn1b`; the `write` call is
  the `syscall` node `sys` (A64's `svc`).

Concrete k=2 copy of the k=5 machinery; to be generalised over k with it.
-/
import Spike.Lib.X64AbortHeapW
import Spike.Lib.X64AbortThreadsW

namespace Spike.Lib.X64.Abort

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower
  Kraken.Promising.Lower.X64 Spike.Lib.X64

set_option linter.unusedSimpArgs false

section Stubs

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {Q : Frag isa}
  {ra : BitVec 64}

/-- **`scc_rt_abort_heap` inside `W` does not return**, with the return
address `ra` at `slot 8` throughout. -/
theorem seg_heapRW {W : Frag isa} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hcode : Code heap c0 x1Heap exe endPc) (hK : ms.K = some Scc.Sem.X64.abi)
    (hWe : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .e) x0)
    (hWn1 : NodeW W K exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .n1))
    (hWn2 : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .n2) x1Heap)
    (hWn5 : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .n5) x2)
    (hWex : NodeW W K exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .ex))
    (hsys : SegW W K p lbl ms
      (At exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .sys))
      (At exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .n5)))
    (hab : ∀ s c, At exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .ex) s c →
      ms.abortAt s) :
    SegW W K p lbl ms (At exe endPc R F (NT (_root_.Executable.labels exe).label heap c0 ra .e)) Q :=
  seg_stubRW heap (by simp [x1Heap]) x1Heap_ok
    (by intro σ c hJ; rw [NT, x1Heap_run]; refine ⟨?_, rfl, ?_⟩ <;>
      simp_all [NT, JR, JI, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self, Reg64s.get64_set64_ne])
    hF hR hlo hhi hcode hK hWe hWn1 hWn2 hWn5 hWex hsys hab

end Stubs

namespace Disp

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (ra : BitVec 64)

/-- **The nodes at the heap code with the return address**: `DN.nd2`'s,
`slot 8 = ra` throughout. -/
def DN.nd2R : DN → ND
  | .e => ⟨lab "scc_rt_abort", oE, fun σ c => c = c0 ∧ σ.regs.get64 .rdi = 2#64 ∧ σ.slot 8 = ra⟩
  | .t1 => ⟨lab ".Lscc_rt_abort.entry", oD, fun σ c => c = c0 ∧ σ.slot (-8) = 2#64 ∧ σ.slot 8 = ra⟩
  | .j1 => ⟨lab ".Lscc_rt_abort.entry" + 16, oD, fun σ c => c = c0 ∧ σ.slot (-8) = 2#64 ∧ σ.slot 8 = ra⟩
  | .t2 => ⟨lab ".Lscc_rt_abort.next1", oD, fun σ c => c = c0 ∧ σ.slot (-8) = 2#64 ∧ σ.slot 8 = ra⟩
  | .g2 => ⟨lab ".Lscc_rt_abort.is2", oD, fun σ c => c = c0 ∧ σ.slot 8 = ra⟩
  | i => ⟨(DN.nd lab c0 i).pc, oD, fun _ _ => False⟩

/-- The code of `DN.nd2R`'s nodes is `DN.nd`'s: the same pcs. -/
theorem DN.nd2R_pc (i : DN) : (DN.nd2R lab c0 ra i).pc = (DN.nd lab c0 i).pc := by
  cases i <;> rfl

/-- **The dispatcher's exit to the heap stub** with the return address. -/
abbrev DX.nhr : ND := Abort.NT lab Abort.heap c0 ra .e

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {ra : BitVec 64}

/-- **`scc_rt_abort(2)` inside `W` with the return address is one segment**
from its entry to the heap stub's entry. -/
theorem seg_disp2RW {W : Frag isa} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
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
  have hentry := hcode.hentry
  cases i
  case e =>
    tnode d0 d0_ok e hWe
    rw [DN.nd2R, d0_run]
    refine .inl ⟨DN.t1, ?_, rfl, ?_⟩ <;> simp_all [DN.nd2R, upd_apply]
  case t1 =>
    tnode t1 t1_ok t1 hWt1
    rw [DN.nd2R, t1_run]
    split
    · next h => exact absurd h (by rw [hJ.2.1]; decide)
    · refine .inl ⟨DN.j1, ?_, rfl, ?_⟩ <;> simp_all [DN.nd2R, DN.nd]
  case j1 =>
    tnode j1 j1_ok j1 hWj1
    rw [DN.nd2R, j1_run]
    refine .inl ⟨DN.t2, ?_, rfl, ?_⟩ <;> simp_all [DN.nd2R, DN.nd]
  case t2 =>
    tnode t2 t2_ok t2 hWt2
    rw [DN.nd2R, t2_run]
    split
    · refine .inl ⟨DN.g2, ?_, rfl, ?_⟩ <;> simp_all [DN.nd2R, DN.nd]
    · next h => exact absurd (by rw [hJ.2.1]; decide) h
  case g2 =>
    tnode g2 g2_ok g2 hWg2
    rw [DN.nd2R, g2_run]
    refine .inr ⟨(), ?_, rfl, ?_⟩ <;>
      simp_all [DN.nd2R, DN.nd, DX.nhr, Abort.NT, Abort.heap, upd_apply]
  all_goals exact dead_ndW fun _ _ h => h

/-- **The heap abort path's obligations with the return address** for one
source control `c0` in the dispatcher's region `R` and frame condition `F`
(`StubHW` over `DN.nd2R` and `NT ra`). -/
structure StubHRW (W : Frag isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isa) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (c0 : Ctl) (ra : BitVec 64) : Prop where
  dcode : Code c0 exe endPc
  de : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .e) d0
  dt1 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .t1) t1
  dj1 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .j1) j1
  dt2 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .t2) t2
  dg2 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .g2) g2
  scode : Abort.Code heap c0 x1Heap exe endPc
  se : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .e) x0
  sn1 : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .n1)
  sn2 : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .n2) x1Heap
  sn5 : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .n5) x2
  sex : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .ex)
  sys : SegW W K p lbl ms (At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .sys))
    (At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .n5))
  ab : ∀ s c, At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .ex) s c → ms.abortAt s

/-- **`scc_rt_abort(2)` with the return address inside `W` does not
return**: `seg_disp2RW` then `seg_heapRW`. -/
theorem seg_abort2RW {W : Frag isa} {K : State → State → Prop} {Q : Frag isa}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi) (hs : StubHRW W K p lbl ms exe endPc R F c0 ra) :
    SegW W K p lbl ms (At exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .e)) Q :=
  (seg_disp2RW hF hR hlo hhi hs.dcode hs.de hs.dt1 hs.dj1 hs.dt2 hs.dg2).seq
    (seg_heapRW hF hR hlo hhi hs.scode hK hs.se hs.sn1 hs.sn2 hs.sn5 hs.sex hs.sys hs.ab)

/-- **A jump to `scc_rt_abort` with `%rdi = 2` and the return address `ra`
pushed inside `W` does not return** (`seg_jabort2W` with the return
address): the dispatcher in the callee's region `[-24, 16)` at the frame
base `nC.o.sp - 8`, given the path's obligations there for each caller's
state and source control of `nC` (`hstub`). -/
theorem seg_jabort2RW {W : Frag isa} {K : State → State → Prop} {Q : Frag isa} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hrdi : ∀ σ c, nC.J σ c → σ.regs.get64 .rdi = 2#64)
    (hra : ∀ σ c, nC.J σ c → σ.slot nC.o.sp = ra)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ nC.o.sp - 32) (hhi : nC.o.sp + 8 ≤ R.hi)
    (h8 : nC.o.sp % 8 = 0) (hK : ms.K = some Scc.Sem.X64.abi)
    (hstub : ∀ m0 σC c0, nC.J σC c0 → StubHRW W K p lbl ms exe endPc (R.callee (nC.o.sp - 8) (-24) 16)
      (fun m => F m ∧ CKept R (nC.o.sp - 8) (-24) 16 m0 m ∧ Abs R nC.o m0 σC) c0 ra) :
    SegW W K p lbl ms (At exe endPc R F nC) Q := by
  have hP : ∀ s c, At exe endPc R F nC s c → ∃ g : MachineData × AS × Ctl,
      (fun s c => At exe endPc (R.callee (nC.o.sp - 8) (-24) 16)
        (fun m => F m ∧ CKept R (nC.o.sp - 8) (-24) 16 g.1 m ∧ Abs R nC.o g.1 g.2.1)
        (DN.nd2R (_root_.Executable.labels exe).label g.2.2 ra .e) s c ∧ nC.J g.2.1 g.2.2) s c := by
    intro s c h
    obtain ⟨m0, σC, he, hn, hdc, hpc', σ, hA, hD, -, rfl, hJ⟩ :=
      at_enter (e0 := 8) (lo' := -24) (hi' := 16) (by omega) (by omega) (by omega) h
    refine ⟨(m0, σC, c), ⟨he, hn, hdc, hpc'.trans hpc, enter (nC.o.sp - 8) σC, hA, hD, rfl, hrdi σC c hJ, ?_⟩, hJ⟩
    show σC.slot (nC.o.sp - 8 + 8) = ra
    rw [show nC.o.sp - 8 + 8 = nC.o.sp by omega]; exact hra σC c hJ
  refine (SegW.exists_pre fun g => SegW.of_imp fun hJ => ?_).mono_pre hP
  exact seg_abort2RW
    (fstable_enter hR hF (by omega) (by decide) (by omega) (by omega) (by omega) (by decide) (by decide))
    (Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)) (by simp [Region.callee])
    (by simp [Region.callee]) hK (hstub g.1 g.2.1 g.2.2 hJ)

/-- **The path's node obligations** inside `W` (`StubHRW`'s nodes, the
`write` call's node `ssys` among them; no code, no segment). -/
structure HPathW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (c0 : Ctl) (ra : BitVec 64) : Prop where
  de : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .e) d0
  dt1 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .t1) t1
  dj1 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .j1) j1
  dt2 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .t2) t2
  dg2 : BlkW W K exe endPc R F (DN.nd2R (_root_.Executable.labels exe).label c0 ra .g2) g2
  se : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .e) x0
  sn1 : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .n1)
  sn2 : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .n2) x1Heap
  ssys : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .sys)
  sn5 : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .n5) x2
  sex : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label heap c0 ra .ex)

/-- **Two path obligations into one**: one inside `W₁` not moved by `K`,
one inside `W₂`, `W₁ ∧ W₂` inside `W`. -/
theorem HPathW.and {W W₁ W₂ : Frag isa} {K : State → State → Prop}
    (h₁ : HPathW W₁ K exe endPc R F c0 ra) (h₂ : HPathW W₂ (fun _ _ => False) exe endPc R F c0 ra)
    (hw : ∀ s c, W₁ s c → W₂ s c → W s c) : HPathW W K exe endPc R F c0 ra := by
  have hb : ∀ {n : ND} {blk : List (Directive × Nat)}, BlkW W₁ K exe endPc R F n blk →
      BlkW W₂ (fun _ _ => False) exe endPc R F n blk → BlkW W K exe endPc R F n blk :=
    fun h₁ h₂ s σ c he hn hd hp hA hF hJ k hk m hA' hD =>
      ⟨hw _ c (h₁ s σ c he hn hd hp hA hF hJ k hk m hA' hD).1 (h₂ s σ c he hn hd hp hA hF hJ k hk m hA' hD).1,
        (h₁ s σ c he hn hd hp hA hF hJ k hk m hA' hD).2⟩
  have hn : ∀ {n : ND}, NodeW W₁ K exe endPc R F n → NodeW W₂ (fun _ _ => False) exe endPc R F n →
      NodeW W K exe endPc R F n :=
    fun h₁ h₂ s c hA => ⟨hw s c (h₁ s c hA).1 (h₂ s c hA).1, (h₁ s c hA).2⟩
  exact ⟨hb h₁.de h₂.de, hb h₁.dt1 h₂.dt1, hb h₁.dj1 h₂.dj1, hb h₁.dt2 h₂.dt2, hb h₁.dg2 h₂.dg2,
    hb h₁.se h₂.se, hn h₁.sn1 h₂.sn1, hb h₁.sn2 h₂.sn2, hn h₁.ssys h₂.ssys,
    hb h₁.sn5 h₂.sn5, hn h₁.sex h₂.sex⟩

end Proof

end Disp

end Spike.Lib.X64.Abort

/-- info: 'Spike.Lib.X64.Abort.seg_heapRW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Abort.seg_heapRW

/-- info: 'Spike.Lib.X64.Abort.Disp.seg_disp2RW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Abort.Disp.seg_disp2RW

/-- info: 'Spike.Lib.X64.Abort.Disp.seg_abort2RW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Abort.Disp.seg_abort2RW

/-- info: 'Spike.Lib.X64.Abort.Disp.seg_jabort2RW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Abort.Disp.seg_jabort2RW

/-- info: 'Spike.Lib.X64.Abort.Disp.HPathW.and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Abort.Disp.HPathW.and
