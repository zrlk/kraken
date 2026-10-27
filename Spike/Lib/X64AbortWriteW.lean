/-
**The write abort path on x64 inside `W`**: `scc_rt_abort(4)` (`print`'s
jump when the `write` system call fails) through the dispatcher to
`scc_rt_abort_write`, which does not return (`Spike/Lib/X64AbortHeapW.lean`
for the heap code). The AArch64 mirror is `Spike/Lib/A64AbortWriteW.lean`.

- `seg_writeW`: `scc_rt_abort_write` (`seg_stubW`);
- `Disp.DN.nd4`, `Disp.seg_disp4W`: the dispatcher at the write code `4`
  (the first three tests not taken, the fourth taken, every other node
  dead), to the write stub's entry;
- `Disp.StubWW`: the path's obligations for one source control;
  `Disp.seg_abort4W`: the dispatcher then the stub;
- `Disp.seg_jabort4W`: from a node at `scc_rt_abort` with `%rdi = 4` at any
  `%rsp` offset of a region (the return address pushed), the dispatcher in
  the callee's region `[-24, 16)` below it (`at_enter`).
-/
import Spike.Lib.X64AbortW
import Spike.Lib.SegCommon

namespace Spike.Lib.X64.Abort

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower
  Kraken.Promising.Lower.X64 Spike.Lib.X64

set_option linter.unusedSimpArgs false

section Stubs

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {Q : Frag isa}

/-- **`scc_rt_abort_write` inside `W` does not return.** -/
theorem seg_writeW {W : Frag isa} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hcode : Code write c0 x1Write exe endPc) (hK : ms.K = some Scc.Sem.X64.abi)
    (hWe : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label write c0 .e) x0)
    (hWn1 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label write c0 .n1))
    (hWn2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label write c0 .n2) x1Write)
    (hWn5 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label write c0 .n5) x2)
    (hWex : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label write c0 .ex))
    (hsys : SegW W K p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label write c0 .sys))
      (At exe endPc R F (N (_root_.Executable.labels exe).label write c0 .n5)))
    (hab : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label write c0 .ex) s c →
      ms.abortAt s) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label write c0 .e)) Q :=
  seg_stubW write (by simp [x1Write]) x1Write_ok (by arg_hit x1Write_run)
    hF hR hlo hhi hcode hK hWe hWn1 hWn2 hWn5 hWex hsys hab

end Stubs

namespace Disp

section Spec

variable (lab : Label → Int64) (c0 : Ctl)

/-- **The nodes at the write code**: the entry with `%rdi = 4`, the first
three tests (not taken) with `4` stored and their jumps to the next, the
fourth test, its taken jump; every other node dead. -/
def DN.nd4 : DN → ND
  | .e => ⟨lab "scc_rt_abort", oE, fun σ c => c = c0 ∧ σ.regs.get64 .rdi = 4#64⟩
  | .t1 => ⟨lab ".Lscc_rt_abort.entry", oD, fun σ c => c = c0 ∧ σ.slot (-8) = 4#64⟩
  | .j1 => ⟨lab ".Lscc_rt_abort.entry" + 16, oD, fun σ c => c = c0 ∧ σ.slot (-8) = 4#64⟩
  | .t2 => ⟨lab ".Lscc_rt_abort.next1", oD, fun σ c => c = c0 ∧ σ.slot (-8) = 4#64⟩
  | .j2 => ⟨lab ".Lscc_rt_abort.next1" + 16, oD, fun σ c => c = c0 ∧ σ.slot (-8) = 4#64⟩
  | .t3 => ⟨lab ".Lscc_rt_abort.next3", oD, fun σ c => c = c0 ∧ σ.slot (-8) = 4#64⟩
  | .j3 => ⟨lab ".Lscc_rt_abort.next3" + 16, oD, fun σ c => c = c0 ∧ σ.slot (-8) = 4#64⟩
  | .t4 => ⟨lab ".Lscc_rt_abort.next5", oD, fun σ c => c = c0 ∧ σ.slot (-8) = 4#64⟩
  | .g4 => ⟨lab ".Lscc_rt_abort.is6", oD, fun _ c => c = c0⟩
  | i => ⟨(DN.nd lab c0 i).pc, oD, fun _ _ => False⟩

/-- The code of `DN.nd4`'s nodes is `DN.nd`'s: the same pcs. -/
theorem DN.nd4_pc (i : DN) : (DN.nd4 lab c0 i).pc = (DN.nd lab c0 i).pc := by
  cases i <;> rfl

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}

/-- **`scc_rt_abort(4)` inside `W` is one segment** from its entry to the
write stub's entry, given the states of the entry block, the four tests, the
first three's fall-through jumps and the fourth's taken jump inside `W`. -/
theorem seg_disp4W {W : Frag isa} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
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
    (E := fun (_ : Unit) => DX.nd (_root_.Executable.labels exe).label c0 .write) (fun i => ?_)
    DN.e).mono_post fun _ _ ⟨_, h⟩ => h
  have hentry := hcode.hentry
  cases i
  case e =>
    refine seg_ndW (by simp [d0]) d0_ok hF hR (by omega) hhi (fun s he hn => hcode.e s he hn) hWe
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [DN.nd4, d0_run]
    refine .inl ⟨DN.t1, ?_, rfl, ?_⟩ <;>
      simp_all [DN.nd4, upd_apply]
  case t1 =>
    refine seg_ndW (by simp [t1]) t1_ok hF hR (by omega) hhi (fun s he hn => hcode.t1 s he hn) hWt1
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [DN.nd4, t1_run]
    split
    · next h => exact absurd h (by rw [hJ.2]; decide)
    · refine .inl ⟨DN.j1, ?_, rfl, ?_⟩ <;> simp_all [DN.nd4, DN.nd]
  case j1 =>
    refine seg_ndW (by simp [j1]) j1_ok hF hR (by omega) hhi (fun s he hn => hcode.j1 s he hn) hWj1
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [DN.nd4, j1_run]
    refine .inl ⟨DN.t2, ?_, rfl, ?_⟩ <;> simp_all [DN.nd4, DN.nd]
  case t2 =>
    refine seg_ndW (by simp [t2]) t2_ok hF hR (by omega) hhi (fun s he hn => hcode.t2 s he hn) hWt2
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [DN.nd4, t2_run]
    split
    · next h => exact absurd h (by rw [hJ.2]; decide)
    · refine .inl ⟨DN.j2, ?_, rfl, ?_⟩ <;> simp_all [DN.nd4, DN.nd]
  case j2 =>
    refine seg_ndW (by simp [j2]) j2_ok hF hR (by omega) hhi (fun s he hn => hcode.j2 s he hn) hWj2
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [DN.nd4, j2_run]
    refine .inl ⟨DN.t3, ?_, rfl, ?_⟩ <;> simp_all [DN.nd4, DN.nd]
  case t3 =>
    refine seg_ndW (by simp [t3]) t3_ok hF hR (by omega) hhi (fun s he hn => hcode.t3 s he hn) hWt3
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [DN.nd4, t3_run]
    split
    · next h => exact absurd h (by rw [hJ.2]; decide)
    · refine .inl ⟨DN.j3, ?_, rfl, ?_⟩ <;> simp_all [DN.nd4, DN.nd]
  case j3 =>
    refine seg_ndW (by simp [j3]) j3_ok hF hR (by omega) hhi (fun s he hn => hcode.j3 s he hn) hWj3
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [DN.nd4, j3_run]
    refine .inl ⟨DN.t4, ?_, rfl, ?_⟩ <;> simp_all [DN.nd4, DN.nd]
  case t4 =>
    refine seg_ndW (by simp [t4]) t4_ok hF hR (by omega) hhi (fun s he hn => hcode.t4 s he hn) hWt4
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [DN.nd4, t4_run]
    split
    · refine .inl ⟨DN.g4, ?_, rfl, ?_⟩ <;> simp_all [DN.nd4, DN.nd]
    · next h => exact absurd (by rw [hJ.2]; decide) h
  case g4 =>
    refine seg_ndW (by simp [g4]) g4_ok hF hR (by omega) hhi (fun s he hn => hcode.g4 s he hn) hWg4
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [DN.nd4, g4_run]
    refine .inr ⟨(), ?_, rfl, ?_⟩ <;> simp_all [DN.nd4, DN.nd, DX.nd, DX.stub, Abort.N, Abort.write]
  all_goals exact dead_ndW fun _ _ h => h

/-- **The write abort path's obligations for one source control `c0`** in
the dispatcher's region `R` and frame condition `F`: the dispatcher's and
the write stub's code, their nodes' states inside `W` (moved by no `K`), the
stub's `write` call a segment inside `W`, and its exit call at an abort
site. -/
structure StubWW (W : Frag isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isa) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
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
  scode : Abort.Code write c0 x1Write exe endPc
  se : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .e) x0
  sn1 : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .n1)
  sn2 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .n2) x1Write
  sn5 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .n5) x2
  sex : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .ex)
  sys : SegW W K p lbl ms (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .sys))
    (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .n5))
  ab : ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .ex) s c → ms.abortAt s

/-- **`scc_rt_abort(4)` inside `W` does not return**: the dispatcher at the
write code (`seg_disp4W`) then `scc_rt_abort_write` (`seg_writeW`); the stub's
frame base is the dispatcher's. -/
theorem seg_abort4W {W : Frag isa} {K : State → State → Prop} {Q : Frag isa}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi) (hs : StubWW W K p lbl ms exe endPc R F c0) :
    SegW W K p lbl ms (At exe endPc R F (DN.nd4 (_root_.Executable.labels exe).label c0 .e)) Q :=
  (seg_disp4W hF hR hlo hhi hs.dcode hs.de hs.dt1 hs.dj1 hs.dt2 hs.dj2 hs.dt3 hs.dj3 hs.dt4 hs.dg4).seq
    (seg_writeW hF hR hlo hhi hs.scode hK hs.se hs.sn1 hs.sn2 hs.sn5 hs.sex hs.sys hs.ab)

/-- **A jump to `scc_rt_abort` with `%rdi = 4` inside `W` does not
return**: from a node `nC` at `scc_rt_abort` (`%rsp` at `nC.o.sp` in `R`,
the return address pushed, `%rdi = 4` in every state of its invariant) a
segment to any fragment, the dispatcher running in the callee's region
`[-24, 16)` at the frame base `nC.o.sp - 8` (`at_enter`), given the write
abort path's obligations there for each caller's state `m0`, `σC` and
source control of `nC` (`hstub`). -/
theorem seg_jabort4W {W : Frag isa} {K : State → State → Prop} {Q : Frag isa} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hrdi : ∀ σ c, nC.J σ c → σ.regs.get64 .rdi = 4#64)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ nC.o.sp - 32) (hhi : nC.o.sp + 8 ≤ R.hi)
    (h8 : nC.o.sp % 8 = 0) (hK : ms.K = some Scc.Sem.X64.abi)
    (hstub : ∀ m0 σC c0, nC.J σC c0 → StubWW W K p lbl ms exe endPc (R.callee (nC.o.sp - 8) (-24) 16)
      (fun m => F m ∧ CKept R (nC.o.sp - 8) (-24) 16 m0 m ∧ Abs R nC.o m0 σC) c0) :
    SegW W K p lbl ms (At exe endPc R F nC) Q := by
  have hP : ∀ s c, At exe endPc R F nC s c → ∃ g : MachineData × AS × Ctl,
      (fun s c => At exe endPc (R.callee (nC.o.sp - 8) (-24) 16)
        (fun m => F m ∧ CKept R (nC.o.sp - 8) (-24) 16 g.1 m ∧ Abs R nC.o g.1 g.2.1)
        (DN.nd4 (_root_.Executable.labels exe).label g.2.2 .e) s c ∧ nC.J g.2.1 g.2.2) s c := by
    intro s c h
    obtain ⟨m0, σC, he, hn, hdc, hpc', σ, hA, hD, -, rfl, hJ⟩ :=
      at_enter (e0 := 8) (lo' := -24) (hi' := 16) (by omega) (by omega) (by omega) h
    exact ⟨(m0, σC, c), ⟨he, hn, hdc, hpc'.trans hpc, enter (nC.o.sp - 8) σC, hA, hD, rfl, hrdi σC c hJ⟩, hJ⟩
  refine (SegW.exists_pre fun g => SegW.of_imp fun hJ => ?_).mono_pre hP
  exact seg_abort4W
    (fstable_enter hR hF (by omega) (by decide) (by omega) (by omega) (by omega) (by decide) (by decide))
    (Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)) (by simp [Region.callee])
    (by simp [Region.callee]) hK (hstub g.1 g.2.1 g.2.2 hJ)

end Proof

end Disp

end Spike.Lib.X64.Abort
