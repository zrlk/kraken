/-
**The threads abort path on x64 inside `W`** (the twin of
`Spike/Lib/A64AbortThreadsW.lean`): `scc_rt_abort(5)` (`alloc_tcb`'s full
pool, a spawn's refused `clone`) through the dispatcher to
`scc_rt_abort_threads`, which does not return (`Spike/Lib/X64AbortWriteW.lean`
for the write code `4`, which this file follows with one more test).

- `seg_threadsW`: `scc_rt_abort_threads` (`seg_stubRW`);
- `Disp.DN.nd5`, `Disp.seg_disp5W`: the dispatcher at the threads code `5`
  (the first four tests not taken, the fifth taken, every other node
  dead), to the threads stub's entry;
- `Disp.StubTW`: the path's obligations for one source control;
  `Disp.seg_abort5W`: the dispatcher then the stub;
- `Disp.seg_jabort5W`: from a node at `scc_rt_abort` with `%rdi = 5` at any
  `%rsp` offset of a region (the return address `ra` pushed), the dispatcher
  in the callee's region `[-24, 16)` below it (`at_enter`).

The return address `ra` (the word the caller's `call` pushed) is carried
through the path. Where x86-64 differs from AArch64: `ra` is not a register
(A64's `x30`) but the region's word at offset `8` (`slot 8`), the
dispatcher's and the stub's common frame base being `8` below it; neither
writes it (the prologues push `%rbp` at `0`, the frames are below). The
stub's `leaq` is one instruction (A64's `adrp`/`add` pair, nodes `n1`,
`n1b`), so `NT` has `N`'s six nodes.

Concrete k=5; to be generalised over k together with the nd1/nd4 copies
(pre-hello.w-release cleanup).
-/
import Spike.Lib.X64AbortWriteW

namespace Spike.Lib.X64.Abort

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower
  Kraken.Promising.Lower.X64 Spike.Lib.X64

set_option linter.unusedSimpArgs false

/-! ## The stub with the return address

Duplicate of seg_stubW over NT; fold into Abort.N with a J parameter in
cleanup. -/

section RA

variable (lab : Label → Int64) (st : Stub) (c0 : Ctl) (ra : BitVec 64)

/-- Inside the stub's frame with the return address: the source has not
moved, `slot 8 = ra`. -/
def JR (σ : AS) (c : Ctl) : Prop := JI c0 σ c ∧ σ.slot 8 = ra

/-- **The stub's nodes with the return address**: `N`'s pcs and frames, each
invariant with `slot 8 = ra`. -/
def NT : PN → ND
  | .e => ⟨lab st.fn, oE, fun σ c => c = c0 ∧ σ.slot 8 = ra⟩
  | .n1 => ⟨lab st.entry, oI, JR c0 ra⟩
  | .n2 => ⟨lab st.entry + 7, oI, JR c0 ra⟩
  | .sys => ⟨pcSys lab st, oI, fun σ c => JR c0 ra σ c ∧ σ.regs.get64 .rdi = 2 ∧ σ.regs.get64 .rax = 1⟩
  | .n5 => ⟨lab st.entry + 36, oI, JR c0 ra⟩
  | .ex => ⟨lab st.exit, oI, fun σ c => JR c0 ra σ c ∧ σ.regs.get64 .rax = 231 ∧ σ.regs.get64 .rdi = 101⟩

/-- `NT`'s pcs are `N`'s. -/
@[simp] theorem NT_pc (i : PN) : (NT lab st c0 ra i).pc = (N lab st c0 i).pc := by cases i <;> rfl

end RA

section ProofRA

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {ra : BitVec 64}

/-- Hitting node `j` of `NT`. -/
macro "hitR " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;>
    simp_all [NT, JR, JI, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self, Reg64s.get64_set64_ne]))

/-- **An abort stub with the return address inside `W` does not return**:
`seg_stubW` over `NT ra` (duplicate of seg_stubW over NT; fold into Abort.N
with a J parameter in cleanup). -/
theorem seg_stubRW {W : Frag isa} {K : State → State → Prop} {Q : Frag isa} (st : Stub)
    {x1 : List (Directive × Nat)} (hne1 : x1 ≠ [])
    (hok1 : okBlk (-24) 16 oI x1 = true)
    (h1 : ∀ σ c, JR c0 ra σ c → Hit (NT (_root_.Executable.labels exe).label st c0 ra .sys)
      (arun (_root_.Executable.labels exe).label x1
        ⟨(NT (_root_.Executable.labels exe).label st c0 ra .n2).pc, oI, σ⟩) c)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hcode : Code st c0 x1 exe endPc) (hK : ms.K = some Scc.Sem.X64.abi)
    (hWe : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .e) x0)
    (hWn1 : NodeW W K exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .n1))
    (hWn2 : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .n2) x1)
    (hWn5 : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .n5) x2)
    (hWex : NodeW W K exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .ex))
    (hsys : SegW W K p lbl ms (At exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .sys))
      (At exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .n5)))
    (hab : ∀ s c, At exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .ex) s c →
      ms.abortAt s) :
    SegW W K p lbl ms (At exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .e)) Q := by
  refine (fn_segW (N := NT _ st c0 ra) (E := E) (fun i => ?_) PN.e).mono_post fun _ _ ⟨x, _⟩ => nomatch x
  have hentry := hcode.hentry
  have hexit := hcode.hexit
  cases i
  case e =>
    refine seg_ndW (by simp [x0]) x0_ok hF hR hlo hhi (fun s he hn => hcode.e s he hn) hWe
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [NT, x0_run]; hitR PN.n1
  case n1 =>
    refine si_ndW (si := siMsg st) rfl hF (fun s he hn => hcode.n1 s he hn) hWn1
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    have : (SI.step (_root_.Executable.labels exe).label (siMsg st) σ).slot = σ.slot := rfl
    hitR PN.n2
  case n2 =>
    exact seg_ndW hne1 hok1 hF hR hlo hhi (fun s he hn => hcode.n2 s he hn) hWn2
      fun σ c hJ => ⟨c, .refl c, .inl ⟨PN.sys, h1 σ c hJ⟩⟩
  case sys => exact seg_givenW PN.n5 hsys
  case n5 =>
    refine seg_ndW (by simp [x2]) x2_ok hF hR hlo hhi (fun s he hn => hcode.n5 s he hn) hWn5
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [NT, x2_run]; hitR PN.ex
  case ex =>
    refine exit_ndW hK (fun s he hn => hcode.ex s he hn) hWex (fun σ c hJ => ?_)
      fun s c _ hAt _ _ => SysOk.exitGroup_abort (hab s c hAt)
    have h := hJ.2.1
    simp only [Reg64s.get64] at h
    show σ.regs.rax.toBitVec.toNat = 231
    rw [h]; rfl

end ProofRA

section Stubs

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {Q : Frag isa}
  {ra : BitVec 64}

/-- **`scc_rt_abort_threads` inside `W` does not return**, with the return
address `ra` at `slot 8` throughout. -/
theorem seg_threadsW {W : Frag isa} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hcode : Code threads c0 x1Threads exe endPc) (hK : ms.K = some Scc.Sem.X64.abi)
    (hWe : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .e) x0)
    (hWn1 : NodeW W K exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .n1))
    (hWn2 : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .n2) x1Threads)
    (hWn5 : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .n5) x2)
    (hWex : NodeW W K exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .ex))
    (hsys : SegW W K p lbl ms
      (At exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .sys))
      (At exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .n5)))
    (hab : ∀ s c, At exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .ex) s c →
      ms.abortAt s) :
    SegW W K p lbl ms (At exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .e)) Q :=
  seg_stubRW threads (by simp [x1Threads]) x1Threads_ok
    (by intro σ c hJ; rw [NT, x1Threads_run]; refine ⟨?_, rfl, ?_⟩ <;>
      simp_all [NT, JR, JI, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self, Reg64s.get64_set64_ne])
    hF hR hlo hhi hcode hK hWe hWn1 hWn2 hWn5 hWex hsys hab

end Stubs

namespace Disp

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (ra : BitVec 64)

/-- **The nodes at the threads code**: the entry with `%rdi = 5`, the first
four tests (not taken) with `5` stored and their jumps to the next, the
fifth test, its taken jump; every other node dead. `slot 8 = ra`
throughout. -/
def DN.nd5 : DN → ND
  | .e => ⟨lab "scc_rt_abort", oE, fun σ c => c = c0 ∧ σ.regs.get64 .rdi = 5#64 ∧ σ.slot 8 = ra⟩
  | .t1 => ⟨lab ".Lscc_rt_abort.entry", oD, fun σ c => c = c0 ∧ σ.slot (-8) = 5#64 ∧ σ.slot 8 = ra⟩
  | .j1 => ⟨lab ".Lscc_rt_abort.entry" + 16, oD, fun σ c => c = c0 ∧ σ.slot (-8) = 5#64 ∧ σ.slot 8 = ra⟩
  | .t2 => ⟨lab ".Lscc_rt_abort.next1", oD, fun σ c => c = c0 ∧ σ.slot (-8) = 5#64 ∧ σ.slot 8 = ra⟩
  | .j2 => ⟨lab ".Lscc_rt_abort.next1" + 16, oD, fun σ c => c = c0 ∧ σ.slot (-8) = 5#64 ∧ σ.slot 8 = ra⟩
  | .t3 => ⟨lab ".Lscc_rt_abort.next3", oD, fun σ c => c = c0 ∧ σ.slot (-8) = 5#64 ∧ σ.slot 8 = ra⟩
  | .j3 => ⟨lab ".Lscc_rt_abort.next3" + 16, oD, fun σ c => c = c0 ∧ σ.slot (-8) = 5#64 ∧ σ.slot 8 = ra⟩
  | .t4 => ⟨lab ".Lscc_rt_abort.next5", oD, fun σ c => c = c0 ∧ σ.slot (-8) = 5#64 ∧ σ.slot 8 = ra⟩
  | .j4 => ⟨lab ".Lscc_rt_abort.next5" + 16, oD, fun σ c => c = c0 ∧ σ.slot (-8) = 5#64 ∧ σ.slot 8 = ra⟩
  | .t5 => ⟨lab ".Lscc_rt_abort.next7", oD, fun σ c => c = c0 ∧ σ.slot (-8) = 5#64 ∧ σ.slot 8 = ra⟩
  | .g5 => ⟨lab ".Lscc_rt_abort.is8", oD, fun σ c => c = c0 ∧ σ.slot 8 = ra⟩
  | i => ⟨(DN.nd lab c0 i).pc, oD, fun _ _ => False⟩

/-- The code of `DN.nd5`'s nodes is `DN.nd`'s: the same pcs. -/
theorem DN.nd5_pc (i : DN) : (DN.nd5 lab c0 ra i).pc = (DN.nd lab c0 i).pc := by
  cases i <;> rfl

/-- **The dispatcher's exit to the threads stub** with the return address. -/
abbrev DX.ntr : ND := Abort.NT lab Abort.threads c0 ra .e

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {ra : BitVec 64}

set_option hygiene false in
/-- A dispatcher node of `seg_disp5W`: the block, its `okBlk`, its code and
its `W` obligation; the edge is left. -/
macro "tnode " b:ident ok:ident f:ident hw:ident : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR (by omega) hhi
    (fun s he hn => hcode.$f s he hn) $hw fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_abort(5)` inside `W` is one segment** from its entry to the
threads stub's entry. -/
theorem seg_disp5W {W : Frag isa} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hcode : Code c0 exe endPc)
    (hWe : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .e) d0)
    (hWt1 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .t1) t1)
    (hWj1 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .j1) j1)
    (hWt2 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .t2) t2)
    (hWj2 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .j2) j2)
    (hWt3 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .t3) t3)
    (hWj3 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .j3) j3)
    (hWt4 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .t4) t4)
    (hWj4 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .j4) j4)
    (hWt5 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .t5) t5)
    (hWg5 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .g5) g5) :
    SegW W K p lbl ms (At exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .e))
      (At exe endPc R F (DX.ntr (_root_.Executable.labels exe).label c0 ra)) := by
  refine (fn_segW (N := DN.nd5 (_root_.Executable.labels exe).label c0 ra)
    (E := fun (_ : Unit) => DX.ntr (_root_.Executable.labels exe).label c0 ra) (fun i => ?_) DN.e).mono_post
    fun _ _ ⟨_, h⟩ => h
  have hentry := hcode.hentry
  cases i
  case e =>
    tnode d0 d0_ok e hWe
    rw [DN.nd5, d0_run]
    refine .inl ⟨DN.t1, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5, upd_apply]
  case t1 =>
    tnode t1 t1_ok t1 hWt1
    rw [DN.nd5, t1_run]
    split
    · next h => exact absurd h (by rw [hJ.2.1]; decide)
    · refine .inl ⟨DN.j1, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5, DN.nd]
  case j1 =>
    tnode j1 j1_ok j1 hWj1
    rw [DN.nd5, j1_run]
    refine .inl ⟨DN.t2, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5, DN.nd]
  case t2 =>
    tnode t2 t2_ok t2 hWt2
    rw [DN.nd5, t2_run]
    split
    · next h => exact absurd h (by rw [hJ.2.1]; decide)
    · refine .inl ⟨DN.j2, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5, DN.nd]
  case j2 =>
    tnode j2 j2_ok j2 hWj2
    rw [DN.nd5, j2_run]
    refine .inl ⟨DN.t3, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5, DN.nd]
  case t3 =>
    tnode t3 t3_ok t3 hWt3
    rw [DN.nd5, t3_run]
    split
    · next h => exact absurd h (by rw [hJ.2.1]; decide)
    · refine .inl ⟨DN.j3, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5, DN.nd]
  case j3 =>
    tnode j3 j3_ok j3 hWj3
    rw [DN.nd5, j3_run]
    refine .inl ⟨DN.t4, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5, DN.nd]
  case t4 =>
    tnode t4 t4_ok t4 hWt4
    rw [DN.nd5, t4_run]
    split
    · next h => exact absurd h (by rw [hJ.2.1]; decide)
    · refine .inl ⟨DN.j4, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5, DN.nd]
  case j4 =>
    tnode j4 j4_ok j4 hWj4
    rw [DN.nd5, j4_run]
    refine .inl ⟨DN.t5, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5, DN.nd]
  case t5 =>
    tnode t5 t5_ok t5 hWt5
    rw [DN.nd5, t5_run]
    split
    · refine .inl ⟨DN.g5, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5, DN.nd]
    · next h => exact absurd (by rw [hJ.2.1]; decide) h
  case g5 =>
    tnode g5 g5_ok g5 hWg5
    rw [DN.nd5, g5_run]
    refine .inr ⟨(), ?_, rfl, ?_⟩ <;>
      simp_all [DN.nd5, DN.nd, DX.ntr, Abort.NT, Abort.threads, upd_apply]
  all_goals exact dead_ndW fun _ _ h => h

/-- **The threads abort path's obligations for one source control `c0`** in
the dispatcher's region `R` and frame condition `F`: the dispatcher's and
the threads stub's code, their nodes' states inside `W` (moved by no `K`),
the stub's `write` call a segment inside `W`, and its exit call at an abort
site. -/
structure StubTW (W : Frag isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isa) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (c0 : Ctl) (ra : BitVec 64) : Prop where
  dcode : Code c0 exe endPc
  de : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .e) d0
  dt1 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .t1) t1
  dj1 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .j1) j1
  dt2 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .t2) t2
  dj2 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .j2) j2
  dt3 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .t3) t3
  dj3 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .j3) j3
  dt4 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .t4) t4
  dj4 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .j4) j4
  dt5 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .t5) t5
  dg5 : BlkW W K exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .g5) g5
  scode : Abort.Code threads c0 x1Threads exe endPc
  se : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label threads c0 ra .e) x0
  sn1 : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label threads c0 ra .n1)
  sn2 : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label threads c0 ra .n2) x1Threads
  sn5 : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label threads c0 ra .n5) x2
  sex : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label threads c0 ra .ex)
  sys : SegW W K p lbl ms (At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label threads c0 ra .sys))
    (At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label threads c0 ra .n5))
  ab : ∀ s c, At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label threads c0 ra .ex) s c → ms.abortAt s

/-- **`scc_rt_abort(5)` inside `W` does not return**: the dispatcher at the
threads code (`seg_disp5W`) then `scc_rt_abort_threads` (`seg_threadsW`). -/
theorem seg_abort5W {W : Frag isa} {K : State → State → Prop} {Q : Frag isa}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi) (hs : StubTW W K p lbl ms exe endPc R F c0 ra) :
    SegW W K p lbl ms (At exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .e)) Q :=
  (seg_disp5W hF hR hlo hhi hs.dcode hs.de hs.dt1 hs.dj1 hs.dt2 hs.dj2 hs.dt3 hs.dj3 hs.dt4 hs.dj4
      hs.dt5 hs.dg5).seq
    (seg_threadsW hF hR hlo hhi hs.scode hK hs.se hs.sn1 hs.sn2 hs.sn5 hs.sex hs.sys hs.ab)

/-- **A jump to `scc_rt_abort` with `%rdi = 5` inside `W` does not
return**: from a node `nC` at `scc_rt_abort` (`%rsp` at `nC.o.sp` in `R`,
the return address `ra` pushed at `nC.o.sp`, `%rdi = 5` in every state of
its invariant) a segment to any fragment, the dispatcher running in the
callee's region `[-24, 16)` at the frame base `nC.o.sp - 8` (`at_enter`),
given the threads abort path's obligations there for each caller's state
`m0`, `σC` and source control of `nC` (`hstub`). -/
theorem seg_jabort5W {W : Frag isa} {K : State → State → Prop} {Q : Frag isa} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hrdi : ∀ σ c, nC.J σ c → σ.regs.get64 .rdi = 5#64)
    (hra : ∀ σ c, nC.J σ c → σ.slot nC.o.sp = ra)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ nC.o.sp - 32) (hhi : nC.o.sp + 8 ≤ R.hi)
    (h8 : nC.o.sp % 8 = 0) (hK : ms.K = some Scc.Sem.X64.abi)
    (hstub : ∀ m0 σC c0, nC.J σC c0 → StubTW W K p lbl ms exe endPc (R.callee (nC.o.sp - 8) (-24) 16)
      (fun m => F m ∧ CKept R (nC.o.sp - 8) (-24) 16 m0 m ∧ Abs R nC.o m0 σC) c0 ra) :
    SegW W K p lbl ms (At exe endPc R F nC) Q := by
  have hP : ∀ s c, At exe endPc R F nC s c → ∃ g : MachineData × AS × Ctl,
      (fun s c => At exe endPc (R.callee (nC.o.sp - 8) (-24) 16)
        (fun m => F m ∧ CKept R (nC.o.sp - 8) (-24) 16 g.1 m ∧ Abs R nC.o g.1 g.2.1)
        (DN.nd5 (_root_.Executable.labels exe).label g.2.2 ra .e) s c ∧ nC.J g.2.1 g.2.2) s c := by
    intro s c h
    obtain ⟨m0, σC, he, hn, hdc, hpc', σ, hA, hD, -, rfl, hJ⟩ :=
      at_enter (e0 := 8) (lo' := -24) (hi' := 16) (by omega) (by omega) (by omega) h
    refine ⟨(m0, σC, c), ⟨he, hn, hdc, hpc'.trans hpc, enter (nC.o.sp - 8) σC, hA, hD, rfl, hrdi σC c hJ, ?_⟩, hJ⟩
    show σC.slot (nC.o.sp - 8 + 8) = ra
    rw [show nC.o.sp - 8 + 8 = nC.o.sp by omega]; exact hra σC c hJ
  refine (SegW.exists_pre fun g => SegW.of_imp fun hJ => ?_).mono_pre hP
  exact seg_abort5W
    (fstable_enter hR hF (by omega) (by decide) (by omega) (by omega) (by omega) (by decide) (by decide))
    (Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)) (by simp [Region.callee])
    (by simp [Region.callee]) hK (hstub g.1 g.2.1 g.2.2 hJ)

end Proof

end Disp

end Spike.Lib.X64.Abort

/-- info: 'Spike.Lib.X64.Abort.seg_stubRW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Abort.seg_stubRW

/-- info: 'Spike.Lib.X64.Abort.seg_threadsW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Abort.seg_threadsW

/-- info: 'Spike.Lib.X64.Abort.Disp.DN.nd5_pc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Abort.Disp.DN.nd5_pc

/-- info: 'Spike.Lib.X64.Abort.Disp.seg_disp5W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Abort.Disp.seg_disp5W

/-- info: 'Spike.Lib.X64.Abort.Disp.seg_abort5W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Abort.Disp.seg_abort5W

/-- info: 'Spike.Lib.X64.Abort.Disp.seg_jabort5W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Abort.Disp.seg_jabort5W
