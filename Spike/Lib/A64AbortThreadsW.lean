/-
**The threads abort path on AArch64 inside `W`**: `scc_rt_abort(5)` (a
spawn's jump when the kernel refuses `clone`) through the dispatcher to
`scc_rt_abort_threads`, which does not return (`Spike/Lib/A64AbortWriteW.lean`
for the write code `4`, which this file follows with one more test).

- `seg_threadsW`: `scc_rt_abort_threads` (`seg_stubW`);
- `Disp.DN.nd5`, `Disp.seg_disp5W`: the dispatcher at the threads code `5`
  (the first four tests not taken, the fifth taken, every other node
  dead), to the threads stub's entry;
- `Disp.StubTW`: the path's obligations for one source control;
  `Disp.seg_abort5W`: the dispatcher then the stub;
- `Disp.seg_jabort5W`: from a node at `scc_rt_abort` with `x0 = 5` at any
  `sp` offset of a region, the dispatcher in the region below it
  (`at_enter`).

The return address `ra` (the caller's `bl`'s `x30`) is carried through the
path: `x30 = ra` at the dispatcher's entry, saved at `[sp + 24]` (`slot (-8)`)
by its prologue and restored from there by `g5`, and kept by the stub
(`NT ra`, `seg_stubRW`); the threads abort phase (`ThreadsAb.Ac`) tells the
spawn's code-5 site from the other ones by it.

Concrete k=5; to be generalised over k together with the nd1/nd2/nd4 copies
(pre-hello.w-release cleanup).
-/
import Spike.Lib.A64AbortWriteW
import Spike.Lib.SegCommon

namespace Spike.Lib.A64.Abort

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

set_option linter.unusedSimpArgs false

/-! ## The stub with the return address

Duplicate of seg_stubW over NT; fold into Abort.N with a J parameter in
cleanup. -/

section RA

variable (lab : Label → Int64) (st : Stub) (c0 : Ctl) (ra : BitVec 64)

/-- Inside the stub's frame with the return address: the source has not
moved, `x30 = ra`. -/
def JR (σ : AS) (c : Ctl) : Prop := JI c0 σ c ∧ σ.regs.X30.toBitVec = ra

/-- **The stub's nodes with the return address**: `N`'s pcs and frames, each
invariant with `x30 = ra`. -/
def NT : PN → ND
  | .e => ⟨lab st.fn, oE, fun σ c => c = c0 ∧ σ.regs.X30.toBitVec = ra⟩
  | .n1 => ⟨lab st.entry, oI, JR c0 ra⟩
  | .n1b => ⟨lab st.entry + 4, oI, JR c0 ra⟩
  | .n2 => ⟨lab st.entry + 4 + 4, oI, JR c0 ra⟩
  | .svc => ⟨pcSvc lab st, oI, fun σ c => JR c0 ra σ c ∧ σ.regs.X0 = 2 ∧ σ.regs.X8 = 64⟩
  | .n5 => ⟨pcSvc lab st + 4, oI, JR c0 ra⟩
  | .ex => ⟨lab st.exit, oI, fun σ c => JR c0 ra σ c ∧ σ.regs.X8 = 94 ∧ σ.regs.X0 = 101⟩

/-- `NT`'s pcs are `N`'s. -/
@[simp] theorem NT_pc (i : PN) : (NT lab st c0 ra i).pc = (N lab st c0 i).pc := by cases i <;> rfl

end RA

section ProofRA

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {ra : BitVec 64}

/-- The message's address leaves `x30`. -/
theorem si_x30 (lab : Label → Int64) (si : SI) (σ : AS) (h : si.dst = some .X9) :
    (SI.step lab si σ).regs.X30.toBitVec = σ.regs.X30.toBitVec := by
  have := SI.regs_get lab si σ.regs (x := .reg .X30) (by intro d hd; rw [h] at hd; cases hd; decide)
  simpa [SI.step, Reg64s.getRegOrSp64] using this

/-- Hitting node `j` of `NT`. -/
macro "hitR " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [NT, JR, JI, upd_apply]))

/-- **An abort stub with the return address inside `W` does not return**:
`seg_stubW` over `NT ra` (duplicate of seg_stubW over NT; fold into Abort.N
with a J parameter in cleanup). -/
theorem seg_stubRW {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2} (st : Stub)
    {b1 : List Directive} (hne1 : b1 ≠ [])
    (hok1 : okBlk (-48) 0 oI b1 = true)
    (h1 : ∀ σ c, JR c0 ra σ c → Hit (NT (_root_.Executable.labels exe).label st c0 ra .svc)
      (arun (_root_.Executable.labels exe).label b1
        ⟨(NT (_root_.Executable.labels exe).label st c0 ra .n2).pc, oI, σ⟩) c)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code st c0 b1 exe endPc) (hK : ms.K = some Scc.Sem.A64.abi)
    (hWe : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .e) b0)
    (hWn1 : NodeW W K exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .n1))
    (hWn1b : NodeW W K exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .n1b))
    (hWn2 : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .n2) b1)
    (hWn5 : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .n5) b2)
    (hWex : NodeW W K exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .ex))
    (hsvc : SegW W K p lbl ms (At exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .svc))
      (At exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .n5)))
    (hab : ∀ s c, At exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .ex) s c →
      ms.abortAt s) :
    SegW W K p lbl ms (At exe endPc R F (NT (_root_.Executable.labels exe).label st c0 ra .e)) Q := by
  refine (fn_segW (N := NT _ st c0 ra) (E := E) (fun i => ?_) PN.e).mono_post
    fun _ _ ⟨x, _⟩ => nomatch x
  have hentry := hcode.hentry
  have hexit := hcode.hexit
  cases i
  case e =>
    refine seg_ndW (by simp [b0]) b0_ok hF hR hal hlo hhi (fun s he hn => hcode.e s he hn)
      hWe fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [NT, b0_run]; hitR PN.n1
  case n1 =>
    refine si_ndW (si := .adrp .X9 st.msg) hF (fun s he hn => hcode.n1 s he hn) hWn1
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    have := si_x30 (_root_.Executable.labels exe).label (.adrp .X9 st.msg) σ rfl
    hitR PN.n1b
  case n1b =>
    refine si_ndW (si := .addLo12 .X9 .X9 st.msg) hF (fun s he hn => hcode.n1b s he hn) hWn1b
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    have := si_x30 (_root_.Executable.labels exe).label (.addLo12 .X9 .X9 st.msg) σ rfl
    hitR PN.n2
  case n2 =>
    exact seg_ndW hne1 hok1 hF hR hal hlo hhi (fun s he hn => hcode.n2 s he hn) hWn2
      fun σ c hJ => ⟨c, .refl c, .inl ⟨PN.svc, h1 σ c hJ⟩⟩
  case svc => exact seg_givenW PN.n5 hsvc
  case n5 =>
    refine seg_ndW (by simp [b2]) b2_ok hF hR hal hlo hhi (fun s he hn => hcode.n5 s he hn)
      hWn5 fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [NT, b2_run]; hitR PN.ex
  case ex =>
    refine exit_ndW hK (fun s he hn => hcode.ex s he hn) hWex (fun σ c hJ => ?_)
      fun s c _ hAt _ _ => SysOk.exitGroup_abort (hab s c hAt)
    rw [hJ.2.1]; rfl

end ProofRA

section Stubs

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {Q : Frag isaLSE2}
  {ra : BitVec 64}

/-- **`scc_rt_abort_threads` inside `W` does not return**, with the return address `ra`
in `x30` throughout. -/
theorem seg_threadsW {W : Frag isaLSE2} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code threads c0 b1Threads exe endPc) (hK : ms.K = some Scc.Sem.A64.abi)
    (hWe : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .e) b0)
    (hWn1 : NodeW W K exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .n1))
    (hWn1b : NodeW W K exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .n1b))
    (hWn2 : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .n2) b1Threads)
    (hWn5 : BlkW W K exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .n5) b2)
    (hWex : NodeW W K exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .ex))
    (hsvc : SegW W K p lbl ms
      (At exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .svc))
      (At exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .n5)))
    (hab : ∀ s c, At exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .ex) s c →
      ms.abortAt s) :
    SegW W K p lbl ms (At exe endPc R F (NT (_root_.Executable.labels exe).label threads c0 ra .e)) Q :=
  seg_stubRW threads (by simp [b1Threads]) b1Threads_ok
    (by intro σ c hJ; rw [NT, b1Threads_run]; refine ⟨?_, rfl, ?_⟩ <;> simp_all [NT, JR, JI, upd_apply])
    hF hR hal hlo hhi hcode hK hWe hWn1 hWn1b hWn2 hWn5 hWex hsvc hab

end Stubs

namespace Disp

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (ra : BitVec 64)

/-- **The nodes at the threads code**: the entry with `x0 = 5`, the first
four tests (not taken) with `5` stored and their jumps to the next, the
fifth test, its taken jump; every other node dead. `x30 = ra` throughout,
and saved at `slot (-8)` after the prologue. -/
def DN.nd5 : DN → ND
  | .e => ⟨lab "scc_rt_abort", oE, fun σ c => c = c0 ∧ σ.regs.X0.toBitVec.toNat = 5 ∧ σ.regs.X30.toBitVec = ra⟩
  | .t1 => ⟨lab ".L12_scc_rt_abort.0_entry", oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 5 ∧ σ.slot (-8) = ra ∧ σ.regs.X30.toBitVec = ra⟩
  | .j1 => ⟨lab ".L12_scc_rt_abort.0_entry" + 4 + 4 + 4 + 4, oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 5 ∧ σ.slot (-8) = ra ∧ σ.regs.X30.toBitVec = ra⟩
  | .t2 => ⟨lab ".L12_scc_rt_abort.2_next1", oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 5 ∧ σ.slot (-8) = ra ∧ σ.regs.X30.toBitVec = ra⟩
  | .j2 => ⟨lab ".L12_scc_rt_abort.2_next1" + 4 + 4 + 4 + 4, oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 5 ∧ σ.slot (-8) = ra ∧ σ.regs.X30.toBitVec = ra⟩
  | .t3 => ⟨lab ".L12_scc_rt_abort.4_next3", oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 5 ∧ σ.slot (-8) = ra ∧ σ.regs.X30.toBitVec = ra⟩
  | .j3 => ⟨lab ".L12_scc_rt_abort.4_next3" + 4 + 4 + 4 + 4, oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 5 ∧ σ.slot (-8) = ra ∧ σ.regs.X30.toBitVec = ra⟩
  | .t4 => ⟨lab ".L12_scc_rt_abort.6_next5", oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 5 ∧ σ.slot (-8) = ra ∧ σ.regs.X30.toBitVec = ra⟩
  | .j4 => ⟨lab ".L12_scc_rt_abort.6_next5" + 4 + 4 + 4 + 4, oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 5 ∧ σ.slot (-8) = ra ∧ σ.regs.X30.toBitVec = ra⟩
  | .t5 => ⟨lab ".L12_scc_rt_abort.8_next7", oD, fun σ c => c = c0 ∧ (σ.slot (-32)).toNat = 5 ∧ σ.slot (-8) = ra ∧ σ.regs.X30.toBitVec = ra⟩
  | .g5 => ⟨lab ".L12_scc_rt_abort.9_is8", oD, fun σ c => c = c0 ∧ σ.slot (-8) = ra ∧ σ.regs.X30.toBitVec = ra⟩
  | i => ⟨(DN.nd lab c0 i).pc, oD, fun _ _ => False⟩

/-- **The dispatcher's exit to the threads stub** with the return address. -/
abbrev DX.ntr : ND := Abort.NT lab Abort.threads c0 ra .e

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {ra : BitVec 64}

set_option hygiene false in
/-- A dispatcher node of `seg_disp5W`: the block, its `okBlk`, its code and
its `W` obligation; the edge is left. -/
macro "tnode " b:ident ok:ident f:ident hw:ident : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hal (by omega) hhi
    (fun s he hn => hcode.$f s he hn) $hw fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A test with `5` stored: the branch against it contradicts the stored code. -/
macro "tnot" : tactic =>
  `(tactic| (exfalso
             obtain ⟨-, h4, -⟩ := hJ
             have e : σ.slot (-32) = 5#64 := BitVec.eq_of_toNat_eq (by simpa using h4)
             rw [e] at h
             revert h; decide))

/-- **`scc_rt_abort(5)` inside `W` is one segment** from its entry to the
threads stub's entry. -/
theorem seg_disp5W {W : Frag isaLSE2} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
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
  · have hentry := hcode.hentry
    cases i
    case e =>
      tnode d0 d0_ok e hWe
      rw [DN.nd5, d0_run]
      refine .inl ⟨DN.t1, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5, upd_apply]
    case t1 =>
      tnode t1 t1_ok t1 hWt1
      rw [DN.nd5, t1_run]
      split
      · next h => tnot
      · refine .inl ⟨DN.j1, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5]
    case j1 =>
      tnode j1 j1_ok j1 hWj1
      rw [DN.nd5, j1_run]
      refine .inl ⟨DN.t2, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5, DN.nd]
    case t2 =>
      tnode t2 t2_ok t2 hWt2
      rw [DN.nd5, t2_run]
      split
      · next h => tnot
      · refine .inl ⟨DN.j2, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5]
    case j2 =>
      tnode j2 j2_ok j2 hWj2
      rw [DN.nd5, j2_run]
      refine .inl ⟨DN.t3, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5, DN.nd]
    case t3 =>
      tnode t3 t3_ok t3 hWt3
      rw [DN.nd5, t3_run]
      split
      · next h => tnot
      · refine .inl ⟨DN.j3, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5]
    case j3 =>
      tnode j3 j3_ok j3 hWj3
      rw [DN.nd5, j3_run]
      refine .inl ⟨DN.t4, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5, DN.nd]
    case t4 =>
      tnode t4 t4_ok t4 hWt4
      rw [DN.nd5, t4_run]
      split
      · next h => tnot
      · refine .inl ⟨DN.j4, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5]
    case j4 =>
      tnode j4 j4_ok j4 hWj4
      rw [DN.nd5, j4_run]
      refine .inl ⟨DN.t5, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5, DN.nd]
    case t5 =>
      tnode t5 t5_ok t5 hWt5
      rw [DN.nd5, t5_run]
      split
      · refine .inl ⟨DN.g5, ?_, rfl, ?_⟩ <;> simp_all [DN.nd5]
      · next h => tnot
    case g5 =>
      tnode g5 g5_ok g5 hWg5
      rw [DN.nd5, g5_run]
      refine .inr ⟨(), ?_, rfl, ?_⟩ <;>
        simp_all [DN.nd5, DX.ntr, Abort.NT, Abort.threads]
    all_goals exact dead_ndW fun _ _ h => h

/-- **The threads abort path's obligations for one source control `c0`** in
the dispatcher's region `R` and frame condition `F`: the dispatcher's and
the threads stub's code, their nodes' states inside `W` (moved by no `K`), the
stub's `write` call a segment inside `W`, and its exit call at an abort
site. -/
structure StubTW (W : Frag isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
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
  scode : Abort.Code threads c0 b1Threads exe endPc
  se : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label threads c0 ra .e) b0
  sn1 : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label threads c0 ra .n1)
  sn1b : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label threads c0 ra .n1b)
  sn2 : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label threads c0 ra .n2) b1Threads
  sn5 : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label threads c0 ra .n5) b2
  sex : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label threads c0 ra .ex)
  svc : SegW W K p lbl ms (At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label threads c0 ra .svc))
    (At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label threads c0 ra .n5))
  ab : ∀ s c, At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label threads c0 ra .ex) s c → ms.abortAt s

/-- **`scc_rt_abort(5)` inside `W` does not return**: the dispatcher at the
threads code (`seg_disp5W`) then `scc_rt_abort_threads` (`seg_threadsW`). -/
theorem seg_abort5W {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi) (hs : StubTW W K p lbl ms exe endPc R F c0 ra) :
    SegW W K p lbl ms (At exe endPc R F (DN.nd5 (_root_.Executable.labels exe).label c0 ra .e)) Q :=
  (seg_disp5W hF hR hal hlo hhi hs.dcode hs.de hs.dt1 hs.dj1 hs.dt2 hs.dj2 hs.dt3 hs.dj3 hs.dt4 hs.dj4
      hs.dt5 hs.dg5).seq
    (seg_threadsW hF hR hal hlo hhi hs.scode hK hs.se hs.sn1 hs.sn1b hs.sn2 hs.sn5 hs.sex hs.svc hs.ab)

/-- **A jump to `scc_rt_abort` with `x0 = 5` inside `W` does not return**:
from a node `nC` at `scc_rt_abort` (`sp` at `nC.o.sp` in `R`, `x0 = 5` and `x30 = ra` in
every state of its invariant) a segment to any fragment, the dispatcher
running in the region below `nC.o.sp` (`at_enter`), given the threads abort
path's obligations there for each caller's state `m0`, `σC` and source
control of `nC` (`hstub`). -/
theorem seg_jabort5W {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hX0 : ∀ σ c, nC.J σ c → σ.regs.X0.toBitVec.toNat = 5)
    (hX30 : ∀ σ c, nC.J σ c → σ.regs.X30.toBitVec = ra)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ nC.o.sp - 48)
    (hkc : nC.o.sp < R.hi) (h16 : nC.o.sp % 16 = 0) (hK : ms.K = some Scc.Sem.A64.abi)
    (hstub : ∀ m0 σC c0, nC.J σC c0 → StubTW W K p lbl ms exe endPc (R.callee nC.o.sp (-48) 0)
      (fun m => F m ∧ CKept R nC.o.sp (-48) 0 m0 m ∧ Abs R nC.o m0 σC) c0 ra) :
    SegW W K p lbl ms (At exe endPc R F nC) Q := by
  have hP : ∀ s c, At exe endPc R F nC s c → ∃ g : MachineData × AS × Ctl,
      (fun s c => At exe endPc (R.callee nC.o.sp (-48) 0)
        (fun m => F m ∧ CKept R nC.o.sp (-48) 0 g.1 m ∧ Abs R nC.o g.1 g.2.1)
        (DN.nd5 (_root_.Executable.labels exe).label g.2.2 ra .e) s c ∧ nC.J g.2.1 g.2.2) s c := by
    intro s c h
    obtain ⟨m0, σC, he, hn, hdc, hpc', σ, hA, hD, -, rfl, hJ⟩ :=
      at_enter (lo' := -48) (hi' := 0) (by omega) hkc (by decide) (by omega) h
    exact ⟨(m0, σC, c), ⟨he, hn, hdc, hpc'.trans hpc, enter nC.o.sp σC, hA, hD, rfl, hX0 σC c hJ, hX30 σC c hJ⟩, hJ⟩
  refine (SegW.exists_pre fun g => SegW.of_imp fun hJ => ?_).mono_pre hP
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ nC.o.sp + -48 by omega) (by decide) hkc
  have hal' : (R.callee nC.o.sp (-48) 0).base.toNat % 16 = 0 := by
    have : (((R.callee nC.o.sp (-48) 0).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
    omega
  exact seg_abort5W (fstable_enter hR hF (by omega) (by decide) hkc (by decide) (by omega) (by decide) (by decide))
    (Region.callee_ok hR (by omega) (by decide) hkc (by omega)) hal' (by simp [Region.callee])
    (by simp [Region.callee]) hK (hstub g.1 g.2.1 g.2.2 hJ)

end Proof

end Disp

end Spike.Lib.A64.Abort
