/-
**wake.w on x86-64: main after its `clone`** (the spawn's parent half, the
twin of `Spike/Lib/A64WakeParent.lean`): back from the clone's `syscall`
(`X64WakeClone.wcNS`, `.Lwc_main.x21 + 46`) with the child's id
`0 < %rax < pidMax` (`Spike.Lib.X64Handover.parent_st`), main runs

    testq %rax, %rax                    -- row (test_ndW): ZF clear
    je .Lwc_main.child.scc_rt_thr_worker                -- not taken
    .x22: movq %rax, -56(%rbp); movq -56(%rbp), %rax; movq $0, %rcx
          cmpq %rcx, %rax; jl .Lwc_main.spawnfail5      -- not taken
          jmp .Lwc_main.spawned6
    .spawned6: movq -16(%rbp), %rdi; movq %rbp, %rsp; popq %rbp
               jmp wc_waitLoop                          -- the tail call

in its frame (`oW`), to `wc_waitLoop`'s entry with `%rdi` the cell, `%rsp`
at offset 8, `%rbp` the caller's (`pE`). The source (past its `spawn`, at
`tail waitLoop c`) takes its tail call on the last block (`hrun`). The
`syscall` keeps every register but `%rax`, `%rcx`, `%r11`, so the thread
pointer `fsBase` is the caller's throughout (`JS`).

- `pN lab cP A fp ra tp`: the nodes (`PN`: `ts`, `je`, `x22`, `bs`, `sp`);
  `pE`: the exit at `wc_waitLoop`.
- `parentIn cells`: the blocks and rows at their places.
- `seg_parent`: main from `pN .ts` (past the clone) to `pE`.
-/
import Spike.Lib.X64WakeClone

namespace Spike.Lib.X64.WakePh.Parent

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.WakePh.WcClone (oW x21L)
open Scc.Cert.Rt.X64 (Lays endOf blockAt labelGap codeAt_blockAt_lays label_labelGap_lays)

/-! ## The blocks -/

/-- The clone's result test (a row). -/
def tsB : List (Directive × Nat) := [(testDir .rax .rax, 3)]

/-- The branch to the child. -/
def jeB : List (Directive × Nat) := (parse("je .Lwc_main.child.scc_rt_thr_worker")).zip [2]

/-- `.x22`'s first block: the id to `-56` and back, compared with 0. -/
def x22B : List (Directive × Nat) := (parse("movq %rax, -56(%rbp)
movq -56(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
jl .Lwc_main.spawnfail5")).zip [4, 4, 7, 3, 2]

/-- The branch to `.spawned6`. -/
def bsB : List (Directive × Nat) := (parse("jmp .Lwc_main.spawned6")).zip [2]

/-- `.spawned6`: the cell to `%rdi`, the frame left, the tail call. -/
def spB : List (Directive × Nat) := (parse("movq -16(%rbp), %rdi
movq %rbp, %rsp
popq %rbp
jmp wc_waitLoop")).zip [4, 3, 1, 5]

example : (parse("testq %rax, %rax")).zip [3] = tsB := by decide

block_spec jeB (-64) 16 oW jeB
block_spec x22B (-64) 16 oW x22B
block_spec bsB (-64) 16 oW bsB
block_spec spB (-64) 16 oW spB

abbrev x22L : Label := ".Lwc_main.x22"
abbrev spL : Label := ".Lwc_main.spawned6"

/-- **The parent's blocks and rows in `cells`**: the test and the `je` at
`.x21 + 48`, `+ 51`; `.x22` fifteen cells (53 bytes) after `.x21`; its
blocks; `.spawned6`'s. -/
def parentIn (cells : List (Directive × Nat)) : Bool :=
  blockAt cells x21L 13 48 tsB && blockAt cells x21L 14 51 jeB && labelGap cells x21L x22L 15 53 &&
    blockAt cells x22L 0 0 x22B && blockAt cells x22L 5 20 bsB && blockAt cells spL 0 0 spB

/-! ## The nodes -/

/-- In main's frame: the source at `cP`, the cell's address `A` at `-16`,
the caller's `%rbp` (`fp`) and return address (`ra`) in their cells, the
thread pointer `tp`. -/
def JS (cP : Ctl) (A fp ra tp : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = cP ∧ σ.slot (-16) = A ∧ σ.slot 0 = fp ∧ σ.slot 8 = ra ∧ σ.regs.fsBase.toBitVec = tp

/-- The child's id: `0 < %rax < pidMax`. -/
def Id (σ : AS) : Prop := 0 < (σ.regs.get64 .rax).toNat ∧ (σ.regs.get64 .rax).toNat < Scc.Sem.Kernel.pidMax

/-- The parent's internal nodes. -/
inductive PN where
  | ts | je | x22 | bs | sp

/-- **The parent's nodes**: past the clone (`ts`), the `je`, `.x22`, its
branch (`bs`), `.spawned6` (`sp`). -/
def pN (lab : Label → Int64) (cP : Ctl) (A fp ra tp : BitVec 64) : PN → ND
  | .ts => ⟨lab x21L + 48, oW, fun σ c => JS cP A fp ra tp σ c ∧ Id σ⟩
  | .je => ⟨lab x21L + 51, oW, fun σ c => JS cP A fp ra tp σ c ∧ Id σ ∧ σ.status.zf = false⟩
  | .x22 => ⟨lab x22L, oW, fun σ c => JS cP A fp ra tp σ c ∧ Id σ⟩
  | .bs => ⟨lab x22L + 20, oW, JS cP A fp ra tp⟩
  | .sp => ⟨lab spL, oW, JS cP A fp ra tp⟩

/-- **The exit**: `wc_waitLoop`'s entry, `%rsp` at offset 8 (the caller's
return address), `%rdi` the cell, `%rbp` the caller's, the source at `c0`. -/
def pE (lab : Label → Int64) (c0 : Ctl) (A fp ra tp : BitVec 64) : ND :=
  ⟨lab "wc_waitLoop", ⟨8, []⟩, fun σ c => c = c0 ∧ σ.regs.get64 .rdi = A ∧ σ.regs.get64 .rbp = fp ∧
    σ.slot 8 = ra ∧ σ.regs.fsBase.toBitVec = tp⟩

/-! ## The segment -/

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **Main after its clone is one segment** in any valid layout of cells
holding the blocks (`parentIn`), from `pN .ts` to `wc_waitLoop`'s entry:
the `je` and the `jl` are not taken (`%rax` the child's id), the frame is
left and the source takes its tail call (`hrun`). -/
theorem seg_parent {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : parentIn cells = true)
    {cP c0 : Ctl} {A fp ra tp : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -64) (hhi : 16 ≤ R.hi) (hrun : LocalRun p cP c0) :
    Seg p lbl ms (At exe endPc R F (pN (_root_.Executable.labels exe).label cP A fp ra tp .ts))
      (At exe endPc R F (pE (_root_.Executable.labels exe).label c0 A fp ra tp)) := by
  simp only [parentIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨bts, bje⟩, hgap⟩, b22⟩, bbs⟩, bsp⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have hg : lab x22L = lab x21L + Int64.ofNat 53 := label_labelGap_lays hp hgap
  have code : ∀ {l : Label} {k off : Nat} {b : List (Directive × Nat)}, blockAt cells l k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab l + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  have code0 : ∀ {l : Label} {k : Nat} {b : List (Directive × Nat)}, blockAt cells l k 0 b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab l) b :=
    fun h s he hn => by simpa using code h s he hn
  refine (fn_seg (N := pN lab cP A fp ra tp) (E := fun _ : Unit => pE lab c0 A fp ra tp) (fun i => ?_)
    PN.ts).mono_post fun _ _ ⟨_, h⟩ => h
  cases i
  case ts =>
    refine test_nd hF (fun s he hn => code bts s he hn) fun σ c hJ af => ⟨c, .refl c, .inl ⟨PN.je, ?_, rfl, ?_⟩⟩
    · show lab x21L + 51 = lab x21L + Int64.ofNat 48 + Int64.ofNat 3
      rw [Int64.add_assoc]; rfl
    · obtain ⟨hS, h0, h1⟩ := hJ
      refine ⟨hS, ⟨h0, h1⟩, ?_⟩
      rw [testStep_zf, BitVec.and_self]
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h; rw [h] at h0; simp at h0
  case je =>
    refine seg_nd (by simp [jeB]) jeB_ok hF hR hlo hhi (fun s he hn => code bje s he hn)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨PN.x22, ?_, rfl, hJ.1, hJ.2.1⟩⟩
    obtain ⟨-, -, hz⟩ := hJ
    show lab x22L = (arun lab jeB ⟨lab x21L + 51, oW, σ⟩).pc
    rw [jeB_run]
    simp only [hz, hg, Bool.false_eq_true, ite_false, Int64.add_assoc]; rfl
  case x22 =>
    refine seg_nd (by simp [x22B]) x22B_ok hF hR hlo hhi (fun s he hn => code0 b22 s he hn)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨PN.bs, ?_, rfl, ?_⟩⟩
    · obtain ⟨-, -, h1⟩ := hJ
      have hm : σ.regs.rax.toBitVec.msb = false := by
        have : (σ.regs.get64 .rax).toNat < 2 ^ 63 := by unfold Scc.Sem.Kernel.pidMax at h1; omega
        rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not, Nat.not_le]
        exact this
      show lab x22L + 20 = (arun lab x22B ⟨lab x22L, oW, σ⟩).pc
      rw [x22B_run]; simp only [hm, Bool.false_eq_true, ite_false]
    · obtain ⟨⟨rfl, h16, h0, h8, htp⟩, -⟩ := hJ
      show JS c A fp ra tp (arun lab x22B ⟨lab x22L, oW, σ⟩).σ c
      rw [x22B_run]
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp [upd, h16, h0, h8, htp, Reg64s.set64]
  case bs =>
    refine seg_nd (by simp [bsB]) bsB_ok hF hR hlo hhi (fun s he hn => code bbs s he hn)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨PN.sp, ?_, rfl, ?_⟩⟩
    · show lab spL = (arun lab bsB ⟨lab x22L + 20, oW, σ⟩).pc
      rw [bsB_run]
    · show JS cP A fp ra tp (arun lab bsB ⟨lab x22L + 20, oW, σ⟩).σ c
      rw [bsB_run]; exact hJ
  case sp =>
    refine seg_nd (by simp [spB]) spB_ok hF hR hlo hhi (fun s he hn => code0 bsp s he hn)
      fun σ c hJ => ⟨c0, ?_, .inr ⟨(), ?_, ?_, ?_⟩⟩
    · obtain ⟨rfl, -⟩ := hJ; exact hrun
    · show lab "wc_waitLoop" = (arun lab spB ⟨lab spL, oW, σ⟩).pc
      rw [spB_run]
    · show SO.le ⟨8, []⟩ (arun lab spB ⟨lab spL, oW, σ⟩).so = true
      rw [spB_run]; rfl
    · obtain ⟨-, h16, h0, h8, htp⟩ := hJ
      show c0 = c0 ∧ _
      simp only [pN]
      rw [spB_run]
      refine ⟨trivial, ?_, ?_, h8, ?_⟩ <;>
        simp (disch := decide) only [Reg64s.get64_set64_self, Reg64s.get64_set64_ne, h16, h0]
      simpa [Reg64s.set64] using htp

end Seg

/-- info: 'Spike.Lib.X64.WakePh.Parent.seg_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_parent

end Spike.Lib.X64.WakePh.Parent
