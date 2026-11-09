/-
**hello.w on x86-64: main after its `clone`** (the spawn's parent half): back from the
clone's `syscall` (`.Lwc_main.x3 + 94` in hello.w's x86-64 listing, `SccCode.helloCells`) with the child's id
`0 < %rax < pidMax`, main runs

    testq %rax, %rax                    -- row (test_ndW): ZF clear
    je .Lwc_main.child.scc_rt_thr_worker                -- not taken
    .x26: movq %rax, -120(%rbp); movq -120(%rbp), %rax; movq $0, %rcx
          cmpq %rcx, %rax; jl .Lwc_main.spawnfail5      -- not taken
          jmp .Lwc_main.spawned6
    .spawned6: movq -48(%rbp), %rdi; movq %rbp, %rsp; popq %rbp
               jmp wc_waitLoop                          -- the tail call

in its frame (offsets from `%rbp`: `%rsp` at `-128`, the published cell's address at `-48`, the caller's
`%rbp` and the return address at `0`/`8`), to `wc_waitLoop`'s entry with `%rdi` the cell, `%rsp` at offset 8,
`%rbp` the caller's (`pE`). wake.w's (`Spike/Lib/X64WakeParent.lean`) at hello's frame of 128 and labels
(`.x25`, `.x26`).

- `oP`: the offsets in main's frame; `tsB`, `jeB`, `x26B`, `bsB`, `spB`: the blocks.
- `JS`, `Id`, `pN lab cP A fp ra tp` (`PN`: `ts`, `je`, `x26`, `bs`, `sp`), `pE`: the nodes and the exit.
- `parentIn`, `hello_parentIn`: the blocks in hello's cells.
- `seg_parent`: main from `pN .ts` (past the clone) to `pE`.

## Differences from the AArch64 version

`Spike/Lib/A64HelloParent.lean`.

- The blocks are x86-64's (as wake's `X64WakeParent`): the clone's result tested by a `testq` row and a
  `je` rather than a `cbz`, the id spilled at `-120(%rbp)` and compared (`x26B`, ending in `jl
  .Lwc_main.spawnfail5`; AArch64's `cl`), `.spawned6`'s tail call through `popq %rbp`. The labels are the
  listing's own: no `pfx` templates (`cbPT`, `clT`, `bsT`, `cl`, `bs` and their `_eq`/`_run` relabellings).
- The frame is addressed from `%rbp` (`oP = ⟨-128, [(.rbp, 0)]⟩`); `JS` has the caller's `%rbp` and return
  address at `0`/`8` (AArch64: `x29`/`x30` at `-16`/`-8`) and the thread pointer in `fsBase`; the child's id
  is `Id` (`%rax`), not part of `JP`.
- The exit `pE` is stated directly (`wc_waitLoop`'s entry at offset 8); there is no `pE_eq` (x86-64's
  `X64WaitLoop` hard-codes wake's labels).
- `seg_parent` is twinned (it is dead in the AArch64 closure, where the parent's run is re-proved in its
  fragment): it is the x86-64 shape the spawn's assembly uses (`X64WakeParent.seg_parent`).
-/
import Spike.Lib.X64HelloChild
import Spike.Lib.X64WakeParent

namespace Spike.Lib.X64.Flow.Worker.Hello.Parent

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow.Worker.Hello.Child (x25L chL)
open Scc.Cert.Rt.X64 (Lays endOf blockAt labelGap codeAt_blockAt_lays label_labelGap_lays)

/-! ## The blocks -/

/-- The offsets in main's frame (from `%rbp`: frame 128). -/
abbrev oP : SO := ⟨-128, [(.rbp, 0)]⟩

/-- The clone's result test (a row). -/
def tsB : List (Directive × Nat) := [(testDir .rax .rax, 3)]

/-- The branch to the child. -/
def jeB : List (Directive × Nat) := (parse("je .Lwc_main.child.scc_rt_thr_worker")).zip [2]

/-- `.x26`'s first block: the id to `-120` and back, compared with 0. -/
def x26B : List (Directive × Nat) := (parse("movq %rax, -120(%rbp)
movq -120(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
jl .Lwc_main.spawnfail5")).zip [4, 4, 7, 3, 2]

/-- The branch to `.spawned6`. -/
def bsB : List (Directive × Nat) := (parse("jmp .Lwc_main.spawned6")).zip [2]

/-- `.spawned6`: the cell to `%rdi`, the frame left, the tail call. -/
def spB : List (Directive × Nat) := (parse("movq -48(%rbp), %rdi
movq %rbp, %rsp
popq %rbp
jmp wc_waitLoop")).zip [4, 3, 1, 5]

example : (parse("testq %rax, %rax")).zip [3] = tsB := by decide

block_spec jeB (-128) 16 oP jeB
block_spec x26B (-128) 16 oP x26B
block_spec bsB (-128) 16 oP bsB
block_spec spB (-128) 16 oP spB

abbrev x26L : Label := ".Lwc_main.x4"
abbrev spL : Label := ".Lwc_main.spawned6"

/-- **The parent's blocks and rows in `cells`**: the test and the `je` at
`.x25 + 96`, `+ 99`; `.x26` twenty-seven cells (101 bytes) after `.x25`;
its blocks; `.spawned6`'s. -/
def parentIn (cells : List (Directive × Nat)) : Bool :=
  blockAt cells x25L 25 96 tsB && blockAt cells x25L 26 99 jeB && labelGap cells x25L x26L 27 101 &&
    blockAt cells x26L 0 0 x26B && blockAt cells x26L 5 20 bsB && blockAt cells spL 0 0 spB

theorem hello_parentIn : parentIn SccCode.helloCells = true := by decide +kernel

/-! ## The nodes -/

/-- In main's frame: the source at `cP`, the cell's address `A` at `-48`,
the caller's `%rbp` (`fp`) and return address (`ra`) in their cells, the
thread pointer `tp`. -/
def JS (cP : Ctl) (A fp ra tp : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = cP ∧ σ.slot (-48) = A ∧ σ.slot 0 = fp ∧ σ.slot 8 = ra ∧ σ.regs.fsBase.toBitVec = tp

/-- The child's id: `0 < %rax < pidMax`. -/
def Id (σ : AS) : Prop := 0 < (σ.regs.get64 .rax).toNat ∧ (σ.regs.get64 .rax).toNat < Scc.Sem.Kernel.pidMax

/-- The parent's internal nodes. -/
inductive PN where
  | ts | je | x26 | bs | sp

/-- **The parent's nodes**: past the clone (`ts`), the `je`, `.x26`, its
branch (`bs`), `.spawned6` (`sp`). -/
def pN (lab : Label → Int64) (cP : Ctl) (A fp ra tp : BitVec 64) : PN → ND
  | .ts => ⟨lab x25L + 96, oP, fun σ c => JS cP A fp ra tp σ c ∧ Id σ⟩
  | .je => ⟨lab x25L + 99, oP, fun σ c => JS cP A fp ra tp σ c ∧ Id σ ∧ σ.status.zf = false⟩
  | .x26 => ⟨lab x26L, oP, fun σ c => JS cP A fp ra tp σ c ∧ Id σ⟩
  | .bs => ⟨lab x26L + 20, oP, JS cP A fp ra tp⟩
  | .sp => ⟨lab spL, oP, JS cP A fp ra tp⟩

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
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 16 ≤ R.hi) (hrun : LocalRun p cP c0) :
    Seg p lbl ms (At exe endPc R F (pN (_root_.Executable.labels exe).label cP A fp ra tp .ts))
      (At exe endPc R F (pE (_root_.Executable.labels exe).label c0 A fp ra tp)) := by
  simp only [parentIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨bts, bje⟩, hgap⟩, b26⟩, bbs⟩, bsp⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have hg : lab x26L = lab x25L + Int64.ofNat 101 := label_labelGap_lays hp hgap
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
    · show lab x25L + 99 = lab x25L + Int64.ofNat 96 + Int64.ofNat 3
      rw [Int64.add_assoc]; rfl
    · obtain ⟨hS, h0, h1⟩ := hJ
      refine ⟨hS, ⟨h0, h1⟩, ?_⟩
      rw [testStep_zf, BitVec.and_self]
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h; rw [h] at h0; simp at h0
  case je =>
    refine seg_nd (by simp [jeB]) jeB_ok hF hR hlo hhi (fun s he hn => code bje s he hn)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨PN.x26, ?_, rfl, hJ.1, hJ.2.1⟩⟩
    obtain ⟨-, -, hz⟩ := hJ
    show lab x26L = (arun lab jeB ⟨lab x25L + 99, oP, σ⟩).pc
    rw [jeB_run]
    simp only [hz, hg, Bool.false_eq_true, ite_false, Int64.add_assoc]; rfl
  case x26 =>
    refine seg_nd (by simp [x26B]) x26B_ok hF hR hlo hhi (fun s he hn => code0 b26 s he hn)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨PN.bs, ?_, rfl, ?_⟩⟩
    · obtain ⟨-, -, h1⟩ := hJ
      have hm : σ.regs.rax.toBitVec.msb = false := by
        have : (σ.regs.get64 .rax).toNat < 2 ^ 63 := by unfold Scc.Sem.Kernel.pidMax at h1; omega
        rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not, Nat.not_le]
        exact this
      show lab x26L + 20 = (arun lab x26B ⟨lab x26L, oP, σ⟩).pc
      rw [x26B_run]; simp only [hm, Bool.false_eq_true, ite_false]
    · obtain ⟨⟨rfl, h48, h0, h8, htp⟩, -⟩ := hJ
      show JS c A fp ra tp (arun lab x26B ⟨lab x26L, oP, σ⟩).σ c
      rw [x26B_run]
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp [upd, h48, h0, h8, htp, Reg64s.set64]
  case bs =>
    refine seg_nd (by simp [bsB]) bsB_ok hF hR hlo hhi (fun s he hn => code bbs s he hn)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨PN.sp, ?_, rfl, ?_⟩⟩
    · show lab spL = (arun lab bsB ⟨lab x26L + 20, oP, σ⟩).pc
      rw [bsB_run]
    · show JS cP A fp ra tp (arun lab bsB ⟨lab x26L + 20, oP, σ⟩).σ c
      rw [bsB_run]; exact hJ
  case sp =>
    refine seg_nd (by simp [spB]) spB_ok hF hR hlo hhi (fun s he hn => code0 bsp s he hn)
      fun σ c hJ => ⟨c0, ?_, .inr ⟨(), ?_, ?_, ?_⟩⟩
    · obtain ⟨rfl, -⟩ := hJ; exact hrun
    · show lab "wc_waitLoop" = (arun lab spB ⟨lab spL, oP, σ⟩).pc
      rw [spB_run]
    · show SO.le ⟨8, []⟩ (arun lab spB ⟨lab spL, oP, σ⟩).so = true
      rw [spB_run]; rfl
    · obtain ⟨-, h48, h0, h8, htp⟩ := hJ
      show c0 = c0 ∧ _
      simp only [pN]
      rw [spB_run]
      refine ⟨trivial, ?_, ?_, h8, ?_⟩ <;>
        simp (disch := decide) only [Reg64s.get64_set64_self, Reg64s.get64_set64_ne, h48, h0]
      simpa [Reg64s.set64] using htp

end Seg

end Spike.Lib.X64.Flow.Worker.Hello.Parent

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Parent.seg_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Parent.seg_parent

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Parent.hello_parentIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Parent.hello_parentIn
