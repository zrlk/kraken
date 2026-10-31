/-
**wake.w on x86-64: the child after its `clone`** (the spawn's child half,
the twin of `Spike/Lib/A64WakeChild.lean`'s stub): past the clone's
`syscall` (`X64WakeClone.wcNS`, `.Lwc_main.x21 + 46`), the child is the
parent's registers with `%rax = 0`, `%rsp` the handed stack's top and
`fsBase` the TLS (`Spike.Lib.X64Handover.child_st`): `%r12` and `%rbx` still
hold the worker's two words (the `syscall` writes `%rax`, `%rcx`, `%r11`
only). It runs

    testq %rax, %rax                    -- row (test_ndW): ZF set
    je .Lwc_main.child.scc_rt_thr_worker                -- taken
    .child: xorl %ebp, %ebp             -- row (flag_ndW)
            movq %r12, %rdi; movq %rbx, %rsi
            call scc_rt_thr_worker                      (chB)

in a region at its stack's top (`⟨0, []⟩`: `%rsp` at offset 0), to
`scc_rt_thr_worker`'s entry with `%rdi`, `%rsi` the two words, `%rbp`
zero, the return address `.child + 13` at offset `-8` (`cE`). The source
stutters (`cW`).

- `childJ`, `childN cW A B tp sp0`: the child's node at the `testq`.
- `cN`, `cE`: the internal nodes and the exit; `childIn cells`.
- `seg_child`: from `childN` to `cE`.
-/
import Spike.Lib.X64WakeClone

namespace Spike.Lib.X64.WakePh.Child

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.WakePh.WcClone (x21L)
open Scc.Cert.Rt.X64 (Lays endOf blockAt codeAt_blockAt_lays)

/-! ## The blocks -/

/-- The child's offsets: `%rsp` at the region's base. -/
abbrev oC : SO := ⟨0, []⟩

/-- The clone's result test (a row). -/
def tsB : List (Directive × Nat) := [(testDir .rax .rax, 3)]

/-- The branch to the child. -/
def jeB : List (Directive × Nat) := (parse("je .Lwc_main.child.scc_rt_thr_worker")).zip [2]

/-- `xorl %ebp, %ebp` (a row). -/
def xbp : List (Directive × Nat) := [(FI.toDir (.xor_rr32_self .rbp), 2)]

/-- The call of the worker thread on the two words. -/
def chB : List (Directive × Nat) := (parse("movq %r12, %rdi
movq %rbx, %rsi
call scc_rt_thr_worker")).zip [3, 3, 5]

example : (parse("testq %rax, %rax
xorl %ebp, %ebp")).zip [3, 2] = tsB ++ xbp := by decide

block_spec jeB (-128) 0 oC jeB
block_spec chB (-128) 0 oC chB

abbrev chL : Label := ".Lwc_main.child.scc_rt_thr_worker"

/-- **The child's blocks and rows in `cells`**: the test and the `je` at
`.x21 + 48`, `+ 51`; `.child`'s row and call block. -/
def childIn (cells : List (Directive × Nat)) : Bool :=
  blockAt cells x21L 13 48 tsB && blockAt cells x21L 14 51 jeB && blockAt cells chL 0 0 xbp &&
    blockAt cells chL 1 2 chB

/-! ## The nodes -/

/-- The child's invariant: the source at `cW`, `%r12`/`%rbx` the worker's
two words `A`/`B`, the thread pointer `tp`, `%rsp` at `sp0`. -/
def childJ (cW : Ctl) (A B tp sp0 : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = cW ∧ σ.regs.get64 .r12 = A ∧ σ.regs.get64 .rbx = B ∧ σ.regs.fsBase.toBitVec = tp ∧
    σ.regs.get64 .rsp = sp0

/-- **The child's node** past the clone's `syscall`, at the `testq`: `%rax = 0`. -/
def childN (lab : Label → Int64) (cW : Ctl) (A B tp sp0 : BitVec 64) : ND :=
  ⟨lab x21L + 48, oC, fun σ c => childJ cW A B tp sp0 σ c ∧ σ.regs.get64 .rax = 0#64⟩

/-- The child's internal nodes. -/
inductive CN where
  | ts | je | xb | ch

/-- The child's nodes. -/
def cN (lab : Label → Int64) (cW : Ctl) (A B tp sp0 : BitVec 64) : CN → ND
  | .ts => childN lab cW A B tp sp0
  | .je => ⟨lab x21L + 51, oC, fun σ c => childJ cW A B tp sp0 σ c ∧ σ.status.zf = true⟩
  | .xb => ⟨lab chL, oC, childJ cW A B tp sp0⟩
  | .ch => ⟨lab chL + 2, oC, fun σ c => childJ cW A B tp sp0 σ c ∧ σ.regs.get64 .rbp = 0#64⟩

/-- **The exit**: `scc_rt_thr_worker`'s entry, `%rsp` at `-8` holding the
return address `.child + 13`, `%rdi`/`%rsi` the two words, `%rbp` zero. -/
def cE (lab : Label → Int64) (cW : Ctl) (A B tp sp0 : BitVec 64) : ND :=
  ⟨lab "scc_rt_thr_worker", ⟨-8, []⟩, fun σ c => c = cW ∧ σ.regs.get64 .rdi = A ∧ σ.regs.get64 .rsi = B ∧
    σ.regs.get64 .rbp = 0#64 ∧ σ.regs.fsBase.toBitVec = tp ∧ σ.regs.get64 .rsp = sp0 - 8#64 ∧
    σ.slot (-8) = (lab chL + 13).toBitVec⟩

/-! ## The segment -/

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **The child up to the worker thread is one segment** in any valid
layout of cells holding the blocks (`childIn`), from its node past the
clone (`childN`) to `scc_rt_thr_worker`'s entry (`cE`): the `je` taken
(`%rax = 0`), `%rbp` zeroed, the two words moved to the argument registers. -/
theorem seg_child {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : childIn cells = true)
    {cW : Ctl} {A B tp sp0 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi) :
    Seg p lbl ms (At exe endPc R F (childN (_root_.Executable.labels exe).label cW A B tp sp0))
      (At exe endPc R F (cE (_root_.Executable.labels exe).label cW A B tp sp0)) := by
  simp only [childIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨bts, bje⟩, bxb⟩, bch⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have code : ∀ {l : Label} {k off : Nat} {b : List (Directive × Nat)}, blockAt cells l k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab l + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  refine (fn_seg (N := cN lab cW A B tp sp0) (E := fun _ : Unit => cE lab cW A B tp sp0) (fun i => ?_)
    CN.ts).mono_post fun _ _ ⟨_, h⟩ => h
  cases i
  case ts =>
    refine test_nd hF (fun s he hn => code bts s he hn) fun σ c hJ af => ⟨c, .refl c, .inl ⟨CN.je, ?_, rfl, ?_⟩⟩
    · show lab x21L + 51 = lab x21L + Int64.ofNat 48 + Int64.ofNat 3
      rw [Int64.add_assoc]; rfl
    · obtain ⟨hS, h0⟩ := hJ
      exact ⟨hS, by rw [testStep_zf, h0]; rfl⟩
  case je =>
    refine seg_nd (by simp [jeB]) jeB_ok hF hR hlo hhi (fun s he hn => code bje s he hn)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨CN.xb, ?_, rfl, hJ.1⟩⟩
    show lab chL = (arun lab jeB ⟨lab x21L + 51, oC, σ⟩).pc
    rw [jeB_run]; simp only [hJ.2, ite_true]
  case xb =>
    refine flag_nd (fi := .xor_rr32_self .rbp) rfl hF
      (fun s he hn => (by simpa using code bxb s he hn : CodeAt s (lab chL) xbp)) fun σ c hJ fl =>
        ⟨c, .refl c, .inl ⟨CN.ch, ?_, rfl, ?_, ?_⟩⟩
    · rfl
    · obtain ⟨h0, h12, hbx, htp, hsp⟩ := hJ
      refine ⟨h0, ?_, ?_, ?_, ?_⟩ <;>
        simp (disch := decide) only [FI.step, FI.regs, Reg64s.get64_set64_ne, h12, hbx, hsp]
      simpa [FI.step, FI.regs, Reg64s.set64] using htp
    · simp only [FI.step, FI.regs, Reg64s.get64_set64_self]; rfl
  case ch =>
    refine seg_nd (by simp [chB]) chB_ok hF hR hlo hhi (fun s he hn => code bch s he hn)
      fun σ c hJ => ⟨c, .refl c, .inr ⟨(), ?_, rfl, ?_⟩⟩
    · show lab "scc_rt_thr_worker" = (arun lab chB ⟨lab chL + 2, oC, σ⟩).pc
      rw [chB_run]
    · obtain ⟨⟨h0, h12, hbx, htp, hsp⟩, hbp⟩ := hJ
      show cE lab cW A B tp sp0 |>.J (arun lab chB ⟨lab chL + 2, oC, σ⟩).σ c
      rw [chB_run]
      simp only [Reg64s.get64] at h12 hbx hbp hsp
      refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Reg64s.get64, Reg64s.set64, h12]
      · simp [Reg64s.get64, Reg64s.set64, hbx]
      · simp [Reg64s.get64, Reg64s.set64, hbp]
      · simpa [Reg64s.set64] using htp
      · simp [Reg64s.get64, Reg64s.set64, hsp]
      · simp only [upd_apply, ite_true]
        rw [Int64.toBitVec_add, BitVec.add_assoc]; rfl

end Seg

/-- info: 'Spike.Lib.X64.WakePh.Child.seg_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_child

end Spike.Lib.X64.WakePh.Child
