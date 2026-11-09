/-
**hello.w on x86-64: the child's stub** (the spawn's child half): after main's `clone`
(the `syscall` at `wc_main`'s `.x25 + 94` in hello.w's x86-64 listing, `SccCode.helloCells`), the child thread
(`%rax = 0`, `%rsp` the handed stack's top, `fsBase` its TCB, the other registers the parent's: `%r12`,
`%rbx`, `%r13`, `%r14`, `%r15`, `%r9` hold the worker's six words; the `syscall` writes `%rax`, `%rcx`, `%r11`
only) runs

    testq %rax, %rax                    -- row (test_ndW): ZF set
    je .Lwc_main.child.scc_rt_thr_worker                -- taken
    .child: xorl %ebp, %ebp             -- row (flag_ndW)
            movq %r12, %rdi; movq %rbx, %rsi; movq %r13, %rdx
            movq %r14, %rcx; movq %r15, %r8
            call scc_rt_thr_worker                      (chB)

in a region at its stack's top (`⟨0, []⟩`: `%rsp` at offset 0), to `scc_rt_thr_worker`'s entry with
`%rdi .. %r9` the six words, `%rbp` zero, the return address `.child + 22` at offset `-8` (`cE`). The source
stutters (`cW`). wake.w's (`Spike/Lib/X64WakeChild.lean`) with hello's packet of six words: the slice's four
words, the cell and the waiter.

- `Words`: the six words; `thrJE`: `scc_rt_thr_worker`'s entry, the six words in `%rdi .. %r9`; `thrJ`: after
  its prologue, the six words in its frame; `wcJE`: `wc_worker`'s entry.
- `childJ`, `childN cW w tp sp0`: the child's node at the `testq`.
- `cN`, `cE`: the internal nodes and the exit; `childIn cells`, `hello_childIn`.
- `seg_child`: from `childN` to `cE`.

## Differences from the AArch64 version

`Spike/Lib/A64HelloChild.lean`.

- The stub is x86-64's (as wake's `X64WakeChild`): the clone's result tested (`testq`/`je`) rather than a
  `cbz`, `%rbp` zeroed by a flag row, the words moved from `%r12, %rbx, %r13, %r14, %r15` (the sixth, `%r9`,
  is already in place) and the return address of the call pushed (`cE` at offset `-8`). The labels are the
  listing's own (no `pfxM`/`cbT` relabelling).
- The child's segment ends at `scc_rt_thr_worker`'s entry (`seg_child`, a `Seg`, wake's x86-64 shape), not at
  any fragment given the worker thread; the AArch64 `seg_childStub`/`seg_thrWorker` (dead in the closure) are
  not twinned.
- `thrJ`'s cells are `-16 .. -56` from the entry `%rsp` (`-8 .. -48(%rbp)`), `%rbp` and `%rsp` pinned; `wcJE`
  has the caller's `%rbp` and the return address in the entry cell `0` (AArch64: `x29`, `x30`).
-/
import Spike.Lib.X64HelloThr
import Spike.Lib.X64WakeChild

namespace Spike.Lib.X64.Flow.Worker.Hello.Child

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
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

/-- The call of the worker thread on the six words. -/
def chB : List (Directive × Nat) := (parse("movq %r12, %rdi
movq %rbx, %rsi
movq %r13, %rdx
movq %r14, %rcx
movq %r15, %r8
call scc_rt_thr_worker")).zip [3, 3, 3, 3, 3, 5]

block_spec jeB (-128) 0 oC jeB
block_spec chB (-128) 0 oC chB

/-- `wc_main`'s label after `scc_rt_thread_init`'s return (the spawn's block). -/
abbrev x25L : Label := ".Lwc_main.x3"

/-- The child's label. -/
abbrev chL : Label := ".Lwc_main.child.scc_rt_thr_worker"

/-- **The child's blocks and rows in `cells`**: the test and the `je` at
`.x25 + 96`, `+ 99`; `.child`'s row and call block. -/
def childIn (cells : List (Directive × Nat)) : Bool :=
  blockAt cells x25L 25 96 tsB && blockAt cells x25L 26 99 jeB && blockAt cells chL 0 0 xbp &&
    blockAt cells chL 1 2 chB

theorem hello_childIn : childIn SccCode.helloCells = true := by decide +kernel

/-! ## The nodes -/

/-- The worker's six words: the slice's four, the cell, the waiter. -/
structure Words where
  (w0 w1 w2 w3 w4 w5 : BitVec 64)

/-- **`scc_rt_thr_worker`'s entry**: the source at `c0` (the worker's
body), the six words in `%rdi .. %r9`, the thread pointer `tp`, `%rsp` at
`sp0`. -/
def thrJE (c0 : Ctl) (w : Words) (tp sp0 : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.regs.rdi.toBitVec = w.w0 ∧ σ.regs.rsi.toBitVec = w.w1 ∧ σ.regs.rdx.toBitVec = w.w2 ∧
    σ.regs.rcx.toBitVec = w.w3 ∧ σ.regs.r8.toBitVec = w.w4 ∧ σ.regs.r9.toBitVec = w.w5 ∧
    σ.regs.fsBase.toBitVec = tp ∧ σ.regs.rsp.toBitVec = sp0

/-- After `scc_rt_thr_worker`'s prologue: the six words in the frame's
cells `-16 .. -56` (`-8 .. -48(%rbp)`), the thread pointer, `%rbp` at the
saved `%rbp`, `%rsp` the frame's base. -/
def thrJ (c0 : Ctl) (w : Words) (tp sp0 : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.slot (-16) = w.w0 ∧ σ.slot (-24) = w.w1 ∧ σ.slot (-32) = w.w2 ∧ σ.slot (-40) = w.w3 ∧
    σ.slot (-48) = w.w4 ∧ σ.slot (-56) = w.w5 ∧ σ.regs.fsBase.toBitVec = tp ∧
    σ.regs.rbp.toBitVec = sp0 - 8#64 ∧ σ.regs.rsp.toBitVec = sp0 - 72#64

/-- **`wc_worker`'s entry**: the source at `c0`, the six words in
`%rdi .. %r9`, the caller's `%rbp` `rbp0`, the return address `ra` in the
entry cell `0`, the thread pointer `tp`. -/
def wcJE (c0 : Ctl) (w : Words) (rbp0 ra tp : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.regs.rdi.toBitVec = w.w0 ∧ σ.regs.rsi.toBitVec = w.w1 ∧ σ.regs.rdx.toBitVec = w.w2 ∧
    σ.regs.rcx.toBitVec = w.w3 ∧ σ.regs.r8.toBitVec = w.w4 ∧ σ.regs.r9.toBitVec = w.w5 ∧
    σ.regs.rbp.toBitVec = rbp0 ∧ σ.slot 0 = ra ∧ σ.regs.fsBase.toBitVec = tp

/-- The child's invariant: the source at `cW`, `%r12, %rbx, %r13, %r14,
%r15, %r9` the worker's six words, the thread pointer `tp`, `%rsp` at
`sp0`. -/
def childJ (cW : Ctl) (w : Words) (tp sp0 : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = cW ∧ σ.regs.get64 .r12 = w.w0 ∧ σ.regs.get64 .rbx = w.w1 ∧ σ.regs.get64 .r13 = w.w2 ∧
    σ.regs.get64 .r14 = w.w3 ∧ σ.regs.get64 .r15 = w.w4 ∧ σ.regs.get64 .r9 = w.w5 ∧
    σ.regs.fsBase.toBitVec = tp ∧ σ.regs.get64 .rsp = sp0

/-- **The child's node** past the clone's `syscall`, at the `testq`: `%rax = 0`. -/
def childN (lab : Label → Int64) (cW : Ctl) (w : Words) (tp sp0 : BitVec 64) : ND :=
  ⟨lab x25L + 96, oC, fun σ c => childJ cW w tp sp0 σ c ∧ σ.regs.get64 .rax = 0#64⟩

/-- The child's internal nodes. -/
inductive CN where
  | ts | je | xb | ch

/-- The child's nodes. -/
def cN (lab : Label → Int64) (cW : Ctl) (w : Words) (tp sp0 : BitVec 64) : CN → ND
  | .ts => childN lab cW w tp sp0
  | .je => ⟨lab x25L + 99, oC, fun σ c => childJ cW w tp sp0 σ c ∧ σ.status.zf = true⟩
  | .xb => ⟨lab chL, oC, childJ cW w tp sp0⟩
  | .ch => ⟨lab chL + 2, oC, fun σ c => childJ cW w tp sp0 σ c ∧ σ.regs.get64 .rbp = 0#64⟩

/-- **The exit**: `scc_rt_thr_worker`'s entry, `%rsp` at `-8` holding the
return address `.child + 22`, `%rdi .. %r9` the six words, `%rbp` zero. -/
def cE (lab : Label → Int64) (cW : Ctl) (w : Words) (tp sp0 : BitVec 64) : ND :=
  ⟨lab "scc_rt_thr_worker", ⟨-8, []⟩, fun σ c => c = cW ∧ σ.regs.get64 .rdi = w.w0 ∧
    σ.regs.get64 .rsi = w.w1 ∧ σ.regs.get64 .rdx = w.w2 ∧ σ.regs.get64 .rcx = w.w3 ∧
    σ.regs.get64 .r8 = w.w4 ∧ σ.regs.get64 .r9 = w.w5 ∧
    σ.regs.get64 .rbp = 0#64 ∧ σ.regs.fsBase.toBitVec = tp ∧ σ.regs.get64 .rsp = sp0 - 8#64 ∧
    σ.slot (-8) = (lab chL + 22).toBitVec⟩

/-! ## The segment -/

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **The child up to the worker thread is one segment** in any valid
layout of cells holding the blocks (`childIn`), from its node past the
clone (`childN`) to `scc_rt_thr_worker`'s entry (`cE`): the `je` taken
(`%rax = 0`), `%rbp` zeroed, the words moved to the argument registers. -/
theorem seg_child {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : childIn cells = true)
    {cW : Ctl} {w : Words} {tp sp0 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi) :
    Seg p lbl ms (At exe endPc R F (childN (_root_.Executable.labels exe).label cW w tp sp0))
      (At exe endPc R F (cE (_root_.Executable.labels exe).label cW w tp sp0)) := by
  simp only [childIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨bts, bje⟩, bxb⟩, bch⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have code : ∀ {l : Label} {k off : Nat} {b : List (Directive × Nat)}, blockAt cells l k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab l + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  refine (fn_seg (N := cN lab cW w tp sp0) (E := fun _ : Unit => cE lab cW w tp sp0) (fun i => ?_)
    CN.ts).mono_post fun _ _ ⟨_, h⟩ => h
  cases i
  case ts =>
    refine test_nd hF (fun s he hn => code bts s he hn) fun σ c hJ af => ⟨c, .refl c, .inl ⟨CN.je, ?_, rfl, ?_⟩⟩
    · show lab x25L + 99 = lab x25L + Int64.ofNat 96 + Int64.ofNat 3
      rw [Int64.add_assoc]; rfl
    · obtain ⟨hS, h0⟩ := hJ
      exact ⟨hS, by rw [testStep_zf, h0]; rfl⟩
  case je =>
    refine seg_nd (by simp [jeB]) jeB_ok hF hR hlo hhi (fun s he hn => code bje s he hn)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨CN.xb, ?_, rfl, hJ.1⟩⟩
    show lab chL = (arun lab jeB ⟨lab x25L + 99, oC, σ⟩).pc
    rw [jeB_run]; simp only [hJ.2, ite_true]
  case xb =>
    refine flag_nd (fi := .xor_rr32_self .rbp) rfl hF
      (fun s he hn => (by simpa using code bxb s he hn : CodeAt s (lab chL) xbp)) fun σ c hJ fl =>
        ⟨c, .refl c, .inl ⟨CN.ch, ?_, rfl, ?_, ?_⟩⟩
    · rfl
    · obtain ⟨h0, h12, hbx, h13, h14, h15, h9, htp, hsp⟩ := hJ
      refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp (disch := decide) only [FI.step, FI.regs, Reg64s.get64_set64_ne, h12, hbx, h13, h14, h15, h9, hsp]
      simpa [FI.step, FI.regs, Reg64s.set64] using htp
    · simp only [FI.step, FI.regs, Reg64s.get64_set64_self]; rfl
  case ch =>
    refine seg_nd (by simp [chB]) chB_ok hF hR hlo hhi (fun s he hn => code bch s he hn)
      fun σ c hJ => ⟨c, .refl c, .inr ⟨(), ?_, rfl, ?_⟩⟩
    · show lab "scc_rt_thr_worker" = (arun lab chB ⟨lab chL + 2, oC, σ⟩).pc
      rw [chB_run]
    · obtain ⟨⟨h0, h12, hbx, h13, h14, h15, h9, htp, hsp⟩, hbp⟩ := hJ
      show cE lab cW w tp sp0 |>.J (arun lab chB ⟨lab chL + 2, oC, σ⟩).σ c
      rw [chB_run]
      simp only [Reg64s.get64] at h12 hbx h13 h14 h15 h9 hbp hsp
      refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Reg64s.get64, Reg64s.set64, h12]
      · simp [Reg64s.get64, Reg64s.set64, hbx]
      · simp [Reg64s.get64, Reg64s.set64, h13]
      · simp [Reg64s.get64, Reg64s.set64, h14]
      · simp [Reg64s.get64, Reg64s.set64, h15]
      · simp [Reg64s.get64, Reg64s.set64, h9]
      · simp [Reg64s.get64, Reg64s.set64, hbp]
      · simpa [Reg64s.set64] using htp
      · simp [Reg64s.get64, Reg64s.set64, hsp]
      · simp only [upd_apply, ite_true]
        rw [Int64.toBitVec_add, BitVec.add_assoc]; rfl

end Seg

end Spike.Lib.X64.Flow.Worker.Hello.Child

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Child.seg_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Child.seg_child

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Child.hello_childIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Child.hello_childIn
