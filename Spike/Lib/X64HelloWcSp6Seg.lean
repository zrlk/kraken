/-
**hello.w's `wc_main` from `.x25` to its `clone`'s `syscall`, inside `W`**
(x86-64; the twin of `Spike/Lib/A64HelloWcSp6Seg.lean`), in any valid layout
of `helloCells`: the blocks, nodes and edges of `Spike/Lib/X64HelloWcSp6.lean`
composed with wake's rows,

    .x25:      sp6AH                    (sp6AH_edge)
    .x25+44:   mfence                   -- row: a fence (WcClone.mfence_ndW)
    .x25+47:   cloneLdH                 (cloneLdH_edge)
    .x25+84:   xorl %edx, %edx          -- row (flag_ndW)
    .x25+86:   xorl %r10d, %r10d        -- row (flag_ndW)
    .x25+89:   movl $56, %eax           (nrBH_edge)
    .x25+94:   syscall                  -- the exit `wcNSH`

wake's `X64WakeCloneSeg.wake_wc_clone_segW` at hello's frame (`oWH`, the
region's low end at most `-128`).

- `XS`, `sN`: the nodes from `.x25` to the `syscall`;
- `WcSp6W`: their states inside `W`, none moved by `K`; `WcSp6W.triv`;
- `hello_wc_sp6_segW`: the segment.

**Where this differs from AArch64**: the segment has six nodes before the
`syscall` (A64: three before the `svc`): the clone's arguments are a load
block, two `xorl` rows with undefined flags (`flag_ndW`, as in wake's
x86-64 clone) and the call number's block; the fence is `mfence`
(`WcClone.mfence_ndW`, A64's `dmb ish`). The edges are `Hit`s, so A64's
`hit_of_edgeH` is not needed. The region asks `R.lo ≤ -128` (the frame) and
`16 ≤ R.hi` (the saved `%rbp` and return address); A64 asks `-144`, `0` and
a 16-aligned base.
-/
import Spike.Lib.X64HelloWcSp6
import Spike.Lib.X64WakeCloneSeg
import Spike.Lib.X64Flags

namespace Spike.Lib.X64.HelloPh.WcSp6

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.WakePh.WcClone (fenceB xdx x10 nrB mfence_ndW)
open Scc.Cert.Rt.X64 (Lays endOf blockAt codeAt_blockAt_lays)
open SccCode (helloCells)

/-- `.x25`'s nodes before the `syscall`. -/
inductive XS where
  | n6 | n6f | n6a | nd | n10 | nr

/-- **The nodes from `.x25` to the `syscall`.** -/
def sN (lab : Label → Int64) (c0 : Ctl) (t k : BitVec 64) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
    (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64) : XS → ND
  | .n6 => wcN6H lab c0 t k sl me cA fr
  | .n6f => wcN6fH lab c0 t k sl me cA fr
  | .n6a => wcN6aH lab c0 t k sl me cA fr
  | .nd => wcNdH lab c0 t k sl me cA fr
  | .n10 => wcN10H lab c0 t k sl me cA fr
  | .nr => wcNrH lab c0 t k sl me cA fr

/-- **`.x25`'s states to the `syscall` inside `W`**, none moved by `K`. -/
structure WcSp6W (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (c0 : Ctl) (t k : BitVec 64)
    (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64) :
    Prop where
  n6 : BlkW W K exe endPc R F (wcN6H (_root_.Executable.labels exe).label c0 t k sl me cA fr) sp6AH
  n6f : NodeW W K exe endPc R F (wcN6fH (_root_.Executable.labels exe).label c0 t k sl me cA fr)
  n6a : BlkW W K exe endPc R F (wcN6aH (_root_.Executable.labels exe).label c0 t k sl me cA fr) cloneLdH
  nd : NodeW W K exe endPc R F (wcNdH (_root_.Executable.labels exe).label c0 t k sl me cA fr)
  n10 : NodeW W K exe endPc R F (wcN10H (_root_.Executable.labels exe).label c0 t k sl me cA fr)
  nr : BlkW W K exe endPc R F (wcNrH (_root_.Executable.labels exe).label c0 t k sl me cA fr) nrB

/-- From `.x25` to the `syscall` inside the trivial predicate, with no outside moves. -/
theorem WcSp6W.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} :
    WcSp6W (fun _ _ => True) (fun _ _ => False) exe endPc R F c0 t k sl me cA fr :=
  ⟨BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, NodeW.triv, BlkW.triv⟩

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from `.x25` to its `clone`'s `syscall` is one segment inside
`W`** in any valid layout of `helloCells`: from `wcN6H` (the child's stack
top `k` in `%rax`, the TCB `t` at `-64`, the frame's words, the source at
`c0`) to `wcNSH` (`clone(855808, k, 0, 0, t)`, the worker's six words in
`%r12, %rbx, %r13, %r14, %r15, %r9`), the source stuttering at the fence.
The frame condition `F` is stable in `R` (`hF`), `R`'s low end at most
`-128`. Its states lie in `W` (`hW`). -/
theorem hello_wc_sp6_segW {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 16 ≤ R.hi)
    {c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} (hW : WcSp6W W K exe endPc R F c0 t k sl me cA fr) :
    SegW W K p lbl ms (At exe endPc R F (wcN6H (_root_.Executable.labels exe).label c0 t k sl me cA fr))
      (At exe endPc R F (wcNSH (_root_.Executable.labels exe).label c0 t k sl me cA fr)) := by
  have hin := hello_wcSp6InH
  simp only [wcSp6InH, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨b0, bf⟩, bl⟩, bd⟩, b10⟩, br⟩, -⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have code : ∀ {k off : Nat} {b : List (Directive × Nat)}, blockAt helloCells x25L k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab x25L + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  have hB : SegW W K p lbl ms (At exe endPc R F (sN lab c0 t k sl me cA fr .n6))
      (fun s c => ∃ x : Unit, At exe endPc R F ((fun _ => wcNSH lab c0 t k sl me cA fr) x) s c) := by
    refine fn_segW (N := sN lab c0 t k sl me cA fr) (fun i => ?_) XS.n6
    cases i
    case n6 =>
      refine seg_ndW (by simp [sp6AH]) sp6AH_ok hF hR hlo hhi
        (fun s he hn => (by simpa using code b0 s he hn : CodeAt s (lab x25L) sp6AH)) hW.n6
        fun σ c hJ => ⟨c, .refl c, .inl ⟨XS.n6f, sp6AH_edge hJ⟩⟩
    case n6f =>
      refine mfence_ndW (fun s he hn => code bf s he hn) hW.n6f fun σ c hJ =>
        ⟨c, .loc (.refl c), .inl ⟨XS.n6a, ?_, rfl, hJ⟩⟩
      show lab x25L + 47 = lab x25L + Int64.ofNat 44 + Int64.ofNat 3
      rw [Int64.add_assoc]; rfl
    case n6a =>
      exact seg_ndW (by simp [cloneLdH]) cloneLdH_ok hF hR hlo hhi (fun s he hn => code bl s he hn) hW.n6a
        fun σ c hJ => ⟨c, .refl c, .inl ⟨XS.nd, cloneLdH_edge hJ⟩⟩
    case nd =>
      refine flag_ndW (fi := .xor_rr32_self .rdx) rfl hF (fun s he hn => code bd s he hn) hW.nd
        fun σ c hJ fl => ⟨c, .refl c, .inl ⟨XS.n10, ?_, rfl, ?_, ?_⟩⟩
      · show lab x25L + 86 = lab x25L + Int64.ofNat 84 + Int64.ofNat 2
        rw [Int64.add_assoc]; rfl
      · obtain ⟨hA, h12, hbx, h13, h14, h15, h9, hsi, h8, hdi⟩ := hJ
        exact ⟨hA, by
          simp (disch := decide) only [FI.step, FI.regs, Reg64s.get64_set64_ne, h12, hbx, h13, h14, h15, h9,
            hsi, h8, hdi, and_self]⟩
      · simp only [FI.step, FI.regs, Reg64s.get64_set64_self]; rfl
    case n10 =>
      refine flag_ndW (fi := .xor_rr32_self .r10) rfl hF (fun s he hn => code b10 s he hn) hW.n10
        fun σ c hJ fl => ⟨c, .refl c, .inl ⟨XS.nr, ?_, rfl, ?_, ?_, ?_⟩⟩
      · show lab x25L + 89 = lab x25L + Int64.ofNat 86 + Int64.ofNat 3
        rw [Int64.add_assoc]; rfl
      · obtain ⟨⟨hA, h12, hbx, h13, h14, h15, h9, hsi, h8, hdi⟩, -⟩ := hJ
        exact ⟨hA, by
          simp (disch := decide) only [FI.step, FI.regs, Reg64s.get64_set64_ne, h12, hbx, h13, h14, h15, h9,
            hsi, h8, hdi, and_self]⟩
      · simp (disch := decide) only [FI.step, FI.regs, Reg64s.get64_set64_ne, hJ.2]
      · simp only [FI.step, FI.regs, Reg64s.get64_set64_self]; rfl
    case nr =>
      exact seg_ndW (by simp [nrB]) nrBH_ok hF hR hlo hhi (fun s he hn => code br s he hn) hW.nr
        fun σ c hJ => ⟨c, .refl c, .inr ⟨(), nrBH_edge hJ⟩⟩
  exact hB.mono_post fun _ _ ⟨_, h⟩ => h

end Seg

/-- info: 'Spike.Lib.X64.HelloPh.WcSp6.hello_wc_sp6_segW' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello_wc_sp6_segW

end Spike.Lib.X64.HelloPh.WcSp6
