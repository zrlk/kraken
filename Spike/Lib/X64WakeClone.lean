/-
**wake.w's `wc_main` from `.x21` to its `clone`'s `syscall`** (x86-64, the
twin of `Spike/Lib/A64WakeWcSp4.lean`'s `.sp6` half and
`A64WakeWcSp4Seg.wake_wc_sp4_call_segW`'s tail), at the listing level, in
`wc_main`'s frame (`oW`: `%rsp` at `-64`, `%rbp` at `0`):

    .Lwc_main.x3:                      -- %rax = the child's stack top k
      movq %rax, -40(%rbp); movq -8(%rbp), %rax; movq %rax, -48(%rbp)  (x21A)
      mfence                            -- row: a fence (mfence_ndW)
      movq -16(%rbp), %r12; movq -48(%rbp), %rbx; movq -40(%rbp), %rsi
      movq -32(%rbp), %r8; movl $855808, %edi                          (cloneLd)
      xorl %edx, %edx                   -- row: flags (flag_ndW)
      xorl %r10d, %r10d                 -- row: flags (flag_ndW)
      movl $56, %eax                                                   (nrB)
      syscall                           -- the exit `wcNS`

At the `syscall`: `clone(855808, k, 0, 0, t)` in x86-64's argument order
(`rdi`, `rsi`, `rdx`, `r10`, `r8`: flags, stack, ptid, ctid, tls;
`Scc.Sem.Kernel.Nrs.x64`), the worker's two arguments in the callee-saved
`%r12` (the cell `cA`) and `%rbx` (main's word `m`), which the `syscall`
keeps (it writes `%rax`, `%rcx`, `%r11` only: `Scc.Sem.X64.retRegs64`).
The frame's words: `-8` main's argument (`m`), `-16` the cell, `-24` the
reserve's id, `-32` the TCB `t`, `-40` the stack top `k`, `-48` main's word
again; the caller's `%rbp` and return address at `0` and `8` (`fr`).

- `x21A`, `cloneLd`, `nrB` (`block_spec`); `fenceB`, `xdx`, `x10`: the rows;
  `wcCloneIn`: the blocks and rows at `.Lwc_main.x3`'s offsets (checked
  against wake's cells: `SccCode.wakeCells`).
- `FrW cA m t fr`: the frame's words; `wcN21`, `wcNf`, `wcNa`, `wcNd`,
  `wcN10`, `wcNr`, `wcNS`: the nodes; `x21A_edge`, `cloneLd_edge`,
  `nrB_edge`: the blocks' edges.
- `mfence_ndW`: a node at `mfence` (`Out.fence .sy`).
- `wcNS_call`: the `syscall` at `wcNS` decodes to `clone k t`.

The segment from `.x21` to the `syscall` is `X64WakeCloneSeg.lean`'s
`wake_wc_clone_segW`.
-/
import Spike.Lib.X64WakeTest
import Spike.Lib.X64Nodes
import Scc.Cert.Rt.LaysX64

namespace Spike.Lib.X64.WakePh.WcClone

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower
  Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAt codeAt_blockAt_lays)

/-! ## The blocks -/

/-- `wc_main`'s offsets inside its frame. -/
abbrev oW : SO := ⟨-64, [(.rbp, 0)]⟩

/-- `.x21`'s first block: the stack top to `-40`, main's word to `-48`. -/
def x21A : List (Directive × Nat) := (parse("movq %rax, -40(%rbp)
movq -8(%rbp), %rax
movq %rax, -48(%rbp)")).zip [4, 4, 4]

/-- The fence (a row). -/
def fenceB : List (Directive × Nat) := [(op64 .mfence, 3)]

/-- The clone's loads: the worker's arguments, the stack top, the TCB, the flags. -/
def cloneLd : List (Directive × Nat) := (parse("movq -16(%rbp), %r12
movq -48(%rbp), %rbx
movq -40(%rbp), %rsi
movq -32(%rbp), %r8
movl $855808, %edi")).zip [4, 4, 4, 4, 5]

/-- `xorl %edx, %edx` (a row). -/
def xdx : List (Directive × Nat) := [(FI.toDir (.xor_rr32_self .rdx), 2)]

/-- `xorl %r10d, %r10d` (a row). -/
def x10 : List (Directive × Nat) := [(FI.toDir (.xor_rr32_self .r10), 3)]

/-- The call number. -/
def nrB : List (Directive × Nat) := (parse("movl $56, %eax")).zip [5]

/-- The `syscall`. -/
def svcB : List (Directive × Nat) := [(op64 .syscall, 2)]

/-- The rows are what Kraken's parser makes of scc's text. -/
example : (parse("mfence
xorl %edx, %edx
xorl %r10d, %r10d
syscall")).zip [3, 2, 3, 2] = fenceB ++ xdx ++ x10 ++ svcB := by decide

block_spec x21A (-64) 16 oW x21A
block_spec cloneLd (-64) 16 oW cloneLd
block_spec nrB (-64) 16 oW nrB

/-- The label of `.x21`. -/
abbrev x21L : Label := ".Lwc_main.x3"

/-- **The blocks and rows in `cells`** at `.Lwc_main.x3`: indices `0`,
`3`, `4`, `9`, `10`, `11`, `12`, byte offsets `0`, `12`, `15`, `36`, `38`,
`41`, `46`. -/
def wcCloneIn (cells : List (Directive × Nat)) : Bool :=
  blockAt cells x21L 0 0 x21A && blockAt cells x21L 3 12 fenceB && blockAt cells x21L 4 15 cloneLd &&
    blockAt cells x21L 9 36 xdx && blockAt cells x21L 10 38 x10 && blockAt cells x21L 11 41 nrB &&
    blockAt cells x21L 12 46 svcB

/-! ## The nodes -/

/-- **The frame's words** the clone reads: the cell `cA` at `-16`, the TCB
`t` at `-32`, main's word `m` at `-8`; and the caller's frame pointer and
return address `fr` the prologue saved at `0`, `8`. -/
def FrW (cA m t : BitVec 64) (fr : BitVec 64 × BitVec 64) (σ : AS) : Prop :=
  σ.slot (-16) = cA ∧ σ.slot (-8) = m ∧ σ.slot (-32) = t ∧ σ.slot 0 = fr.1 ∧ σ.slot 8 = fr.2

section Nodes

variable (lab : Label → Int64) (c0 : Ctl) (t k cA m : BitVec 64) (fr : BitVec 64 × BitVec 64)

/-- At `.x21`: `%rax` the stack top `k`. -/
def wcN21 : ND := ⟨lab x21L, oW, fun σ c => c = c0 ∧ σ.regs.get64 .rax = k ∧ FrW cA m t fr σ⟩

/-- The facts past `x21A`: `k` at `-40`, main's word at `-48`. -/
def JA (σ : AS) (c : Ctl) : Prop := c = c0 ∧ σ.slot (-40) = k ∧ σ.slot (-48) = m ∧ FrW cA m t fr σ

/-- At the fence. -/
def wcNf : ND := ⟨lab x21L + 12, oW, JA c0 t k cA m fr⟩

/-- Past the fence. -/
def wcNa : ND := ⟨lab x21L + 15, oW, JA c0 t k cA m fr⟩

/-- The registers the loads set: `%r12` the cell, `%rbx` main's word,
`%rsi` the stack top, `%r8` the TCB, `%rdi` the flags. -/
def JL (σ : AS) (c : Ctl) : Prop := JA c0 t k cA m fr σ c ∧ σ.regs.get64 .r12 = cA ∧ σ.regs.get64 .rbx = m ∧
  σ.regs.get64 .rsi = k ∧ σ.regs.get64 .r8 = t ∧ σ.regs.get64 .rdi = 855808#64

/-- At `xorl %edx, %edx`. -/
def wcNd : ND := ⟨lab x21L + 36, oW, JL c0 t k cA m fr⟩

/-- At `xorl %r10d, %r10d`: `%rdx` zero. -/
def wcN10 : ND := ⟨lab x21L + 38, oW, fun σ c => JL c0 t k cA m fr σ c ∧ σ.regs.get64 .rdx = 0#64⟩

/-- At `movl $56, %eax`: `%rdx`, `%r10` zero. -/
def wcNr : ND := ⟨lab x21L + 41, oW, fun σ c =>
  JL c0 t k cA m fr σ c ∧ σ.regs.get64 .rdx = 0#64 ∧ σ.regs.get64 .r10 = 0#64⟩

/-- **At the clone's `syscall`**: `clone(855808, k, 0, 0, t)` (`%rax` 56),
`%r12` the cell, `%rbx` main's word; the frame's words. -/
def wcNS : ND := ⟨lab x21L + 46, oW, fun σ c =>
  JL c0 t k cA m fr σ c ∧ σ.regs.get64 .rdx = 0#64 ∧ σ.regs.get64 .r10 = 0#64 ∧ σ.regs.get64 .rax = 56#64⟩

end Nodes

/-! ## The edges -/

section Edges

variable {lab : Label → Int64} {c0 : Ctl} {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} {σ : AS} {c : Ctl}

/-- `x21A` from `.x21` to the fence. -/
theorem x21A_edge (hJ : (wcN21 lab c0 t k cA m fr).J σ c) :
    Hit (wcNf lab c0 t k cA m fr) (arun lab x21A ⟨(wcN21 lab c0 t k cA m fr).pc, oW, σ⟩) c := by
  obtain ⟨h0, hk, h16, h8, h32, hf1, hf2⟩ := hJ
  rw [x21A_run]
  refine ⟨rfl, rfl, h0, ?_, ?_, ?_⟩
  · simp [upd, Reg64s.get64] at hk ⊢; exact hk
  · simp [upd, h8]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [upd, h16, h8, h32, hf1, hf2]

/-- `cloneLd` from past the fence to `xorl %edx, %edx`. -/
theorem cloneLd_edge (hJ : (wcNa lab c0 t k cA m fr).J σ c) :
    Hit (wcNd lab c0 t k cA m fr) (arun lab cloneLd ⟨(wcNa lab c0 t k cA m fr).pc, oW, σ⟩) c := by
  obtain ⟨h0, h40, h48, h16, h8, h32, hf1, hf2⟩ := hJ
  rw [cloneLd_run]
  refine ⟨by simp only [wcNa, wcNd, Int64.add_assoc]; rfl, rfl,
    ⟨h0, h40, h48, h16, h8, h32, hf1, hf2⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := decide) only [Reg64s.get64_set64_self, Reg64s.get64_set64_ne, h16, h48, h40, h32]

/-- `nrB` from `movl $56, %eax` to the `syscall`. -/
theorem nrB_edge (hJ : (wcNr lab c0 t k cA m fr).J σ c) :
    Hit (wcNS lab c0 t k cA m fr) (arun lab nrB ⟨(wcNr lab c0 t k cA m fr).pc, oW, σ⟩) c := by
  obtain ⟨⟨hA, h12, hbx, hsi, h8, hdi⟩, hdx, h10⟩ := hJ
  rw [nrB_run]
  refine ⟨by simp only [wcNr, wcNS, Int64.add_assoc]; rfl, rfl, ⟨hA, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp (disch := decide) only [Reg64s.get64_set64_self, Reg64s.get64_set64_ne, h12, hbx, hsi, h8, hdi, hdx,
      h10]

end Edges

/-! ## The `syscall` -/

/-- **The `syscall` at `wcNS` asks for `clone(k, t)`** (x86-64's order: the
stack in `%rsi`, the TLS in `%r8`, `ptid` in `%rdx`, `ctid` in `%r10`). -/
theorem wcNS_call {lab : Label → Int64} {c0 : Ctl} {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} {σ : AS}
    {c : Ctl} (hJ : (wcNS lab c0 t k cA m fr).J σ c) :
    syscallCall σ.regs = some (.clone k.toNat t.toNat) := by
  obtain ⟨⟨-, -, -, hsi, h8, hdi⟩, hdx, h10, hax⟩ := hJ
  have e : ∀ {u : UInt64} {v : BitVec 64}, u.toBitVec = v → u.toNat = v.toNat := fun h => by rw [← h]; rfl
  have hax' := e hax; have hdi' := e hdi; have hdx' := e hdx; have h10' := e h10; have hsi' := e hsi
  have h8' := e h8
  simp [syscallCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.x64, Scc.Sem.Kernel.cloneFlags, hax', hdi', hdx',
    hsi']
  exact ⟨h10', h8'⟩

/-! ## A node at `mfence` -/

section Fence

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A node at `mfence`** inside `W` (`Out.fence .sy`): the abstract state
unchanged, the source's run at the fence (`FenceRun` under `ms.pub`),
landing at `pc + 3`. Its states lie in `W`, none moved by `K` (`hW`). The
twin of `A64WakeWcRes.dmb_ndW`. -/
theorem mfence_ndW {W : Frag isa} {K : State → State → Prop} {n : ND}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc fenceB)
    (hW : NodeW W K exe endPc R F n)
    (hedge : ∀ σ c, n.J σ c → ∃ c', FenceRun p ms.pub .sy c c' ∧ Lands N E ⟨n.pc + Int64.ofNat 3, n.o, σ⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (op64 .mfence) 3 := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨c', hr, hL⟩ := hedge σ c hJ
  refine .fence .sy _ c' (exec_mfence hc) hr ?_
  have hs1 : after s 3 s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat 3) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA hD⟩
  · exact .inr ⟨y, hy.at he hn hdc hA hD⟩

end Fence

/-- info: 'Spike.Lib.X64.WakePh.WcClone.wcNS_call' depends on axioms: [propext] -/
#guard_msgs in #print axioms wcNS_call

/-- info: 'Spike.Lib.X64.WakePh.WcClone.mfence_ndW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mfence_ndW

/-- info: 'Spike.Lib.X64.WakePh.WcClone.x21A_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms x21A_edge

/-- info: 'Spike.Lib.X64.WakePh.WcClone.cloneLd_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cloneLd_edge

/-- info: 'Spike.Lib.X64.WakePh.WcClone.nrB_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nrB_edge

end Spike.Lib.X64.WakePh.WcClone
