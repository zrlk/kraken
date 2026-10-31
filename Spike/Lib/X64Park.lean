/-
**`scc_rt_park` on x64 as one segment**: the x64 twin of
`Spike/Lib/A64Park.lean`. `wake.w`'s listing of the park routine (the lines
from `scc_rt_park:` to `.size scc_rt_park` in `SccCode.wakeAsm`), composed
from its blocks over its control-flow graph (`Spike/Lib/X64Cfg.lean`), as
`scc_rt_print` is in `Spike/Lib/X64Print.lean`.

    scc_rt_park():
      prologue (push %rbp, frame of 48 bytes below it)
      entry: tp = %fs:0 (spilled at -8(%rbp))
             old = xchg(0, [tp + 16])             -- take the permit
             if old = 1 goto done
      wait:  futex(tp + 16, FUTEX_WAIT_PRIVATE, 0, 0)   -- syscall, %eax = 202
             xchg(0, [tp + 16])                   -- consume a permit
             epilogue; ret
      done:  epilogue; ret

The region is the function's frame, offsets from the `%rsp` at entry (the
return address at `0`, the saved `%rbp` at `-8`, the frame down to `-56`):
`[-56, 8)`, `Spike/Lib/X64WakeFrame.lean`'s `parkD`. Ghost parameters: the
source control `c0` (runtime code: the source stutters throughout), the
caller's `%rbp` `rbp0`, the return address `ra` and the thread pointer `tp`
(`fsBase`, kept by every instruction here). The specification:

- **entry** (`.e`): pc at `scc_rt_park`, `%rsp` at offset 0, `%rbp = rbp0`,
  the return address `ra` at offset 0, `fsBase = tp`;
- **return** (exit `.ret`): pc at `ra`, `%rsp` at offset 8 (the return
  address popped), `%rbp` and `fsBase` as at entry, the memory outside the
  frame unchanged.

Unlike AArch64's `mrs x9, tpidr_el0`, x64 reads the thread pointer from
memory: `movq %fs:0, %rax` loads the TCB's self pointer, a runtime word
(`ownFsld_nd`). It is mapped for the load (`hT`, `LdOk`), and the thread
owns it with value `tp` at the load (`hown`, `OwnAt`). The permit word at
`tp + 16` is the runtime's but not owned by the thread (the unparking
thread exchanges it too): both exchanges are `Out.rtRmw` rows for **any**
old value (`rtXchg_nd`), with the memory-side facts of the word for the new
value `0` a hypothesis (`hS`, `StOk`). The futex wait is a `syscall_nd` node
under the kernel model (`hK`); its address must be 4-aligned (`htp4`). The
layout facts are hypotheses: each block is at its node's pc (`Code`), and
the prologue falls through to `.Lscc_rt_park.entry` (`hentry`).
-/
import Spike.Lib.X64Ret0
import Spike.Lib.X64KeepTP
import Spike.Lib.X64OwnFs
import Kraken.X64.Parser

namespace Spike.Lib.X64.Flow.Park

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64

open Spike.Lib.X64.Flow.Ret0 (StOk LdOk)

set_option linter.unusedSimpArgs false

/-! ## A non-owned runtime word's exchange -/

section RtXchg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A node at a runtime word's `xchgq %r, k(%b)`, the word not owned by
the thread** (another thread may write it): the address `k(%b)` is `A`, the
new value (`%r`'s) is one runtime memory may hold there (`StOk`), and for
**every** old value `v` the state after it (`%r := v`) lands at a node; the
source stutters. The owned variant is `ownXchg_ndW`
(`Spike/Lib/X64RtNodes.lean`). Inside `W`, not moved by `K` (`hW`). -/
theorem rtXchg_ndW {W : Frag isa} {K : State → State → Prop} {n : ND} {b r : Reg64} {k : Int64} {z : Nat}
    {A : BitVec 64} (hr : r ≠ .rsp) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(xchgDir b k r, z)])
    (hW : NodeW W K exe endPc R F n)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = A ∧ StOk ms F A (σ.regs.get64 r) ∧
      ∀ v : BitVec 64, Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, ownStep r v σ⟩ c) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (xchgDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨ha, hS, hL⟩ := hedge _ σ c hA hD hJ
  have ha' : eaddr s z (mB b k) = A := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha)
  have hex := exec_xchgG_agrees (w := .W64) hc ha' (hS.unmapped _ hD) (agrees_of_decls hdc _ _)
  rw [Reg64s.get_low64] at hex
  refine .rtRmw .acqRel _ _ _ c hex hS.rt hS.mp (.refl c) fun old _ _ => ?_
  refine ⟨fun new hnew => ?_, ?_⟩
  · simp only [Option.some.injEq] at hnew
    subst hnew
    rw [hA.regs]; exact hS.G
  · exact land_own (flm := s.st.1.status) (fla := σ.status) hA.status hr hF he hn hdc hpc hA hD (hL _)

/-- **A node at a non-owned runtime word's `xchgq`** (`rtXchg_ndW` inside
the trivial predicate, with no outside moves). -/
theorem rtXchg_nd {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {A : BitVec 64} (hr : r ≠ .rsp)
    (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(xchgDir b k r, z)])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      bAddr σ.regs b k = A ∧ StOk ms F A (σ.regs.get64 r) ∧
      ∀ v : BitVec 64, Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill r, ownStep r v σ⟩ c) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (rtXchg_ndW hr hF hcode NodeW.triv hedge).toSeg

end RtXchg

/-- `xchgDir` is what Kraken's parser makes of scc's permit exchange. -/
theorem xchg_parse : parse("xchgq %rax, 16(%rcx)") = [xchgDir .rcx 16 .rax] := by decide

/-- `fsDir` is what Kraken's parser makes of scc's thread-pointer load. -/
theorem fs_parse : parse("movq %fs:0, %rax") = [fsDir .rax 0] := by decide

/-- **The futex wait the kernel model decodes**: `%rax = 202`, `%rsi =
FUTEX_WAIT_PRIVATE`, a 4-aligned address in `%rdi`, no timeout (`%r10 =
0`). -/
theorem syscallCall_futexWait {r : Reg64s} (ha : r.rax.toNat = 202) (h1 : r.rsi.toNat = 128)
    (h0 : r.rdi.toNat % 4 = 0) (h3 : r.r10.toNat = 0) : syscallCall r = some .futexWait := by
  simp [syscallCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.x64, Scc.Sem.Kernel.futexWaitPrivate, ha, h1, h0]
  exact h3

/-! ## The blocks (generated) -/

def b0 : List (Directive × Nat) := (parse("pushq %rbp
movq %rsp, %rbp
subq $48, %rsp")).zip [1, 3, 4]
def b1 : List (Directive × Nat) := (parse("movq %rax, -8(%rbp)
movq -8(%rbp), %rcx
movq $0, %rax")).zip [4, 4, 7]
def b2 : List (Directive × Nat) := (parse("movq %rax, -16(%rbp)
movq -16(%rbp), %rax
movq $1, %rcx
cmpq %rcx, %rax
je .Lscc_rt_park.done")).zip [4, 4, 7, 3, 2]
def b3 : List (Directive × Nat) := (parse("jmp .Lscc_rt_park.wait")).zip [2]
def b4 : List (Directive × Nat) := (parse("movq -8(%rbp), %rax
movq $16, %rcx
addq %rcx, %rax
movq %rax, -24(%rbp)
movq -24(%rbp), %rdi
movq $128, %rsi
movq $0, %rdx
movq $0, %r10
movq $0, %r8
movq $0, %r9
movl $202, %eax")).zip [4, 7, 3, 4, 4, 7, 7, 7, 7, 7, 5]
def b5 : List (Directive × Nat) := (parse("movq %rax, -32(%rbp)
movq -8(%rbp), %rcx
movq $0, %rax")).zip [4, 4, 7]
def b6 : List (Directive × Nat) := (parse("movq %rax, -40(%rbp)
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 3, 1, 1]
def b7 : List (Directive × Nat) := (parse("movq %rbp, %rsp
popq %rbp
ret")).zip [3, 1, 1]

/-- The function's offsets inside the frame: `%rsp` at the frame's base,
`%rbp` at the saved `%rbp`. -/
abbrev oI : SO := ⟨-56, [(.rbp, -8)]⟩
/-- The offsets at entry. -/
abbrev oE : SO := ⟨0, []⟩
/-- The offsets after the return. -/
abbrev oR : SO := ⟨8, []⟩

block_spec b0 (-56) 8 oE b0
block_spec b1 (-56) 8 oI b1
block_spec b2 (-56) 8 oI b2
block_spec b3 (-56) 8 oI b3
block_spec b4 (-56) 8 oI b4
block_spec b5 (-56) 8 oI b5
block_spec b6 (-56) 8 oI b6
block_spec b7 (-56) 8 oI b7

/-! ## The graph -/

/-- The internal nodes: one per block, the thread-pointer load, the two
exchanges and the system call. -/
inductive PN where
  | e | fsl | n1 | xchg1 | n2 | n3 | wait | sys | n5 | xchg2 | n6 | done

/-- The exits. -/
inductive PX where
  | ret

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (rbp0 ra tp : BitVec 64)

/-- Inside the frame: the source has not moved, the caller's `%rbp` and the
return address are in their cells, the thread pointer is `tp`. -/
def JI (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.slot (-8) = rbp0 ∧ σ.slot 0 = ra ∧ σ.regs.fsBase.toBitVec = tp

/-- After the thread pointer's spill: `JI`, and `tp` in the cell `-8(%rbp)`. -/
def JT (σ : AS) (c : Ctl) : Prop := JI c0 rbp0 ra tp σ c ∧ σ.slot (-16) = tp

/-- At an exchange: `%rcx` the TCB (the permit at `16(%rcx)`), `%rax` the
new value `0`. -/
def JS (σ : AS) (c : Ctl) : Prop :=
  JT c0 rbp0 ra tp σ c ∧ σ.regs.get64 .rcx = tp ∧ σ.regs.get64 .rax = 0#64

/-- At entry. -/
def JE (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.regs.rbp.toBitVec = rbp0 ∧ σ.slot 0 = ra ∧ σ.regs.fsBase.toBitVec = tp

/-- At the return. -/
def JR (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.regs.get64 .rbp = rbp0 ∧ σ.regs.fsBase.toBitVec = tp

/-- The pc of the futex wait's `syscall`. -/
abbrev pcSys : Int64 := lab ".Lscc_rt_park.wait" + 62

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab "scc_rt_park", oE, JE c0 rbp0 ra tp⟩
  | .fsl => ⟨lab ".Lscc_rt_park.entry", oI, JI c0 rbp0 ra tp⟩
  | .n1 => ⟨lab ".Lscc_rt_park.entry" + 9, oI, fun σ c => JI c0 rbp0 ra tp σ c ∧ σ.regs.get64 .rax = tp⟩
  | .xchg1 => ⟨lab ".Lscc_rt_park.entry" + 24, oI, JS c0 rbp0 ra tp⟩
  | .n2 => ⟨lab ".Lscc_rt_park.entry" + 28, oI, JT c0 rbp0 ra tp⟩
  | .n3 => ⟨lab ".Lscc_rt_park.entry" + 48, oI, JT c0 rbp0 ra tp⟩
  | .wait => ⟨lab ".Lscc_rt_park.wait", oI, JT c0 rbp0 ra tp⟩
  | .sys => ⟨pcSys lab, oI, fun σ c => JT c0 rbp0 ra tp σ c ∧ σ.regs.get64 .rdi = tp + 16#64 ∧
      σ.regs.get64 .rsi = 128#64 ∧ σ.regs.get64 .r10 = 0#64 ∧ σ.regs.get64 .rax = 202#64⟩
  | .n5 => ⟨lab ".Lscc_rt_park.wait" + 64, oI, JT c0 rbp0 ra tp⟩
  | .xchg2 => ⟨lab ".Lscc_rt_park.wait" + 79, oI, JS c0 rbp0 ra tp⟩
  | .n6 => ⟨lab ".Lscc_rt_park.wait" + 83, oI, JT c0 rbp0 ra tp⟩
  | .done => ⟨lab ".Lscc_rt_park.done", oI, JT c0 rbp0 ra tp⟩

/-- **The exit**: the return to `ra` with `%rsp` past the return address,
`%rbp` and the thread pointer as at entry. -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, oR, JR c0 rbp0 tp⟩

/-- **The code**: every block and single instruction at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .e).pc b0
  fsl : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .fsl).pc [(fsDir .rax 0, 9)]
  n1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .n1).pc b1
  xchg1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .xchg1).pc [(xchgDir .rcx 16 .rax, 4)]
  n2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .n2).pc b2
  n3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .n3).pc b3
  wait : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .wait).pc b4
  sys : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .sys).pc [(op64 .syscall, 2)]
  n5 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .n5).pc b5
  xchg2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .xchg2).pc [(xchgDir .rcx 16 .rax, 4)]
  n6 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .n6).pc b6
  done : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .done).pc b7

end Spec

/-! ## The proof -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {rbp0 ra tp : BitVec 64}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code; the edge is left. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_nd (by simp [$b:ident]) $ok hF hR hlo hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- Hitting node `j`. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;>
    simp_all [N, JI, JT, JS, JE, JR, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self,
      Reg64s.get64_set64_ne, KeepTP.set64_tp, fsStep, ownStep, syscallStep, syscallRegs]))

/-- Hitting exit `x`. -/
macro "exit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;>
    simp_all [N, E, JI, JT, JS, JE, JR, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self,
      Reg64s.get64_set64_ne, KeepTP.set64_tp]))

/-- **`scc_rt_park` is one segment** from its entry to its return: the
source stutters throughout, the thread pointer is read from the TCB's self
pointer, the permit word at `tp + 16` is exchanged with `0` (twice on the
waiting path) for any old value, and the futex wait returns `0`, `-EAGAIN`
or `-EINTR`. -/
theorem seg_park (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -56) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp)
    (hS : StOk ms F (tp + 16#64) 0#64) (htp4 : (tp + 16#64).toNat % 4 = 0)
    (hcode : Code c0 rbp0 ra tp exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 8) :
    Seg p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .e))
      (fun s c => ∃ x, At exe endPc R F (E c0 rbp0 ra tp x) s c) := by
  refine fn_seg (N := N _ c0 rbp0 ra tp) (E := E c0 rbp0 ra tp) (fun i => ?_) PN.e
  cases i
  case e => node b0 b0_ok e; rw [N, b0_run]; hit PN.fsl
  case fsl =>
    refine ownFsld_nd (by decide) hF (fun s he hn => hcode.fsl s he hn) hown fun m σ c _ hm hJ => ?_
    obtain ⟨hc0, h8, h0, hfs⟩ := hJ
    have ha : σ.regs.fsBase.toBitVec + (0 : Int64).toBitVec = tp := by rw [hfs]; exact BitVec.add_zero tp
    refine ⟨ha, hT.rt, hT.mp, hT.unmapped m hm, c, .refl c, ?_⟩
    hit PN.n1
  case n1 => node b1 b1_ok n1; rw [N, b1_run]; hit PN.xchg1
  case xchg1 =>
    refine rtXchg_nd (A := tp + 16#64) (by decide) hF (fun s he hn => hcode.xchg1 s he hn)
      fun m σ c _ _ hJ => ?_
    obtain ⟨hT', hc, ha⟩ := hJ
    refine ⟨by rw [bAddr, hc]; rfl, by rw [ha]; exact hS, fun v => ?_⟩
    hit PN.n2
  case n2 =>
    node b2 b2_ok n2; rw [N, b2_run]
    split
    · hit PN.done
    · hit PN.n3
  case n3 => node b3 b3_ok n3; rw [N, b3_run]; hit PN.wait
  case wait =>
    node b4 b4_ok wait; rw [N, b4_run]
    have hc : (16#64 : BitVec 64) + tp = tp + 16#64 := BitVec.add_comm _ _
    hit PN.sys
  case sys =>
    have hcall : ∀ σ c, (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .sys).J σ c →
        syscallCall σ.regs = some .futexWait := by
      rintro σ c ⟨-, h0, h1, h3, h8⟩
      refine syscallCall_futexWait ?_ ?_ ?_ ?_
      · have := congrArg BitVec.toNat h8; simpa [Reg64s.get64] using this
      · have := congrArg BitVec.toNat h1; simpa [Reg64s.get64] using this
      · have := congrArg BitVec.toNat h0; rw [← htp4, ← this]; simp [Reg64s.get64]
      · have := congrArg BitVec.toNat h3; simpa [Reg64s.get64] using this
    refine syscall_nd hK hF (fun s he hn => hcode.sys s he hn) (fun σ c hJ => ?_) ?_
    · refine ⟨.futexWait, hcall σ c hJ, nofun, fun v _ => ⟨c, .refl c, ?_⟩⟩
      obtain ⟨hT', -⟩ := hJ
      hit PN.n5
    · rintro s c σ call - hJ hc
      rw [hcall σ c hJ] at hc
      cases hc
      exact ⟨nofun, nofun, nofun, nofun⟩
  case n5 => node b5 b5_ok n5; rw [N, b5_run]; hit PN.xchg2
  case xchg2 =>
    refine rtXchg_nd (A := tp + 16#64) (by decide) hF (fun s he hn => hcode.xchg2 s he hn)
      fun m σ c _ _ hJ => ?_
    obtain ⟨hT', hc, ha⟩ := hJ
    refine ⟨by rw [bAddr, hc]; rfl, by rw [ha]; exact hS, fun v => ?_⟩
    hit PN.n6
  case n6 => node b6 b6_ok n6; rw [N, b6_run]; exit PX.ret
  case done => node b7 b7_ok done; rw [N, b7_run]; exit PX.ret

end Proof

end Spike.Lib.X64.Flow.Park
