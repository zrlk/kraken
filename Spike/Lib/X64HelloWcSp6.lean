/-
**hello.w's `wc_main` from `.x25` to its `clone`'s `syscall`** (x86-64; the twin of
`Spike/Lib/A64HelloWcSp6.lean`), at the listing level, in `wc_main`'s frame of 128 (`oWH`: `%rsp` at `-128`,
`%rbp` at `0`, the saved `%rbp`):

    .Lwc_main.x3:                      -- %rax = the child's stack top k
      movq %rax, -72(%rbp)
      movq -16(%rbp), %rax; movq %rax, -80(%rbp)   … -24 → -88, -32 → -96, -48 → -104, -40 → -112   (sp6AH)
      mfence                            -- row: a fence (WcClone.mfence_ndW)
      movq -8(%rbp), %r12; movq -80(%rbp), %rbx; movq -88(%rbp), %r13; movq -96(%rbp), %r14
      movq -104(%rbp), %r15; movq -112(%rbp), %r9; movq -72(%rbp), %rsi; movq -64(%rbp), %r8
      movl $855808, %edi                                                                        (cloneLdH)
      xorl %edx, %edx; xorl %r10d, %r10d                                       -- rows (flag_ndW)
      movl $56, %eax                                                           (WcClone.nrB)
    .x25+94: syscall                    -- the clone (`wcNSH`)

wake.w's `X64WakeClone` (`.x21`) at hello's frame: the five spills of `wc_main`'s arguments at `-8 .. -40`
(the slice's four registers `sl` and main's word `me`), the cell at `-48`, the TCB at `-64`, the stack top at
`-72`, the packet `-80 .. -112`. At the `syscall`: `clone(855808, k, 0, 0, t)` in x86-64's argument order, the
worker's six words in `%r12, %rbx, %r13, %r14, %r15, %r9` (callee-saved but `%r9`; the `syscall` writes only
`%rax`, `%rcx`, `%r11`), as `X64HelloChild.childJ` reads them.

- `oWH`, `sp6AH`, `cloneLdH` (`block_spec`); `x25L`; `wcSp6InH`, `hello_wcSp6InH`: the blocks and wake's rows
  (`WcClone.fenceB`, `xdx`, `x10`, `nrB`, `svcB`) at `.x25`'s offsets in `helloCells`.
- `FrWH sl me cA fr`, `PktH sl me cA`: the frame's words; the packet.
- `wcN6H`, `wcN6fH`, `wcN6aH`, `wcNdH`, `wcN10H`, `wcNrH`, `wcNSH`: the nodes; `sp6AH_edge`, `cloneLdH_edge`,
  `nrBH_edge`: the blocks' edges.
- `wcNSH_call`: the `syscall` at `wcNSH` decodes to `clone k t`.

## Differences from the AArch64 version

- The frame is addressed from `%rbp` (`oWH = ⟨-128, [(.rbp, 0)]⟩`); `FrWH` has the caller's `%rbp` and return
  address at `0`/`8` (AArch64: `x29`/`x30` at `-16`/`-8`). The packet is copied word by word through `%rax`
  (AArch64: through `x9`), and the clone's arguments are x86-64's (`%rdi` flags, `%rsi` stack, `%rdx` ptid,
  `%r10` ctid, `%r8` TLS; AArch64's `x0 .. x4`); the worker's words are in callee-saved registers rather than
  `x9 .. x14`.
- The edges are `Hit`s (x86-64's `X64WakeClone` form); AArch64's `EdgeH` has no counterpart. The two `xorl`
  rows and the call number are their own nodes (`wcNdH`, `wcN10H`, `wcNrH`), as in wake's.
-/
import Spike.Lib.X64WakeClone
import Spike.Lib.X64HelloCode

namespace Spike.Lib.X64.HelloPh.WcSp6

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower
  Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.WakePh.WcClone (fenceB xdx x10 nrB svcB nrB_run)
open Scc.Cert.Rt.X64 (Lays endOf blockAt codeAt_blockAt_lays)
open SccCode (helloCells)

/-! ## The blocks -/

/-- `wc_main`'s offsets inside its frame of 128 (from `%rbp`). -/
abbrev oWH : SO := ⟨-128, [(.rbp, 0)]⟩

/-- `.x25`'s first block: the stack top to `-72`, the packet `-80 .. -112`. -/
def sp6AH : List (Directive × Nat) := (parse("movq %rax, -72(%rbp)
movq -16(%rbp), %rax
movq %rax, -80(%rbp)
movq -24(%rbp), %rax
movq %rax, -88(%rbp)
movq -32(%rbp), %rax
movq %rax, -96(%rbp)
movq -48(%rbp), %rax
movq %rax, -104(%rbp)
movq -40(%rbp), %rax
movq %rax, -112(%rbp)")).zip [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4]

/-- The clone's loads: the worker's six words, the stack top, the TCB, the flags. -/
def cloneLdH : List (Directive × Nat) := (parse("movq -8(%rbp), %r12
movq -80(%rbp), %rbx
movq -88(%rbp), %r13
movq -96(%rbp), %r14
movq -104(%rbp), %r15
movq -112(%rbp), %r9
movq -72(%rbp), %rsi
movq -64(%rbp), %r8
movl $855808, %edi")).zip [4, 4, 4, 4, 4, 4, 4, 4, 5]

block_spec sp6AH (-128) 16 oWH sp6AH
block_spec cloneLdH (-128) 16 oWH cloneLdH
block_spec nrBH (-128) 16 oWH nrB

/-- The label of `.x25`. -/
abbrev x25L : Label := ".Lwc_main.x3"

/-- **The blocks and rows in `cells`** at `.Lwc_main.x3`: indices `0`, `11`, `12`, `21`, `22`, `23`, `24`,
byte offsets `0`, `44`, `47`, `84`, `86`, `89`, `94`. -/
def wcSp6InH (cells : List (Directive × Nat)) : Bool :=
  blockAt cells x25L 0 0 sp6AH && blockAt cells x25L 11 44 fenceB && blockAt cells x25L 12 47 cloneLdH &&
    blockAt cells x25L 21 84 xdx && blockAt cells x25L 22 86 x10 && blockAt cells x25L 23 89 nrB &&
    blockAt cells x25L 24 94 svcB

theorem hello_wcSp6InH : wcSp6InH helloCells = true := by decide +kernel

/-! ## The nodes -/

/-- **The frame's words**: the spills of `wc_main`'s arguments, the slice's registers `sl` at `-8 .. -32` and
main's word `me` at `-40`; the cell `cA` at `-48`; the caller's frame pointer and return address `fr` the
prologue saved at `0`, `8`. -/
def FrWH (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64)
    (σ : AS) : Prop :=
  σ.slot (-8) = sl.1 ∧ σ.slot (-16) = sl.2.1 ∧ σ.slot (-24) = sl.2.2.1 ∧ σ.slot (-32) = sl.2.2.2 ∧
    σ.slot (-40) = me ∧ σ.slot (-48) = cA ∧ σ.slot 0 = fr.1 ∧ σ.slot 8 = fr.2

/-- **The packet** at `-80 .. -112`: `sl2`, `sl3`, `sl4`, the cell, main's word. -/
def PktH (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64) (σ : AS) : Prop :=
  σ.slot (-80) = sl.2.1 ∧ σ.slot (-88) = sl.2.2.1 ∧ σ.slot (-96) = sl.2.2.2 ∧ σ.slot (-104) = cA ∧
    σ.slot (-112) = me

section Nodes

variable (lab : Label → Int64) (c0 : Ctl) (t k : BitVec 64) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
  (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64)

/-- **At `.x25`** (back from `scc_rt_thread_init`): `%rax` the stack top `k`, the TCB `t` at `-64`, the
frame's words. -/
def wcN6H : ND := ⟨lab x25L, oWH, fun σ c => c = c0 ∧ σ.regs.get64 .rax = k ∧ σ.slot (-64) = t ∧
  FrWH sl me cA fr σ⟩

/-- The facts past `sp6AH`: `k` at `-72`, the TCB, the packet, the frame's words. -/
def JAH (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.slot (-72) = k ∧ σ.slot (-64) = t ∧ PktH sl me cA σ ∧ FrWH sl me cA fr σ

/-- At the fence. -/
def wcN6fH : ND := ⟨lab x25L + 44, oWH, JAH c0 t k sl me cA fr⟩

/-- Past the fence (the same facts). -/
def wcN6aH : ND := ⟨lab x25L + 47, oWH, JAH c0 t k sl me cA fr⟩

/-- The registers the loads set: the worker's six words in `%r12, %rbx, %r13, %r14, %r15, %r9`, `%rsi` the
stack top, `%r8` the TCB, `%rdi` the flags. -/
def JLH (σ : AS) (c : Ctl) : Prop := JAH c0 t k sl me cA fr σ c ∧ σ.regs.get64 .r12 = sl.1 ∧
  σ.regs.get64 .rbx = sl.2.1 ∧ σ.regs.get64 .r13 = sl.2.2.1 ∧ σ.regs.get64 .r14 = sl.2.2.2 ∧
  σ.regs.get64 .r15 = cA ∧ σ.regs.get64 .r9 = me ∧ σ.regs.get64 .rsi = k ∧ σ.regs.get64 .r8 = t ∧
  σ.regs.get64 .rdi = 855808#64

/-- At `xorl %edx, %edx`. -/
def wcNdH : ND := ⟨lab x25L + 84, oWH, JLH c0 t k sl me cA fr⟩

/-- At `xorl %r10d, %r10d`: `%rdx` zero. -/
def wcN10H : ND := ⟨lab x25L + 86, oWH, fun σ c => JLH c0 t k sl me cA fr σ c ∧ σ.regs.get64 .rdx = 0#64⟩

/-- At `movl $56, %eax`: `%rdx`, `%r10` zero. -/
def wcNrH : ND := ⟨lab x25L + 89, oWH, fun σ c =>
  JLH c0 t k sl me cA fr σ c ∧ σ.regs.get64 .rdx = 0#64 ∧ σ.regs.get64 .r10 = 0#64⟩

/-- **At the clone's `syscall`**: `clone(855808, k, 0, 0, t)` (`%rax` 56), the worker's six words; the
frame's words. -/
def wcNSH : ND := ⟨lab x25L + 94, oWH, fun σ c =>
  JLH c0 t k sl me cA fr σ c ∧ σ.regs.get64 .rdx = 0#64 ∧ σ.regs.get64 .r10 = 0#64 ∧ σ.regs.get64 .rax = 56#64⟩

end Nodes

/-! ## The edges -/

section Edges

variable {lab : Label → Int64} {c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
  {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} {σ : AS} {c : Ctl}

/-- `sp6AH` from `.x25` to the fence. -/
theorem sp6AH_edge (hJ : (wcN6H lab c0 t k sl me cA fr).J σ c) :
    Hit (wcN6fH lab c0 t k sl me cA fr) (arun lab sp6AH ⟨(wcN6H lab c0 t k sl me cA fr).pc, oWH, σ⟩) c := by
  obtain ⟨h0, hk, h64, h8, h16, h24, h32, h40, h48, hf1, hf2⟩ := hJ
  rw [sp6AH_run]
  refine ⟨rfl, rfl, h0, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [upd, Reg64s.get64] at hk ⊢; exact hk
  all_goals simp [upd, h64, h8, h16, h24, h32, h40, h48, hf1, hf2]

/-- `cloneLdH` from past the fence to `xorl %edx, %edx`. -/
theorem cloneLdH_edge (hJ : (wcN6aH lab c0 t k sl me cA fr).J σ c) :
    Hit (wcNdH lab c0 t k sl me cA fr) (arun lab cloneLdH ⟨(wcN6aH lab c0 t k sl me cA fr).pc, oWH, σ⟩) c := by
  obtain ⟨h0, h72, h64, ⟨p80, p88, p96, p104, p112⟩, ⟨h8, h16, h24, h32, h40, h48, hf1, hf2⟩⟩ := hJ
  rw [cloneLdH_run]
  refine ⟨by simp only [wcN6aH, wcNdH, Int64.add_assoc]; rfl, rfl,
    ⟨h0, h72, h64, ⟨p80, p88, p96, p104, p112⟩, ⟨h8, h16, h24, h32, h40, h48, hf1, hf2⟩⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := decide) only [Reg64s.get64_set64_self, Reg64s.get64_set64_ne, h8, p80, p88, p96, p104, p112,
      h72, h64]

/-- `nrB` from `movl $56, %eax` to the `syscall`. -/
theorem nrBH_edge (hJ : (wcNrH lab c0 t k sl me cA fr).J σ c) :
    Hit (wcNSH lab c0 t k sl me cA fr) (arun lab nrB ⟨(wcNrH lab c0 t k sl me cA fr).pc, oWH, σ⟩) c := by
  obtain ⟨⟨hA, h12, hbx, h13, h14, h15, h9, hsi, h8, hdi⟩, hdx, h10⟩ := hJ
  rw [nrBH_run]
  refine ⟨by simp only [wcNrH, wcNSH, Int64.add_assoc]; rfl, rfl,
    ⟨hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp (disch := decide) only [Reg64s.get64_set64_self, Reg64s.get64_set64_ne, h12, hbx, h13, h14, h15, h9,
      hsi, h8, hdi, hdx, h10]

end Edges

/-! ## The `syscall` -/

/-- **The `syscall` at `wcNSH` asks for `clone(k, t)`** (x86-64's order: the stack in `%rsi`, the TLS in
`%r8`, `ptid` in `%rdx`, `ctid` in `%r10`). -/
theorem wcNSH_call {lab : Label → Int64} {c0 : Ctl} {t k : BitVec 64}
    {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} {σ : AS}
    {c : Ctl} (hJ : (wcNSH lab c0 t k sl me cA fr).J σ c) :
    syscallCall σ.regs = some (.clone k.toNat t.toNat) := by
  obtain ⟨⟨-, -, -, -, -, -, -, hsi, h8, hdi⟩, hdx, h10, hax⟩ := hJ
  have e : ∀ {u : UInt64} {v : BitVec 64}, u.toBitVec = v → u.toNat = v.toNat := fun h => by rw [← h]; rfl
  have hax' := e hax; have hdi' := e hdi; have hdx' := e hdx; have h10' := e h10; have hsi' := e hsi
  have h8' := e h8
  simp [syscallCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.x64, Scc.Sem.Kernel.cloneFlags, hax', hdi', hdx',
    hsi']
  exact ⟨h10', h8'⟩

/-- info: 'Spike.Lib.X64.HelloPh.WcSp6.hello_wcSp6InH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hello_wcSp6InH

/-- info: 'Spike.Lib.X64.HelloPh.WcSp6.sp6AH_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sp6AH_edge

/-- info: 'Spike.Lib.X64.HelloPh.WcSp6.cloneLdH_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cloneLdH_edge

/-- info: 'Spike.Lib.X64.HelloPh.WcSp6.nrBH_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nrBH_edge

/-- info: 'Spike.Lib.X64.HelloPh.WcSp6.wcNSH_call' depends on axioms: [propext] -/
#guard_msgs in #print axioms wcNSH_call

end Spike.Lib.X64.HelloPh.WcSp6
