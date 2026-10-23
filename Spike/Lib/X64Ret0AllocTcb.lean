/-
**`scc_rt_alloc_tcb` in `ret0.w` on x64, block by block**: the x64 twin of
`Spike/Lib/A64Ret0AllocTcb.lean`. The walks of the runtime's TCB allocator
along its one feasible path when `scc_rt_start` calls it with the header
`2307` and `k = 1`, the named entry and exit predicates of its segment
(S2), and the pcs of its writes outside the frame. The nodes at its single
instructions (the label addresses, the instructions with undefined flags,
the counter's `lock xadd`, the header's store) are the composition's; each
walk takes the facts they establish as hypotheses.

    scc_rt_alloc_tcb(h = %rdi, k = %rsi):       frame of 176 below %rbp
      .entry: if k ≥ 2^28 goto full                         (atChk: not taken)
      .len:   d = (k·(((h >> 8) & 16383) + m) + 1)·8,       (atL0 … atL6: d = 80)
              m = (h >> 22) & 16383                         (m = 0)
              old = lock xadd [scc_rt_pinned_next], d       (rmwPc)
              if old + d > 2^17 goto full                   (atBnd: not taken)
      .ok:    [pinned + old + 8·k·m] = h | k << 36          (hdrPc)
              %rax = pinned + old + 8·k·m + 8; ret          (atRet)

- **The specification**: `Pre g n0` at the entry (`%rsp`, `%rbp` and the
  return address the ghosts `g`, `%rdi = hdr0`, `%rsi = 1`) and
  `Post g n0 pinned` at `g.ra` (`%rax = pinned + n0 + 8`). The ghost `n0`
  is the own word `scc_rt_pinned_next` on entry; it holds `n0 + tcbLen`
  after `rmwPc`, so the add's old value is `n0`. The header
  `hdr0 ||| 1 << 36` is stored at `pinned + n0` at `hdrPc`.
- **The frame** (`Fr g ss`): `%rsp` at the frame's base, `%rbp` at the
  saved `%rbp`, and the cells `ss` the later blocks read (`s0` … `s5`),
  offsets from the entry's `%rsp`.
- **The walks** (`atPro_walk` … `atRet_walk`): each block's run from its
  frame to the next, with its pc, offsets and branch (`atChk` and `atBnd`
  fall through) and the registers the next single instruction reads.
- **The single instructions**: `fi_fr`/`si_fr` keep the frame, `fi_so`/
  `si_so` the offsets; `shr_rax`, `and_rax`, `imul_rax`, `shl_rax`,
  `or_rax` and `si_rax` give `%rax` after them.
- **The code** (`allocTcbIn`, `ret0_allocTcbIn`): every block and single
  instruction at its label and byte offset in `ret0Cells`, decided by the
  kernel.
-/
import Spike.Lib.X64CodeSegs
import Spike.Lib.X64Flags
import Spike.Lib.X64Ret0Code

namespace Spike.Lib.X64.Flow.Ret0.AllocTcb

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB)

set_option linter.unusedSimpArgs false

/-! ## The blocks -/

/-- The offsets in the frame: `%rsp` at the frame's base, `%rbp` at the saved `%rbp`. -/
abbrev oI : SO := ⟨-184, [(.rbp, -8)]⟩
/-- The offsets at entry. -/
abbrev oE : SO := ⟨0, []⟩
/-- The offsets after the return. -/
abbrev oR : SO := ⟨8, []⟩

/-- The prologue: a frame of 176, `h`/`k` at `-8`/`-16(%rbp)`. -/
def atPro : List (Directive × Nat) := (parse("pushq %rbp
movq %rsp, %rbp
subq $176, %rsp
movq %rdi, -8(%rbp)
movq %rsi, -16(%rbp)")).zip [1, 3, 7, 4, 4]

/-- `k ≥ 2^28` goes to the abort. -/
def atChk : List (Directive × Nat) := (parse("movq -16(%rbp), %rax
movq $268435456, %rcx
cmpq %rcx, %rax
jae .Lscc_rt_alloc_tcb.full")).zip [4, 7, 3, 6]

/-- On to `.len`. -/
def atJ1 : List (Directive × Nat) := (parse("jmp .Lscc_rt_alloc_tcb.len")).zip [2]

/-- `h >> 8`'s operands. -/
def atL0 : List (Directive × Nat) := (parse("movq -8(%rbp), %rax
movq $8, %rcx")).zip [4, 7]

/-- `(h >> 8) & 16383`'s operands. -/
def atL1 : List (Directive × Nat) := (parse("movq %rax, -24(%rbp)
movq -24(%rbp), %rax
movq $16383, %rcx")).zip [4, 4, 7]

/-- The length field saved; `h >> 22`'s operands. -/
def atL2 : List (Directive × Nat) := (parse("movq %rax, -32(%rbp)
movq -8(%rbp), %rax
movq $22, %rcx")).zip [4, 4, 7]

/-- `(h >> 22) & 16383`'s operands. -/
def atL3 : List (Directive × Nat) := (parse("movq %rax, -40(%rbp)
movq -40(%rbp), %rax
movq $16383, %rcx")).zip [4, 4, 7]

/-- `m` saved, `len + m`; `k·(len + m)`'s operands. -/
def atL4 : List (Directive × Nat) := (parse("movq %rax, -48(%rbp)
movq -32(%rbp), %rax
movq -48(%rbp), %rcx
addq %rcx, %rax
movq %rax, -56(%rbp)
movq -16(%rbp), %rax
movq -56(%rbp), %rcx")).zip [4, 4, 4, 3, 4, 4, 4]

/-- `k·(len + m) + 1`; the shift's operands. -/
def atL5 : List (Directive × Nat) := (parse("movq %rax, -64(%rbp)
movq -64(%rbp), %rax
movq $1, %rcx
addq %rcx, %rax
movq %rax, -72(%rbp)
movq -72(%rbp), %rax
movq $3, %rcx")).zip [4, 4, 7, 3, 4, 4, 7]

/-- `d` saved. -/
def atL6 : List (Directive × Nat) := (parse("movq %rax, -80(%rbp)")).zip [4]

/-- The add's operands: `%rcx` the counter's address, `%rax = d`. -/
def atArg : List (Directive × Nat) := (parse("movq %rax, -88(%rbp)
movq -88(%rbp), %rcx
movq -80(%rbp), %rax")).zip [4, 4, 4]

/-- The counter's old value saved; past the pinned area (`2^17` bytes) goes to the abort. -/
def atBnd : List (Directive × Nat) := (parse("movq %rax, -96(%rbp)
movq -96(%rbp), %rax
movq -80(%rbp), %rcx
addq %rcx, %rax
movq %rax, -104(%rbp)
movq -104(%rbp), %rax
movq $131072, %rcx
cmpq %rcx, %rax
ja .Lscc_rt_alloc_tcb.full")).zip [4, 4, 4, 3, 4, 4, 7, 3, 2]

/-- On to `.ok`. -/
def atJ2 : List (Directive × Nat) := (parse("jmp .Lscc_rt_alloc_tcb.ok")).zip [2]

/-- The header's address `pinned + old`; `k·m`'s operands. -/
def atO1 : List (Directive × Nat) := (parse("movq %rax, -112(%rbp)
movq -112(%rbp), %rax
movq -96(%rbp), %rcx
addq %rcx, %rax
movq %rax, -120(%rbp)
movq -16(%rbp), %rax
movq -48(%rbp), %rcx")).zip [4, 4, 4, 3, 4, 4, 4]

/-- `8·k·m`'s operands. -/
def atO2 : List (Directive × Nat) := (parse("movq %rax, -128(%rbp)
movq -128(%rbp), %rax
movq $3, %rcx")).zip [4, 4, 7]

/-- `8·k·m` saved; `k << 36`'s operands. -/
def atO3 : List (Directive × Nat) := (parse("movq %rax, -136(%rbp)
movq -16(%rbp), %rax
movq $36, %rcx")).zip [7, 4, 7]

/-- `h | k << 36`'s operands. -/
def atO4 : List (Directive × Nat) := (parse("movq %rax, -144(%rbp)
movq -8(%rbp), %rax
movq -144(%rbp), %rcx")).zip [7, 4, 7]

/-- The header and its address: `%rax` the header, `%rcx = pinned + old + 8·k·m`. -/
def atO5 : List (Directive × Nat) := (parse("movq %rax, -152(%rbp)
movq -120(%rbp), %rax
movq -136(%rbp), %rcx
addq %rcx, %rax
movq %rax, -160(%rbp)
movq -160(%rbp), %rcx
movq -152(%rbp), %rax")).zip [7, 4, 7, 3, 7, 7, 7]

/-- `%rax` one word past the header; the epilogue and the return. -/
def atRet : List (Directive × Nat) := (parse("movq -120(%rbp), %rax
movq -136(%rbp), %rcx
addq %rcx, %rax
movq %rax, -168(%rbp)
movq -168(%rbp), %rax
movq $8, %rcx
addq %rcx, %rax
movq %rax, -176(%rbp)
movq -176(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 7, 3, 7, 7, 7, 3, 7, 7, 3, 1, 1]

block_spec atPro (-184) 8 oE atPro
block_spec atChk (-184) 8 oI atChk
block_spec atJ1 (-184) 8 oI atJ1
block_spec atL0 (-184) 8 oI atL0
block_spec atL1 (-184) 8 oI atL1
block_spec atL2 (-184) 8 oI atL2
block_spec atL3 (-184) 8 oI atL3
block_spec atL4 (-184) 8 oI atL4
block_spec atL5 (-184) 8 oI atL5
block_spec atL6 (-184) 8 oI atL6
block_spec atArg (-184) 8 oI atArg
block_spec atBnd (-184) 8 oI atBnd
block_spec atJ2 (-184) 8 oI atJ2
block_spec atO1 (-184) 8 oI atO1
block_spec atO2 (-184) 8 oI atO2
block_spec atO3 (-184) 8 oI atO3
block_spec atO4 (-184) 8 oI atO4
block_spec atO5 (-184) 8 oI atO5
block_spec atRet (-184) 8 oI atRet

/-! ## The specification -/

/-- **The ghosts of a call**: `%rsp`, `%rbp` and the return address at entry. -/
structure G where
  /-- `%rsp` at entry. -/
  sp : BitVec 64
  /-- `%rbp` at entry. -/
  fp : BitVec 64
  /-- The return address (at `[%rsp]`). -/
  ra : BitVec 64

/-- The header `scc_rt_start` passes. -/
abbrev hdr0 : BitVec 64 := 2307#64

/-- The TCB's length in bytes the code computes for `hdr0` and `k = 1`. -/
abbrev tcbLen : BitVec 64 := 80#64

/-- **Entry**: `%rsp`, `%rbp`, the return address the ghosts', `%rdi = 2307`,
`%rsi = 1`. The own word `scc_rt_pinned_next` holds `n0` (the map's, not
the state's). -/
def Pre (g : G) (_n0 : BitVec 64) (σ : AS) : Prop :=
  σ.regs.rsp.toBitVec = g.sp ∧ σ.regs.rbp.toBitVec = g.fp ∧ σ.slot 0 = g.ra ∧
  σ.regs.rdi.toBitVec = hdr0 ∧ σ.regs.rsi.toBitVec = 1#64

/-- **Exit** (at `g.ra`): `%rsp` past the return address, `%rbp` restored,
`%rax` one word past the header at `pinned + n0`. `scc_rt_pinned_next`
holds `n0 + tcbLen`. -/
def Post (g : G) (n0 pinned : BitVec 64) (σ : AS) : Prop :=
  σ.regs.rsp.toBitVec = g.sp + 8#64 ∧ σ.regs.rbp.toBitVec = g.fp ∧ σ.regs.rax.toBitVec = pinned + n0 + 8#64

/-- **The frame**: `%rsp` at the frame's base, `%rbp` at the saved `%rbp`,
the cells `ss` (offsets from the entry's `%rsp`). -/
def Fr (g : G) (ss : List (Int × BitVec 64)) (σ : AS) : Prop :=
  σ.regs.rsp.toBitVec = g.sp - 184#64 ∧ σ.regs.rbp.toBitVec = g.sp - 8#64 ∧ ∀ p ∈ ss, σ.slot p.1 = p.2

/-- The return address, the saved `%rbp` and the arguments. -/
abbrev s0 (g : G) : List (Int × BitVec 64) := [(0, g.ra), (-8, g.fp), (-16, hdr0), (-24, 1#64)]
/-- With the length field `9`. -/
abbrev sA (g : G) : List (Int × BitVec 64) := (-40, 9#64) :: s0 g
/-- With `m = 0`. -/
abbrev s1 (g : G) : List (Int × BitVec 64) := (-56, 0#64) :: s0 g
/-- With `d = tcbLen`. -/
abbrev s2 (g : G) : List (Int × BitVec 64) := (-88, tcbLen) :: s1 g
/-- With the counter's old value `n0`. -/
abbrev s3 (g : G) (n0 : BitVec 64) : List (Int × BitVec 64) := (-104, n0) :: s1 g
/-- With the header's address `Q + n0`. -/
abbrev s4 (g : G) (n0 Q : BitVec 64) : List (Int × BitVec 64) := (-128, Q + n0) :: s3 g n0
/-- With `8·k·m = 0`. -/
abbrev s5 (g : G) (n0 Q : BitVec 64) : List (Int × BitVec 64) := (-144, 0#64) :: s4 g n0 Q

/-! ## The walks -/

/-- Unfolds a frame hypothesis. -/
local macro "frh" h:ident : tactic => `(tactic| simp only [Fr, List.forall_mem_cons, List.forall_mem_nil] at $h:ident)

/-- Closes a walk's goal from the run's normal form. -/
local macro "walk" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [Fr, Post, Reg64s.set64, Reg64s.get64, upd_apply, $ts,*])

/-- **The prologue**: from the entry to `.entry`, the frame set up. -/
theorem atPro_walk (lab : String → Int64) (pc : Int64) {g : G} {n0 : BitVec 64} {σ : AS} (h : Pre g n0 σ) :
    (arun lab atPro ⟨pc, oE, σ⟩).pc = pc + Int64.ofNat 19 ∧
    (arun lab atPro ⟨pc, oE, σ⟩).so = oI ∧ Fr g (s0 g) (arun lab atPro ⟨pc, oE, σ⟩).σ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [atPro_run]
  refine ⟨rfl, rfl, ?_⟩
  walk [h1, h2, h3, h4, h5]
  bv_omega

/-- **The size check is not taken** (`k = 1`). -/
theorem atChk_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} (h : Fr g (s0 g) σ) :
    (arun lab atChk ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 20 ∧
    (arun lab atChk ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s0 g) (arun lab atChk ⟨pc, oI, σ⟩).σ := by
  frh h
  rw [atChk_run]
  walk [h]

/-- On to `.len`. -/
theorem atJ1_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} (h : Fr g (s0 g) σ) :
    (arun lab atJ1 ⟨pc, oI, σ⟩).pc = lab ".Lscc_rt_alloc_tcb.len" ∧
    (arun lab atJ1 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s0 g) (arun lab atJ1 ⟨pc, oI, σ⟩).σ := by
  rw [atJ1_run]
  exact ⟨rfl, rfl, h⟩

/-- `h >> 8`'s operands. -/
theorem atL0_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} (h : Fr g (s0 g) σ) :
    (arun lab atL0 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 11 ∧
    (arun lab atL0 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s0 g) (arun lab atL0 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atL0 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = hdr0 ∧
    (arun lab atL0 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 8#64 := by
  frh h
  rw [atL0_run]
  walk [h]

/-- `(h >> 8) & 16383`'s operands (`h >> 8 = 9`). -/
theorem atL1_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} (h : Fr g (s0 g) σ)
    (ha : σ.regs.rax.toBitVec = 9#64) :
    (arun lab atL1 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 15 ∧
    (arun lab atL1 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s0 g) (arun lab atL1 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atL1 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = 9#64 ∧
    (arun lab atL1 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 16383#64 := by
  frh h
  rw [atL1_run]
  walk [h, ha]

/-- The length field `9` saved; `h >> 22`'s operands. -/
theorem atL2_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} (h : Fr g (s0 g) σ)
    (ha : σ.regs.rax.toBitVec = 9#64) :
    (arun lab atL2 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 15 ∧
    (arun lab atL2 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (sA g) (arun lab atL2 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atL2 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = hdr0 ∧
    (arun lab atL2 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 22#64 := by
  frh h
  rw [atL2_run]
  walk [h, ha]

/-- `(h >> 22) & 16383`'s operands (`h >> 22 = 0`). -/
theorem atL3_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} (h : Fr g (sA g) σ)
    (ha : σ.regs.rax.toBitVec = 0#64) :
    (arun lab atL3 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 15 ∧
    (arun lab atL3 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (sA g) (arun lab atL3 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atL3 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = 0#64 ∧
    (arun lab atL3 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 16383#64 := by
  frh h
  rw [atL3_run]
  walk [h, ha]

/-- `m = 0` saved; `k·(len + m)`'s operands. -/
theorem atL4_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} (h : Fr g (sA g) σ)
    (ha : σ.regs.rax.toBitVec = 0#64) :
    (arun lab atL4 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 27 ∧
    (arun lab atL4 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s1 g) (arun lab atL4 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atL4 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = 1#64 ∧
    (arun lab atL4 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 9#64 := by
  frh h
  rw [atL4_run]
  walk [h, ha]

/-- `k·(len + m) + 1 = 10`; the shift's operands. -/
theorem atL5_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} (h : Fr g (s1 g) σ)
    (ha : σ.regs.rax.toBitVec = 9#64) :
    (arun lab atL5 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 33 ∧
    (arun lab atL5 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s1 g) (arun lab atL5 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atL5 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = 10#64 ∧
    (arun lab atL5 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 3#64 := by
  frh h
  rw [atL5_run]
  walk [h, ha]

/-- **The length** `d = tcbLen` saved. -/
theorem atL6_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} (h : Fr g (s1 g) σ)
    (ha : σ.regs.rax.toBitVec = tcbLen) :
    (arun lab atL6 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 4 ∧
    (arun lab atL6 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s2 g) (arun lab atL6 ⟨pc, oI, σ⟩).σ := by
  frh h
  rw [atL6_run]
  walk [h, ha]

/-- **The add's operands**: `%rax = tcbLen`, `%rcx` the counter's address `P`
(in `%rax` before). -/
theorem atArg_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {P : BitVec 64} (h : Fr g (s2 g) σ)
    (hP : σ.regs.rax.toBitVec = P) :
    (arun lab atArg ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 12 ∧
    (arun lab atArg ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s2 g) (arun lab atArg ⟨pc, oI, σ⟩).σ ∧
    (arun lab atArg ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = tcbLen ∧
    (arun lab atArg ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = P := by
  frh h
  rw [atArg_run]
  walk [h, hP]

/-- **The bound is not crossed** when the counter's old value `n0` (in
`%rax`) has room for `tcbLen` more bytes below `2^17`. -/
theorem atBnd_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {n0 : BitVec 64} (h : Fr g (s2 g) σ)
    (ha : σ.regs.rax.toBitVec = n0) (hn : n0.toNat + 80 ≤ 131072) :
    (arun lab atBnd ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 35 ∧
    (arun lab atBnd ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s3 g n0) (arun lab atBnd ⟨pc, oI, σ⟩).σ := by
  frh h
  have hr : (σ.regs.rax.toNat : Int) = n0.toNat := by rw [← ha]; rfl
  rw [atBnd_run]
  walk [h, ha]
  intro h1 h2
  by_cases he : n0.toNat + 80 = 131072
  · refine absurd (BitVec.eq_of_toNat_eq ?_) h2
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Width.bits] at he ⊢
    omega
  · rw [hr] at h1; omega

/-- On to `.ok`. -/
theorem atJ2_walk (lab : String → Int64) (pc : Int64) {g : G} {n0 : BitVec 64} {σ : AS} (h : Fr g (s3 g n0) σ) :
    (arun lab atJ2 ⟨pc, oI, σ⟩).pc = lab ".Lscc_rt_alloc_tcb.ok" ∧
    (arun lab atJ2 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s3 g n0) (arun lab atJ2 ⟨pc, oI, σ⟩).σ := by
  rw [atJ2_run]
  exact ⟨rfl, rfl, h⟩

/-- **The header's address** `Q + n0` saved (`Q`, the pinned area's address,
in `%rax` before); `k·m`'s operands. -/
theorem atO1_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {n0 Q : BitVec 64} (h : Fr g (s3 g n0) σ)
    (hQ : σ.regs.rax.toBitVec = Q) :
    (arun lab atO1 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 27 ∧
    (arun lab atO1 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s4 g n0 Q) (arun lab atO1 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atO1 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = 1#64 ∧
    (arun lab atO1 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 0#64 := by
  frh h
  rw [atO1_run]
  walk [h, hQ]
  exact BitVec.add_comm _ _

/-- `8·k·m`'s operands (`k·m = 0`). -/
theorem atO2_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {n0 Q : BitVec 64} (h : Fr g (s4 g n0 Q) σ)
    (ha : σ.regs.rax.toBitVec = 0#64) :
    (arun lab atO2 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 15 ∧
    (arun lab atO2 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s4 g n0 Q) (arun lab atO2 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atO2 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = 0#64 ∧
    (arun lab atO2 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 3#64 := by
  frh h
  rw [atO2_run]
  walk [h, ha]

/-- `8·k·m = 0` saved; `k << 36`'s operands. -/
theorem atO3_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {n0 Q : BitVec 64} (h : Fr g (s4 g n0 Q) σ)
    (ha : σ.regs.rax.toBitVec = 0#64) :
    (arun lab atO3 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 18 ∧
    (arun lab atO3 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s5 g n0 Q) (arun lab atO3 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atO3 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = 1#64 ∧
    (arun lab atO3 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 36#64 := by
  frh h
  rw [atO3_run]
  walk [h, ha]

/-- `h | k << 36`'s operands. -/
theorem atO4_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {n0 Q : BitVec 64} (h : Fr g (s5 g n0 Q) σ)
    (ha : σ.regs.rax.toBitVec = 1#64 <<< 36) :
    (arun lab atO4 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 18 ∧
    (arun lab atO4 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s5 g n0 Q) (arun lab atO4 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atO4 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = hdr0 ∧
    (arun lab atO4 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 1#64 <<< 36 := by
  frh h
  rw [atO4_run]
  walk [h, ha]

/-- **The header and its address**: `%rax = hdr0 ||| 1 << 36`, `%rcx = Q + n0`. -/
theorem atO5_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {n0 Q : BitVec 64} (h : Fr g (s5 g n0 Q) σ)
    (ha : σ.regs.rax.toBitVec = hdr0 ||| 1#64 <<< 36) :
    (arun lab atO5 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 42 ∧
    (arun lab atO5 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s5 g n0 Q) (arun lab atO5 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atO5 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = hdr0 ||| 1#64 <<< 36 ∧
    (arun lab atO5 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = Q + n0 := by
  frh h
  rw [atO5_run]
  walk [h, ha]
  decide

/-- **The return**: to `g.ra` with `%rax = Q + n0 + 8`, the frame popped. -/
theorem atRet_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {n0 Q : BitVec 64}
    (h : Fr g (s5 g n0 Q) σ) :
    (arun lab atRet ⟨pc, oI, σ⟩).pc = Int64.ofBitVec g.ra ∧
    (arun lab atRet ⟨pc, oI, σ⟩).so = oR ∧ Post g n0 Q (arun lab atRet ⟨pc, oI, σ⟩).σ := by
  frh h
  rw [atRet_run]
  walk [h]
  exact BitVec.add_comm _ _

/-! ## The single instructions -/

/-- An instruction with undefined flags writing `%rax` keeps the frame. -/
theorem fi_fr {fi : FI} (hd : fi.dst = some .rax) {g : G} {ss : List (Int × BitVec 64)} {σ : AS}
    (h : Fr g ss σ) (fl : StatusFlags) : Fr g ss (fi.step σ fl) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, h3⟩
  · rw [← h1]; exact fi.regs_get64 σ.regs (x := .rsp) (by rw [hd]; decide)
  · rw [← h2]; exact fi.regs_get64 σ.regs (x := .rbp) (by rw [hd]; decide)

/-- It forgets `%rax` only. -/
theorem fi_so {fi : FI} (hd : fi.dst = some .rax) : fi.so oI = oI := by
  simp [FI.so, hd, SO.kill, rm]

/-- A label's address into `%rax` keeps the frame. -/
theorem si_fr (lab : Label → Int64) (L : Label) {g : G} {ss : List (Int × BitVec 64)} {σ : AS}
    (h : Fr g ss σ) : Fr g ss ((SI.leaRip .rax L).step lab σ) := h

/-- It forgets `%rax` only. -/
theorem si_so (L : Label) : (SI.leaRip .rax L).so oI = oI := by
  simp [SI.so, SI.dst, SO.kill, rm]

/-- `%rax` after a label's address. -/
theorem si_rax (lab : Label → Int64) (L : Label) (σ : AS) :
    ((SI.leaRip .rax L).step lab σ).regs.rax.toBitVec = (lab L).toBitVec := by
  simp [SI.step, SI.regs, Reg64s.set64]

section Vals

variable {σ : AS} {a c : BitVec 64} (ha : σ.regs.rax.toBitVec = a) (hc : σ.regs.rcx.toBitVec = c)
  (fl : StatusFlags)
include ha hc

/-- `%rax` after `shrq %cl, %rax`. -/
theorem shr_rax : ((FI.shr_cl .rax).step σ fl).regs.rax.toBitVec = a.ushiftRight ((c.take 8).toNat &&& 63) := by
  simp [FI.step, FI.regs, clOf, Reg64s.set64, Reg64s.get64, ha, hc]

/-- `%rax` after `shlq %cl, %rax`. -/
theorem shl_rax : ((FI.shl_cl .rax).step σ fl).regs.rax.toBitVec = a <<< ((c.take 8).toNat &&& 63) := by
  simp [FI.step, FI.regs, clOf, Reg64s.set64, Reg64s.get64, ha, hc]

/-- `%rax` after `andq %rcx, %rax`. -/
theorem and_rax : ((FI.and_rr .rax .rcx).step σ fl).regs.rax.toBitVec = a &&& c := by
  simp [FI.step, FI.regs, clOf, Reg64s.set64, Reg64s.get64, ha, hc]

/-- `%rax` after `orq %rcx, %rax`. -/
theorem or_rax : ((FI.or_rr .rax .rcx).step σ fl).regs.rax.toBitVec = a ||| c := by
  simp [FI.step, FI.regs, clOf, Reg64s.set64, Reg64s.get64, ha, hc]

/-- `%rax` after `imulq %rcx, %rax`. -/
theorem imul_rax : ((FI.imul_rr .rax .rcx).step σ fl).regs.rax.toBitVec = a * c := by
  simp [FI.step, FI.regs, clOf, Reg64s.set64, Reg64s.get64, ha, hc]

end Vals

/-- **The values along the path**: the single instructions' results on the
operands the walks give, as the next walks take them. -/
theorem path_vals :
    hdr0.ushiftRight (((8#64).take 8).toNat &&& 63) = 9#64 ∧ (9#64 &&& 16383#64) = 9#64 ∧
    hdr0.ushiftRight (((22#64).take 8).toNat &&& 63) = 0#64 ∧ (0#64 &&& 16383#64) = 0#64 ∧
    1#64 * 9#64 = 9#64 ∧ 10#64 <<< (((3#64).take 8).toNat &&& 63) = tcbLen ∧
    1#64 * 0#64 = 0#64 ∧ 0#64 <<< (((3#64).take 8).toNat &&& 63) = 0#64 ∧
    1#64 <<< (((36#64).take 8).toNat &&& 63) = 1#64 <<< 36 := by decide

/-! ## The code -/

/-- `scc_rt_alloc_tcb`'s label. -/
abbrev fnL : Label := "scc_rt_alloc_tcb"
/-- Its entry label. -/
abbrev entryL : Label := ".Lscc_rt_alloc_tcb.entry"
/-- The length's label. -/
abbrev lenL : Label := ".Lscc_rt_alloc_tcb.len"
/-- The header's label. -/
abbrev okL : Label := ".Lscc_rt_alloc_tcb.ok"
/-- The abort's label. -/
abbrev fullL : Label := ".Lscc_rt_alloc_tcb.full"

/-- The counter's add `lock xaddq %rax, (%rcx)`. -/
def rmwBlk : List (Directive × Nat) := (parse("lock xaddq %rax, (%rcx)")).zip [5]
/-- The header's store `movq %rax, (%rcx)`. -/
def hdrBlk : List (Directive × Nat) := (parse("movq %rax, (%rcx)")).zip [3]

/-- **The pc of the own word's write** (`scc_rt_pinned_next`'s add). -/
abbrev rmwPc (lab : Label → Int64) : Int64 := lab lenL + Int64.ofNat 158
/-- The pc of the header's store. -/
abbrev hdrPc (lab : Label → Int64) : Int64 := lab okL + Int64.ofNat 140

/-- An instruction with undefined flags at `l + off`. -/
def fiAt (cells : List (Directive × Nat)) (l : Label) (off : Nat) (fi : FI) (z : Nat) : Bool :=
  blockAtB cells l off [(fi.toDir, z)]

/-- A label's address into `%rax` at `l + off`. -/
def siAt (cells : List (Directive × Nat)) (l : Label) (off : Nat) (L : Label) : Bool :=
  blockAtB cells l off [((SI.leaRip .rax L).toDir, 7)]

/-- **`scc_rt_alloc_tcb`'s code in `cells`**: its blocks, its single
instructions and the fall-through into `.entry`. -/
def allocTcbIn (cells : List (Directive × Nat)) : Bool :=
  labelGapB cells fnL entryL 19 && blockAtB cells fnL 0 atPro && blockAtB cells entryL 0 atChk &&
  blockAtB cells entryL 20 atJ1 && blockAtB cells lenL 0 atL0 && fiAt cells lenL 11 (.shr_cl .rax) 3 &&
  blockAtB cells lenL 14 atL1 && fiAt cells lenL 29 (.and_rr .rax .rcx) 3 && blockAtB cells lenL 32 atL2 &&
  fiAt cells lenL 47 (.shr_cl .rax) 3 && blockAtB cells lenL 50 atL3 && fiAt cells lenL 65 (.and_rr .rax .rcx) 3 &&
  blockAtB cells lenL 68 atL4 && fiAt cells lenL 95 (.imul_rr .rax .rcx) 4 && blockAtB cells lenL 99 atL5 &&
  fiAt cells lenL 132 (.shl_cl .rax) 3 && blockAtB cells lenL 135 atL6 &&
  siAt cells lenL 139 "scc_rt_pinned_next" && blockAtB cells lenL 146 atArg && blockAtB cells lenL 158 rmwBlk &&
  blockAtB cells lenL 163 atBnd && blockAtB cells lenL 198 atJ2 &&
  siAt cells okL 0 "scc_rt_pinned" && blockAtB cells okL 7 atO1 && fiAt cells okL 34 (.imul_rr .rax .rcx) 4 &&
  blockAtB cells okL 38 atO2 && fiAt cells okL 53 (.shl_cl .rax) 3 && blockAtB cells okL 56 atO3 &&
  fiAt cells okL 74 (.shl_cl .rax) 3 && blockAtB cells okL 77 atO4 && fiAt cells okL 95 (.or_rr .rax .rcx) 3 &&
  blockAtB cells okL 98 atO5 && blockAtB cells okL 140 hdrBlk && blockAtB cells okL 143 atRet

#guard allocTcbIn SccCode.ret0Cells

/-- The code's check on `ret0Cells`. -/
theorem ret0_allocTcbIn : allocTcbIn SccCode.ret0Cells = true := by decide +kernel

end Spike.Lib.X64.Flow.Ret0.AllocTcb
