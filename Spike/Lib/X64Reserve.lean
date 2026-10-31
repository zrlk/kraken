/-
**`scc_rt_thread_reserve` on x86-64, block by block**: the x86-64 twin of
`Spike/Lib/A64Reserve.lean`. The walks of the thread counter's reservation
along its one feasible path (the counter's old value `n` with
`n + 1 ≤ 1023`, so the bound's abort is not taken), the named entry and
exit predicates of its segment, and the pc of its write outside the frame
(`Runtime.threadReserveF`, `Scc.Cert.Spawn.X64.reserveGrps`).

    scc_rt_thread_reserve():                  frame of 32 below %rbp
      .entry: %rax = &scc_rt_nthreads                       (leaq)
              -8(%rbp) = %rax; %rcx = %rax; %rax = 1        (rArg)
              n = lock xadd [scc_rt_nthreads], 1            (rmwPc)
              -16(%rbp) = n; -24(%rbp) = n + 1
              if n + 1 > 1023 goto full                     (rBnd: not taken)
              goto ok                                       (rJ)
      .ok:    %rax = n + 1; ret                             (rRet)

- **The specification**: `Pre g` at the entry (`%rsp`, `%rbp` and the
  return address the ghosts) and `Post g n` at `g.ra` (`%rax = n + 1`).
  The ghost `n` is the own word `scc_rt_nthreads` at the add; it holds
  `n + 1` after `rmwPc`.
- **The frame** (`Fr g ss`, cells `s0` … `s2`), **the walks** (`rPro_walk`
  … `rRet_walk`), the `leaq`'s (`si_fr`, `si_so`, `si_rax`) and **the
  code** (`reserveIn`), as `X64Ret0AllocTcb`'s.

Where x86-64 differs from AArch64: the counter's address is one `leaq`
(AArch64's `adrp`/`add` pair), the frame is `Fr g ss` with cell lists, and
the jump to `.ok` is its own block (`rJ`), as AArch64's.
-/
import Spike.Lib.X64Ret0AllocTcb

namespace Spike.Lib.X64.Flow.Reserve

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB)
open Spike.Lib.X64.Flow.Ret0.AllocTcb (G siAt)

set_option linter.unusedSimpArgs false

/-! ## The blocks -/

/-- The offsets in the frame: `%rsp` at the frame's base, `%rbp` at the saved `%rbp`. -/
abbrev oI : SO := ⟨-40, [(.rbp, -8)]⟩
/-- The offsets at entry. -/
abbrev oE : SO := ⟨0, []⟩
/-- The offsets after the return. -/
abbrev oR : SO := ⟨8, []⟩

/-- The prologue: a frame of 32. -/
def rPro : List (Directive × Nat) := (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp")).zip [1, 3, 4]

/-- The add's operands: the counter's address saved, `%rcx` the address, `%rax = 1`. -/
def rArg : List (Directive × Nat) := (parse("movq %rax, -8(%rbp)
movq -8(%rbp), %rcx
movq $1, %rax")).zip [4, 4, 7]

/-- The old value and `n + 1` saved; past `maxThreads` goes to the abort. -/
def rBnd : List (Directive × Nat) := (parse("movq %rax, -16(%rbp)
movq -16(%rbp), %rax
movq $1, %rcx
addq %rcx, %rax
movq %rax, -24(%rbp)
movq -24(%rbp), %rax
movq $1023, %rcx
cmpq %rcx, %rax
ja .Lscc_rt_thread_reserve.full")).zip [4, 4, 7, 3, 4, 4, 7, 3, 2]

/-- On to `.ok`. -/
def rJ : List (Directive × Nat) := (parse("jmp .Lscc_rt_thread_reserve.ok")).zip [2]

/-- The result `n + 1` and the epilogue. -/
def rRet : List (Directive × Nat) := (parse("movq -24(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 3, 1, 1]

block_spec rPro (-40) 8 oE rPro
block_spec rArg (-40) 8 oI rArg
block_spec rBnd (-40) 8 oI rBnd
block_spec rJ (-40) 8 oI rJ
block_spec rRet (-40) 8 oI rRet

/-! ## The specification -/

/-- **Entry**: `%rsp`, `%rbp`, the return address the ghosts'. -/
def Pre (g : G) (σ : AS) : Prop :=
  σ.regs.rsp.toBitVec = g.sp ∧ σ.regs.rbp.toBitVec = g.fp ∧ σ.slot 0 = g.ra

/-- **Exit** (at `g.ra`): `%rsp` past the return address, `%rbp` restored,
`%rax = n + 1`, the new thread's id. `scc_rt_nthreads` holds `n + 1`. -/
def Post (g : G) (n : BitVec 64) (σ : AS) : Prop :=
  σ.regs.rsp.toBitVec = g.sp + 8#64 ∧ σ.regs.rbp.toBitVec = g.fp ∧ σ.regs.rax.toBitVec = n + 1#64

/-- **The frame**: `%rsp` at the frame's base, `%rbp` at the saved `%rbp`,
the cells `ss` (offsets from the entry's `%rsp`). -/
def Fr (g : G) (ss : List (Int × BitVec 64)) (σ : AS) : Prop :=
  σ.regs.rsp.toBitVec = g.sp - 40#64 ∧ σ.regs.rbp.toBitVec = g.sp - 8#64 ∧ ∀ p ∈ ss, σ.slot p.1 = p.2

/-- The return address and the saved `%rbp`. -/
abbrev s0 (g : G) : List (Int × BitVec 64) := [(0, g.ra), (-8, g.fp)]
/-- With the counter's address `P`. -/
abbrev s1 (g : G) (P : BitVec 64) : List (Int × BitVec 64) := (-16, P) :: s0 g
/-- With the old value `n` and `n + 1`. -/
abbrev s2 (g : G) (P n : BitVec 64) : List (Int × BitVec 64) := (-24, n) :: (-32, n + 1#64) :: s1 g P

/-! ## The walks -/

/-- Unfolds a frame hypothesis. -/
local macro "frh" h:ident : tactic => `(tactic| simp only [Fr, List.forall_mem_cons, List.forall_mem_nil] at $h:ident)

/-- Closes a walk's goal from the run's normal form. -/
local macro "walk" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [Fr, Post, Reg64s.set64, Reg64s.get64, upd_apply, $ts,*])

/-- **The prologue**: from the entry to `.entry`, the frame set up. -/
theorem rPro_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} (h : Pre g σ) :
    (arun lab rPro ⟨pc, oE, σ⟩).pc = pc + Int64.ofNat 8 ∧
    (arun lab rPro ⟨pc, oE, σ⟩).so = oI ∧ Fr g (s0 g) (arun lab rPro ⟨pc, oE, σ⟩).σ := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [rPro_run]
  refine ⟨rfl, rfl, ?_⟩
  walk [h1, h2, h3]
  bv_omega

/-- **The add's operands**: `%rax = 1`, `%rcx` the counter's address `P` (in
`%rax` before), `P` saved. -/
theorem rArg_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {P : BitVec 64} (h : Fr g (s0 g) σ)
    (hP : σ.regs.rax.toBitVec = P) :
    (arun lab rArg ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 15 ∧
    (arun lab rArg ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s1 g P) (arun lab rArg ⟨pc, oI, σ⟩).σ ∧
    (arun lab rArg ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = 1#64 ∧
    (arun lab rArg ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = P := by
  frh h
  rw [rArg_run]
  walk [h, hP]

/-- **The bound is not crossed** when the old value `n` (in `%rax`) has
`n + 1 ≤ 1023`. -/
theorem rBnd_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {P n : BitVec 64} (h : Fr g (s1 g P) σ)
    (ha : σ.regs.rax.toBitVec = n) (hn : n.toNat + 1 ≤ 1023) :
    (arun lab rBnd ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 38 ∧
    (arun lab rBnd ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s2 g P n) (arun lab rBnd ⟨pc, oI, σ⟩).σ := by
  frh h
  have hr : (σ.regs.rax.toNat : Int) = n.toNat := by rw [← ha]; rfl
  rw [rBnd_run]
  walk [h, ha]
  refine ⟨fun h1 h2 => ?_, BitVec.add_comm _ _⟩
  by_cases he : n.toNat + 1 = 1023
  · refine absurd (BitVec.eq_of_toNat_eq ?_) h2
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Width.bits] at he ⊢
    omega
  · rw [hr] at h1; omega

/-- On to `.ok`. -/
theorem rJ_walk (lab : String → Int64) (pc : Int64) {g : G} {P n : BitVec 64} {σ : AS} (h : Fr g (s2 g P n) σ) :
    (arun lab rJ ⟨pc, oI, σ⟩).pc = lab ".Lscc_rt_thread_reserve.ok" ∧
    (arun lab rJ ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s2 g P n) (arun lab rJ ⟨pc, oI, σ⟩).σ := by
  rw [rJ_run]
  exact ⟨rfl, rfl, h⟩

/-- **The return**: to `g.ra` with `%rax = n + 1`, the frame popped. -/
theorem rRet_walk (lab : String → Int64) (pc : Int64) {g : G} {σ : AS} {P n : BitVec 64} (h : Fr g (s2 g P n) σ) :
    (arun lab rRet ⟨pc, oI, σ⟩).pc = Int64.ofBitVec g.ra ∧
    (arun lab rRet ⟨pc, oI, σ⟩).so = oR ∧ Post g n (arun lab rRet ⟨pc, oI, σ⟩).σ := by
  frh h
  rw [rRet_run]
  walk [h]

/-! ## The counter's address -/

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

/-! ## The code -/

/-- `scc_rt_thread_reserve`'s label. -/
abbrev fnL : Label := "scc_rt_thread_reserve"
/-- Its entry label. -/
abbrev entryL : Label := ".Lscc_rt_thread_reserve.entry"
/-- The return's label. -/
abbrev okL : Label := ".Lscc_rt_thread_reserve.ok"
/-- The abort's label. -/
abbrev fullL : Label := ".Lscc_rt_thread_reserve.full"

/-- The counter's add `lock xaddq %rax, (%rcx)`. -/
def rmwBlk : List (Directive × Nat) := (parse("lock xaddq %rax, (%rcx)")).zip [5]

/-- **The pc of the own word's write** (`scc_rt_nthreads`' add). -/
abbrev rmwPc (lab : Label → Int64) : Int64 := lab entryL + Int64.ofNat 22

/-- **`scc_rt_thread_reserve`'s code in `cells`**: its blocks, its `leaq`
and the fall-through into `.entry`. -/
def reserveIn (cells : List (Directive × Nat)) : Bool :=
  labelGapB cells fnL entryL 8 && blockAtB cells fnL 0 rPro && siAt cells entryL 0 "scc_rt_nthreads" &&
  blockAtB cells entryL 7 rArg && blockAtB cells entryL 22 rmwBlk && blockAtB cells entryL 27 rBnd &&
  blockAtB cells entryL 65 rJ && blockAtB cells okL 0 rRet

end Spike.Lib.X64.Flow.Reserve

/-- info: 'Spike.Lib.X64.Flow.Reserve.rPro_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Reserve.rPro_walk

/-- info: 'Spike.Lib.X64.Flow.Reserve.rArg_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Reserve.rArg_walk

/-- info: 'Spike.Lib.X64.Flow.Reserve.rBnd_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Reserve.rBnd_walk

/-- info: 'Spike.Lib.X64.Flow.Reserve.rJ_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Reserve.rJ_walk

/-- info: 'Spike.Lib.X64.Flow.Reserve.rRet_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Reserve.rRet_walk

/-- info: 'Spike.Lib.X64.Flow.Reserve.si_fr' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Reserve.si_fr

/-- info: 'Spike.Lib.X64.Flow.Reserve.si_so' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Reserve.si_so

/-- info: 'Spike.Lib.X64.Flow.Reserve.si_rax' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Reserve.si_rax
