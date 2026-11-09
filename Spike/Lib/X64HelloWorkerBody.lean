/-
**`wc_worker`'s head on x86-64** (the twin of `Spike/Lib/A64WorkerBody.lean`):
hello.w's `wc_worker` from `.Lwc_worker.entry` (after its prologue: `%rsp`
at the frame's base, offset `-88`, `%rbp` at the saved `%rbp`, `-8`; the
six arguments in the words `-16 … -56`) to the call of `scc_rt_print`,
whose return point is `.Lwc_worker.x0` (`Spike/Lib/X64HelloWkTail.lean`).

The `.entry` block is `hello1`'s `wc_main` `.entry` block
(`Spike/Lib/X64Hello1Body.lean`) with its scratch words moved down by 8
(they sit below the worker's six argument words): it computes `print`'s
buffer `%rdi = b + lo32(o)` and count `%rsi = min(n, 8·m)` (`b`, `o`, `m`,
`n` the words at `-16`, `-24`, `-32`, `-40`), writes only the words
`-64 … -88` (and the call's return address at `-96`), and calls
`scc_rt_print` with the return address `.x17`. `imulq` leaves the flags
undefined, so the block is two blocks around the multiply (`wkE1`,
`wkMul`, `wkE2`), and the state at the call is a function of the
multiply's flags `fl` (`wkC`).

- `wkE1`, `wkMul`, `wkE2` (`_ok`, `_run`), `oB`; `wkS1`; `wkC` (the call
  state, irreducible), `wkC_eq`; `wkSl` (the frame's words after the
  block), `wkC_slot`, `wkSl_keep` (the frame record, `c`, `j` kept);
  `wkC_rbp`, `wkC_fs`, `wkC_ra` (the pushed return address `.x17`),
  `wkC_rsi`, `wkC_rsi_lt`, `wkC_rdi`;
- `WN`, `wN`: the head's nodes, from the invariant `J` at `.entry` to
  `print`'s entry with `print`'s predicate `Pr` at 0 bytes.

## Differences from the AArch64 version

- The block is split at the multiply (`imulq` leaves the flags undefined:
  a node of its own, as in `X64Hello1Body`), so `WN` has the nodes
  `.mul`, `.e2` between `.e` and `.call`, and `wkC` takes the flags `fl`;
  `wkSl` is the words at `σ.status` (`wkC_slot`: any flags).
- The return address is the word the `call` pushes (`wkC_ra`, at `-96`,
  given `.x17 = .entry + 87`) for A64's `x30` (`wkE_X30`); the thread
  pointer `fsBase` (`wkC_fs`) for `TPIDR_EL0` (`wkC_tp`); the buffer and
  count are `%rdi`, `%rsi` (`wkC_rdi`, `wkC_rsi`, `wkC_rsi_lt`) for `x0`,
  `x1`; `wkC_rbp` is new (`%rbp` kept).
- `wkSl_keep` keeps the saved `%rbp` (`-8`), the return address (`0`) and
  the tail's words `c`, `j` (`-48`, `-56`).
- A64's `WX`, `wX`, `seg_wkBodyT`, `seg_wkT`, `SegT.seq_or` and the
  `ThrHead` part (dead) are not twinned (`scc_rt_thr_worker`'s head is
  `Spike/Lib/X64HelloThr.lean`'s).
-/
import Spike.Lib.X64Hello1PrintLen
import Spike.Lib.X64HelloWkTail

namespace Spike.Lib.X64.Flow.Worker.Body

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow

set_option linter.unusedSimpArgs false

/-! ## The `.entry` block -/

/-- `wc_worker`'s `.entry` block up to its multiply: `o`'s low half, its sum
with `b`, `m` and the factor `8`. -/
def wkE1 : List (Directive × Nat) := (parse("movq -16(%rbp), %rax
movl %eax, %eax
movq %rax, -56(%rbp)
movq -8(%rbp), %rax
movq -56(%rbp), %rcx
addq %rcx, %rax
movq %rax, -64(%rbp)
movq -24(%rbp), %rax
movq $8, %rcx")).zip [4, 2, 4, 4, 4, 3, 4, 4, 7]

/-- The multiply `imulq %rcx, %rax` (its flags undefined: a node of its own). -/
abbrev wkMul : FI := .imul_rr .rax .rcx

/-- `wc_worker`'s `.entry` block after its multiply: the minimum, `print`'s
arguments, the call. -/
def wkE2 : List (Directive × Nat) := (parse("movq %rax, -72(%rbp)
movq -32(%rbp), %rdx
movq -72(%rbp), %rsi
movq -32(%rbp), %rax
movq -72(%rbp), %rcx
cmpq %rcx, %rax
movq %rsi, %rax
cmovb %rdx, %rax
movq %rax, -80(%rbp)
movq -64(%rbp), %rdi
movq -80(%rbp), %rsi
call scc_rt_print")).zip [4, 4, 4, 4, 4, 3, 3, 4, 4, 4, 4, 5]

/-- The head's offsets: `%rsp` at the frame's base, `%rbp` at the saved
`%rbp`. -/
abbrev oB : SO := ⟨-88, [(.rbp, -8)]⟩

block_spec wkE1 (-144) 8 oB wkE1
block_spec wkE2 (-144) 8 oB wkE2

/-- The state after `.entry`'s first block from `σ`. -/
def wkS1 (lab : Label → Int64) (σ : AS) : AS := (arun lab wkE1 ⟨lab ".Lwc_worker.entry", oB, σ⟩).σ

/-- The abstract state at `print`'s entry, after the `.entry` block from
`σ` with the multiply's flags `fl` (irreducible: the block's closed form is
large). -/
@[irreducible] def wkC (lab : Label → Int64) (σ : AS) (fl : StatusFlags) : AS :=
  (arun lab wkE2 ⟨lab ".Lwc_worker.entry" + 40, oB, wkMul.step (wkS1 lab σ) fl⟩).σ

theorem wkC_eq (lab : Label → Int64) (σ : AS) (fl : StatusFlags) :
    wkC lab σ fl = (arun lab wkE2 ⟨lab ".Lwc_worker.entry" + 40, oB, wkMul.step (wkS1 lab σ) fl⟩).σ := by
  unfold wkC; rfl

/-- The frame's words at `print`'s entry, after the `.entry` block from `σ`
(the multiply's flags do not reach them, `wkC_slot`). -/
def wkSl (lab : Label → Int64) (σ : AS) : Int → BitVec 64 := (wkC lab σ σ.status).slot

theorem wkC_slot (lab : Label → Int64) (σ : AS) (fl : StatusFlags) : (wkC lab σ fl).slot = wkSl lab σ := by
  rw [wkSl, wkC_eq, wkC_eq, wkE2_run, wkE2_run]; rfl

/-- The block keeps the frame record and the tail's words `c`, `j`. -/
theorem wkSl_keep (lab : Label → Int64) (σ : AS) : wkSl lab σ (-8) = σ.slot (-8) ∧ wkSl lab σ 0 = σ.slot 0 ∧
    wkSl lab σ (-48) = σ.slot (-48) ∧ wkSl lab σ (-56) = σ.slot (-56) := by
  simp only [wkSl, wkC_eq, wkE2_run, FI.step, wkS1, wkE1_run]
  exact ⟨by simp [Spike.Lib.upd_apply], by simp [Spike.Lib.upd_apply], by simp [Spike.Lib.upd_apply],
    by simp [Spike.Lib.upd_apply]⟩

/-- The block keeps `%rbp`. -/
theorem wkC_rbp (lab : Label → Int64) (σ : AS) (fl : StatusFlags) :
    (wkC lab σ fl).regs.get64 .rbp = σ.regs.get64 .rbp := by
  rw [wkC_eq, wkE2_run]
  simp [FI.step, wkS1, wkE1_run, FI.regs, Reg64s.get64_set64_ne]

/-- The block keeps the thread pointer. -/
theorem wkC_fs (lab : Label → Int64) (σ : AS) (fl : StatusFlags) :
    (wkC lab σ fl).regs.fsBase = σ.regs.fsBase := by
  rw [wkC_eq, wkE2_run]
  simp [FI.step, wkS1, wkE1_run, FI.regs, Reg64s.set64]

/-- The call pushes `.x17`, the next instruction, `87` bytes on. -/
theorem wkC_ra (lab : Label → Int64) (σ : AS) (fl : StatusFlags)
    (e : lab ".Lwc_worker.x0" = lab ".Lwc_worker.entry" + Int64.ofNat 87) :
    (wkC lab σ fl).slot (-96) = (lab ".Lwc_worker.x0").toBitVec := by
  rw [wkC_eq, wkE2_run, e]
  simp only [Spike.Lib.upd_apply, ↓reduceIte, Int64.toBitVec_add, BitVec.add_assoc]
  rfl

/-- **The byte count**: `min(n, m·8)`. -/
theorem wkC_rsi (lab : Label → Int64) (σ : AS) (fl : StatusFlags) :
    ((wkC lab σ fl).regs.get64 .rsi).toNat = min (σ.slot (-40)).toNat (σ.slot (-32) * 8#64).toNat := by
  rw [wkC_eq, wkE2_run]
  simp only [FI.step, wkS1, wkE1_run, FI.regs, Reg64s.get64_set64_self, Spike.Lib.upd_apply]
  simp
  have h8 : (σ.slot (-32) * 8#64).toNat = (σ.slot (-32)).toNat * 8 % 18446744073709551616 := by
    rw [BitVec.toNat_mul]; rfl
  split <;> rename_i h <;> simp only [UInt64.toNat_ofNat] at h <;> omega

/-- The count is below `2^63` when `8·m` is. -/
theorem wkC_rsi_lt (lab : Label → Int64) (σ : AS) (fl : StatusFlags) (hm : (σ.slot (-32)).toNat * 8 < 2 ^ 63) :
    ((wkC lab σ fl).regs.get64 .rsi).toNat < 2 ^ 63 := by
  rw [wkC_rsi]
  have : (σ.slot (-32) * 8#64).toNat = (σ.slot (-32)).toNat * 8 := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]; omega
  omega

/-- **The buffer**: the slice's base plus the offset's low word. -/
theorem wkC_rdi (lab : Label → Int64) (σ : AS) (fl : StatusFlags) :
    (wkC lab σ fl).regs.get64 .rdi = σ.slot (-16) + BitVec.setWidth 64 ((σ.slot (-24)).take 32) := by
  rw [wkC_eq, wkE2_run]
  simp only [FI.step, wkS1, wkE1_run, FI.regs, Reg64s.get64_set64_self, Spike.Lib.upd_apply]
  simp only [Reg64s.get]
  simp [Reg.base, Reg.offset]
  rw [BitVec.add_comm]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.drop, BitVec.take]

/-! ## The head -/

/-- The head's internal nodes. -/
inductive WN where
  | e | mul | e2 | call

section Spec

variable (lab : Label → Int64) (J : AS → Ctl → Prop) (Pr : AS → Nat → Ctl → Prop)

/-- **The head's nodes**, from the invariant `J` at `.entry` (the source
stutters through the block); at the call, the source at `print`'s
predicate `Pr` of the call state at 0 bytes. -/
def wN : WN → ND
  | .e => ⟨lab ".Lwc_worker.entry", oB, J⟩
  | .mul => ⟨lab ".Lwc_worker.entry" + 36, oB, fun σ c => ∃ σ0, J σ0 c ∧ σ = wkS1 lab σ0⟩
  | .e2 => ⟨lab ".Lwc_worker.entry" + 40, oB, fun σ c => ∃ σ0 fl, J σ0 c ∧ σ = wkMul.step (wkS1 lab σ0) fl⟩
  | .call => ⟨lab "scc_rt_print", ⟨-96, []⟩, fun σ c => (∃ σ0 c0 fl, J σ0 c0 ∧ σ = wkC lab σ0 fl) ∧ Pr σ 0 c⟩

end Spec

end Spike.Lib.X64.Flow.Worker.Body

/-- info: 'Spike.Lib.X64.Flow.Worker.Body.wkSl_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Body.wkSl_keep

/-- info: 'Spike.Lib.X64.Flow.Worker.Body.wkC_ra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Body.wkC_ra

/-- info: 'Spike.Lib.X64.Flow.Worker.Body.wkC_rsi_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Body.wkC_rsi_lt

/-- info: 'Spike.Lib.X64.Flow.Worker.Body.wkC_rdi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Body.wkC_rdi

/-- info: 'Spike.Lib.X64.Flow.Worker.Body.wkC_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Body.wkC_fs
