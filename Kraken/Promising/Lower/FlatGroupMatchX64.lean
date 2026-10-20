/-
WeakCore's FlatHashMap portable group match, lowered to an x64 leaf. ISA:
x64; machine: the sequential machine-founded wp (`MachineWP`). The twin of
the AArch64 `FlatGroupMatch.lean`, over the same ISA-neutral model
(`FlatModel.lean`: `matchN`, `emptyN`, `zbBV`, `matchBV`).

The leaf `groupMatchX` takes the control word `w` in `rdi` and `h2` in `rsi`
(SysV argument registers) and returns the match mask in `rax` and the empty
mask in `rdx` (a two-word result, as SysV returns one). It computes
`pt = h2 * L8` with `imul`, `x = w ^ pt`, and `zb` of `x` and of `w`; the
constants `Lo7` and `L8` are `movabs` immediates. Scratch: `rcx`, `r8`
(caller-saved).

`groupMatchX_spec`: entered with a return address on the stack, the leaf
returns to it with `rax = matchN w h2` and `rdx = emptyN w`, the stack
popped, memory and the callee-saved `rbx`, `rbp`, `r12`–`r15` unchanged.
-/
import Kraken.Promising.Lower.FlatModel
import Kraken.X64.Parser
import Kraken.MachineWPALU

open Kraken
open Std.WP
open MachineWP
open Lean.Order

set_option mvcgen.warning false
set_option experimental.vcgen true

namespace Kraken.Promising.Lower.Flat

/-- `sp` popped by the return, and the SysV callee-saved registers as in `t₀`. -/
def CalleeX (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp + 8 ∧ s.regs.get64 .rbx = t₀.regs.get64 .rbx
    ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ s.regs.get64 .r12 = t₀.regs.get64 .r12
    ∧ s.regs.get64 .r13 = t₀.regs.get64 .r13 ∧ s.regs.get64 .r14 = t₀.regs.get64 .r14
    ∧ s.regs.get64 .r15 = t₀.regs.get64 .r15

/-- The leaf's text: one block, ending in `ret`. -/
def groupMatchX : Program := parse("
group_match:
  movabsq $0x7f7f7f7f7f7f7f7f, %rcx
  movabsq $0x0101010101010101, %rdx
  movq %rsi, %rax
  imulq %rdx, %rax
  movq %rdi, %r8
  xorq %rax, %r8
  movq %r8, %rax
  andq %rcx, %rax
  addq %rcx, %rax
  orq %r8, %rax
  orq %rcx, %rax
  notq %rax
  movq %rdi, %rdx
  andq %rcx, %rdx
  addq %rcx, %rdx
  orq %rdi, %rdx
  orq %rcx, %rdx
  notq %rdx
  ret
")

section Leaf
variable [CodeEnv]

/-- **The functional spec of the x64 group-match leaf** (sequential machine).
Entered with return address `ra` on the stack, it returns to `ra` with
`rax = matchN w h2` and `rdx = emptyN w`, where `w`, `h2` are `rdi`, `rsi` on
entry; memory is unchanged, `rsp` is popped, and `rbx`, `rbp`, `r12`–`r15`
are as they were. -/
theorem groupMatchX_spec (ra : Int64) (s : MachineData) (hra : s.retAddr = some ra) :
    ⦃ fun t => t = s ⦄
      groupMatchX
    ⦃ (fun _ _ => False); fun a s' => a = ra
        ∧ (s'.regs.get64 .rax).toNat = matchN (s.regs.get64 .rdi).toNat (s.regs.get64 .rsi).toNat
        ∧ (s'.regs.get64 .rdx).toNat = emptyN (s.regs.get64 .rdi).toNat
        ∧ s'.dmem = s.dmem ∧ CalleeX s s' ⦄ := by
  vcgen [groupMatchX] simplifying_assumptions
  all_goals subst_vars
  · simp only [MachineData.retAddr_eq, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hra ⊢
    simp only [Reg64s.get64, Option.map_eq_some_iff] at hra
    obtain ⟨_, h, _⟩ := hra
    simp [h]
  · rename_i ra' h'
    simp only [MachineData.retAddr_eq, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at h'
    rw [← MachineData.retAddr_eq, hra, Option.some.injEq] at h'
    subst h'
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, emptyN, ← matchBV_toNat, ← zbBV_toNat,
      BitVec.toNat_inj, CalleeX, matchBV, zbBV, true_and, and_true]
    exact ⟨by rw [BitVec.add_comm], by rw [BitVec.add_comm], rfl⟩

end Leaf

end Kraken.Promising.Lower.Flat
