import Spike.Lib.LowerX64.Construct
import Spike.Test.LowerInvX64
import Spike.Lib.X64Ret0Code

/-!
# The x86-64 per-construct lemmas on `ret0.w`

`Spike.Lib.LowerX64`'s statements instantiated at `ret0.w`'s `main` (the
frame `mainFr` of `Spike/Test/LowerInvX64.lean`): its `addChk "y%0" 40 2`
block and its `ret [y%0]` block are covered and run as the generic lemmas
say, and they are the cells the assembler laid out (`ret0Cells`, after
`.Lwc_main.entry`).
-/

namespace Spike.Test.LowerX64Construct

open Kraken Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.IR
open Scc.Emit.X64 (S i64 xr om or_ mem)
open Spike.Lib.X64 Spike.Lib.LowerX64 Spike.Test.LowerInvX64

theorem mainFr_ok : FrameOk mainFr := ⟨_, mainF, rfl, rfl⟩

theorem mainFr_small : mainFr.size ≤ 2 ^ 31 := by decide +kernel

/-- The operand loads of `main`'s `addChk`. -/
def la : List Scc.Emit.X64.Item := [.d (i64 (.mov (xr .rax) (.imm (.int64 (40 : UInt64).toInt64))))]
def lb : List Scc.Emit.X64.Item := [.d (i64 (.mov (xr .rcx) (.imm (.int64 (2 : UInt64).toInt64))))]

theorem getOp_a : getOp mainFr .rax (.imm 40) = .ok la := rfl
theorem getOp_b : getOp mainFr .rcx (.imm 2) = .ok lb := rfl

/-- The load of `y%0` into `%rax` (`ret`). -/
def ly : List Scc.Emit.X64.Item := [.d (i64 (.mov (xr .rax) (om (mem .rbp (-8)))))]

theorem getOp_y : getOp mainFr .rax (.reg "y%0") = .ok ly := by
  unfold getOp; rw [Scc.Lower.InvX64.ld_reg (mainFr_y {})]; rfl

theorem rsOf_y : rsOf mainFr "y%0" = some (-8) := rsOf_eq (mainFr_y {})

/-- The overflow label of `main`. -/
abbrev ovf : String := Scc.Emit.X64.labelOf mainFr.fn "ovf"

#guard ovf == ".Lwc_main.ovf"

/-- **`main`'s checked add**, by the generic lemma: covered, and with the
operands `40` and `2` it falls through with `%rax = 42`. -/
example (lab : String → Int64) (pc : Int64) (σ : AS) (zs : List Nat) (hz : zs.length = 4) :=
  add_block mainFr_ok mainFr_small getOp_a getOp_b ovf lab pc σ (zs := zs) (by rw [hz]; rfl)

example (lab : String → Int64) (pc : Int64) (σ : AS) :
    (arun lab ((dirs (la ++ lb ++ addChecked ovf)).zip [7, 7, 3, 2]) ⟨pc, oB mainFr, σ⟩).pc =
      pc + Int64.ofNat 19 := by
  obtain ⟨-, va, vb, hva, hvb, hpc, -⟩ :=
    add_block mainFr_ok mainFr_small getOp_a getOp_b ovf lab pc σ (zs := [7, 7, 3, 2]) rfl
  simp only [Spike.Lib.Form.opdVal, Option.some.injEq] at hva hvb
  have ha : va.toNat = 40 := by rw [← hva]; rfl
  have hb : vb.toNat = 2 := by rw [← hvb]; rfl
  have hlt : va.toNat + vb.toNat < 2 ^ 64 := by omega
  simp only [hpc, hlt, ↓reduceIte]; rfl

/-- **`main`'s return**, by the generic lemma: the code is `retBlk`. -/
theorem ret_main : dirs (ly ++ epiItems) = retBlk [.slot (Int64.ofInt (-8))] := dirs_ret_slot rsOf_y getOp_y

example (s : S) :
    Scc.Emit.X64.emitTerm mainFr (.ret [.reg "y%0"]) s = .ok ((), { s with out := (ly ++ epiItems).reverse ++ s.out }) :=
  emitTerm_ret getOp_y s

/-- Covered in the frame's region `[-16, 16)`. -/
example (zs : List Nat) (hz : zs.length = 4) :
    okBlk (-(mainFr.size : Int)) 16 (oR (-(mainFr.size : Int))) ((retBlk [.slot (Int64.ofInt (-8))]).zip zs) = true :=
  retBlk_ok (by decide +kernel) (by decide +kernel) (by rw [hz]; rfl)

/-! ## Against the assembler's cells -/

-- The add block is the cells after `.Lwc_main.entry`, at the assembler's
-- sizes; the store into `y%0` follows, then the return block.
#guard Scc.Cert.Rt.X64.blockAtB SccCode.ret0Cells ".Lwc_main.entry" 0
  ((dirs (la ++ lb ++ addChecked ovf)).zip [7, 7, 3, 2])
#guard Scc.Cert.Rt.X64.blockAtB SccCode.ret0Cells ".Lwc_main.entry" 23
  ((retBlk [.slot (Int64.ofInt (-8))]).zip [4, 3, 1, 1])

end Spike.Test.LowerX64Construct
