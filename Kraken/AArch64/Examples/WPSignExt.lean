/-
`vcgen` over the sign-extending loads: `LDRSB`/`LDRSH`/`LDRSW`, their
unscaled forms `LDURS*`, and `LDPSW`.

- `sext_correct`: on mapped memory, by the `MachineWP` rules of
  `Kraken.AArch64.WP.RulesSignExt` (`ldrsb_spec`, `ldursh_spec`, `ldrsw_spec`,
  `ldpsw_spec`); the bytes are readable and hold the given values.
- `sext_correctEnv`: the same program over the environment wp
  (`EnvProgram`), with the four accessed slots shared
  (`SharedEnv.lastWrite`) and none of them in `dmem`: the combined rules of
  `Kraken/AArch64/EnvVCGen.lean` (`ldrsb_env_spec`, `ldursh_env_spec`,
  `ldrsw_env_spec`, `ldpsw_env_spec`) take their shared disjuncts.

In both, a negative byte or halfword lands in the register with its upper bits
set: `0x80` read by `LDRSB Xt` is `-128`.
-/
import Kraken.AArch64.Parser
import Kraken.AArch64.EnvVCGen

open Kraken.AArch64.Parser
open Kraken
open Std.WP
open MachineWP

set_option mvcgen.warning false
set_option experimental.vcgen true

section

variable [layout : _root_.Layout]

/-- One load of each sign-extending family. -/
def sext : Program := parseAArch64("
  ldrsb x2, [x1, #1]
  ldursh w3, [x1, #-2]
  ldrsw x4, [x1, #8]
  ldpsw x5, x6, [x1, #16]
")

local instance sext.env : CodeEnv := ⟨layout sext⟩

/-- On mapped memory: each register gets its field sign-extended. -/
theorem sext_correct (d : MachineData) (b h w w₁ w₂ : Int)
    (hb : Mem.loadInt d.dmem (d.regs.X1.toBitVec + 1#64) 1 = some b)
    (hh : Mem.loadInt d.dmem (d.regs.X1.toBitVec - 2#64) 2 = some h)
    (hw : Mem.loadInt d.dmem (d.regs.X1.toBitVec + 8#64) 4 = some w)
    (hw₁ : Mem.loadInt d.dmem (d.regs.X1.toBitVec + 16#64) 4 = some w₁)
    (hw₂ : Mem.loadInt d.dmem (d.regs.X1.toBitVec + 20#64) 4 = some w₂) :
    ⦃ fun s => s = d ⦄
      sext
    ⦃ fun _ s => s.regs.X2.toBitVec = (BitVec.ofInt 8 b).signExtend 64
        ∧ s.regs.X3.toBitVec = ((BitVec.ofInt 16 h).signExtend 32).setWidth 64
        ∧ s.regs.X4.toBitVec = (BitVec.ofInt 32 w).signExtend 64
        ∧ s.regs.X5.toBitVec = (BitVec.ofInt 32 w₁).signExtend 64
        ∧ s.regs.X6.toBitVec = (BitVec.ofInt 32 w₂).signExtend 64 ⦄ := by
  -- `#-2` arrives as the 64-bit two's complement of 2; `LDPSW`'s second slot is
  -- 4 bytes past the first
  have e₂ : d.regs.X1.toBitVec - 2#64 = d.regs.X1.toBitVec + 18446744073709551614#64 := by bv_omega
  have e₂₀ : d.regs.X1.toBitVec + 16#64 + 4#64 = d.regs.X1.toBitVec + 20#64 := by bv_omega
  rw [e₂] at hh
  vcgen [sext]
  all_goals subst_vars
  all_goals simp_all

/-- The same program on shared slots: each register gets the environment's
value for its slot, sign-extended. -/
theorem sext_correctEnv (d : MachineData)
    (hb : Mem.loadInt d.dmem (d.regs.X1.toBitVec + 1#64) 1 = none)
    (hh : Mem.loadInt d.dmem (d.regs.X1.toBitVec - 2#64) 2 = none)
    (hw : Mem.loadInt d.dmem (d.regs.X1.toBitVec + 8#64) 4 = none)
    (hw₁ : Mem.loadInt d.dmem (d.regs.X1.toBitVec + 16#64) 4 = none)
    (hw₂ : Mem.loadInt d.dmem (d.regs.X1.toBitVec + 20#64) 4 = none) :
    let x1 := d.regs.X1.toBitVec
    TripleEnv (SharedEnv.lastWrite
        [(x1 + 1#64, 1), (x1 - 2#64, 2), (x1 + 8#64, 4), (x1 + 16#64, 4), (x1 + 20#64, 4)])
      (fun s _ => s = d)
      sext
      (fun s g => s.regs.X2.toBitVec = ((g (x1 + 1#64)).setWidth 8).signExtend 64
        ∧ s.regs.X3.toBitVec = (((g (x1 - 2#64)).setWidth 16).signExtend 32).setWidth 64
        ∧ s.regs.X4.toBitVec = ((g (x1 + 8#64)).setWidth 32).signExtend 64
        ∧ s.regs.X5.toBitVec = ((g (x1 + 16#64)).setWidth 32).signExtend 64
        ∧ s.regs.X6.toBitVec = ((g (x1 + 20#64)).setWidth 32).signExtend 64)
      (fun _ _ _ => False) := by
  intro x1
  have e₂ : d.regs.X1.toBitVec - 2#64 = d.regs.X1.toBitVec + 18446744073709551614#64 := by bv_omega
  have e₂₀ : d.regs.X1.toBitVec + 16#64 + 4#64 = d.regs.X1.toBitVec + 20#64 := by bv_omega
  apply TripleEnv.of_triple
  unfold sext
  vcgen
  -- each load: the environment's answer is its slot's value, the state unchanged
  all_goals simp_all [x1, SharedEnv.lastWrite, and_assoc]

end
