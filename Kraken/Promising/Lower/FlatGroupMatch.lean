/-
**The portable group match of WeakCore's
FlatHashMap, lowered to an AArch64 leaf.** ISA: AArch64;
machine: the **sequential** machine-founded wp (`MachineWP`, the triples of
`Kraken/AArch64/Examples/WPControl.lean`). FlatHashMap is owned and by value
(thread-local), so its lowering is a sequential refinement and needs no
weak-memory reasoning.

WeakCore's `FlatHashMap.lean` (portable variant, `x = false`) matches a group
with SWAR on one 64-bit control word `w` (`matchOps`, `emptyOps`, `zb`):

* `pt = wmul h2 L8`, `x = xor w pt`, `mk = zb x` (the lanes whose byte is `h2`);
* `em = zb w` (the empty lanes; `find` stops when `em ≠ 0`);
* `zb y = not (((y and Lo7) wadd Lo7) or y or Lo7)` (the exact zero-byte test).

`§1` (the word primitives of WeakCore's `TermRun.lean`, `W64`, `bitN`,
`bit1N`, …, verbatim, on `Nat`, as the pure model) and `§2` (each operation
the leaf uses is the `toNat` of the `BitVec` operation the semantics
performs) are ISA-neutral and live in `FlatModel.lean`; `§3` is the leaf and its functional specification
`groupMatch_spec`: from any state whose `x0` is the control word and `x1` is
`h2`, the leaf returns to the link address with `x0 = matchN w h2` and
`x1 = emptyN w`, the model's values.

`lookup` itself, and the `RBIT`/`CLZ`/`UMULH` rules it needs, are in
`FlatLookup.lean`; no instruction or semantics is added or changed.
-/
import Kraken.Promising.Lower.FlatModel
import Kraken.AArch64.Parser
import Kraken.AArch64.WP.Cfg
import Kraken.AArch64.WP.RulesCF
import Kraken.AArch64.WP.Rules

open Kraken.AArch64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order

set_option mvcgen.warning false
set_option experimental.vcgen true

namespace Kraken.Promising.Lower.Flat

/-! ## 3. The leaf: `groupMatch`

Arguments `x0` (the control word `w`) and `x1` (`h2`); results `x0` (the match
mask) and `x1` (the empty mask). Scratch: `x2`–`x4`, `x9`, `x10` (caller-saved
under AAPCS64). `Lo7` and `L8` are bitmask immediates. The `mul` is `madd`
with `xzr`; `mvn` is `orn` with `xzr`. -/

/-- The leaf's text: one block, ending in `ret`. -/
def groupMatch : Program := parseAArch64("
group_match:
  mov x9, #0x7f7f7f7f7f7f7f7f
  mov x10, #0x0101010101010101
  mul x2, x1, x10
  eor x2, x0, x2
  and x3, x2, x9
  add x3, x3, x9
  orr x3, x3, x2
  orr x3, x3, x9
  mvn x3, x3
  and x4, x0, x9
  add x4, x4, x9
  orr x4, x4, x0
  orr x4, x4, x9
  mvn x1, x4
  mov x0, x3
  ret
")

section Leaf
variable [CodeEnv]

/-- **The functional spec of the group-match leaf** (sequential machine).
Entered with `x30 = ra`, it returns to `ra` with `x0 = matchN w h2` and
`x1 = emptyN w`, where `w`, `h2` are `x0`, `x1` on entry; memory, `sp` and
the callee-saved `x19`–`x28` are as they were. -/
theorem groupMatch_spec (ra : Int64) (s : MachineData) :
    ⦃ fun t => t = s.setLr ra ∧ True ⦄
      groupMatch
    ⦃ (fun _ _ => False); fun a s' => a = ra
        ∧ s'.regs.X0.toNat = matchN s.regs.X0.toNat s.regs.X1.toNat
        ∧ s'.regs.X1.toNat = emptyN s.regs.X0.toNat
        ∧ s'.dmem = s.dmem ∧ s'.regs.SP = s.regs.SP
        ∧ s'.regs.X19 = s.regs.X19 ∧ s'.regs.X20 = s.regs.X20 ∧ s'.regs.X21 = s.regs.X21
        ∧ s'.regs.X22 = s.regs.X22 ∧ s'.regs.X23 = s.regs.X23 ∧ s'.regs.X24 = s.regs.X24
        ∧ s'.regs.X25 = s.regs.X25 ∧ s'.regs.X26 = s.regs.X26 ∧ s'.regs.X27 = s.regs.X27
        ∧ s'.regs.X28 = s.regs.X28 ⦄ := by
  vcgen [groupMatch] simplifying_assumptions
  rename_i h _ _
  obtain ⟨rfl, -⟩ := h
  simp only [← UInt64.toNat_toBitVec, emptyN, ← matchBV_toNat, ← zbBV_toNat, BitVec.toNat_inj]
  simp [matchBV, zbBV, MachineData.setLr]

end Leaf

end Kraken.Promising.Lower.Flat
