/-
**`print`'s arguments at `hello1`'s call site** (AArch64): the block
`wcE` (`wc_main`'s `.0_entry`) hands `scc_rt_print` the byte count
`min(n, 8·m)` that `Scc/Lower/Term.lean`'s `callBlock` clamps to (`cap = m·8`,
`k = select ult n cap`), in `x1`, and the slice's first byte in `x0`.

The frame's words at the block's entry are the extern's arguments
`(((b, o), m), n)`: `b` at `-96`, `o` at `-88`, `m` at `-80`, `n` at `-72`.

- `wcC_x1`: `x1 = min(n, m·8)` (the product as the 64-bit word the code
  computes);
- `wcC_x1_le`: the count is at most `n`;
- `wcC_x1_lt`: the count is below `2^63` when `8·m` is (the bound
  `seg_printA_ofW` asks of `len0`);
- `wcC_x0`: `x0 = b + lo32(o)`.
-/
import Spike.Lib.A64Hello1Body
import Spike.Lib.A64Alloc

namespace Spike.Lib.A64.Flow.Hello1

open Kraken.Promising.AArch64
open Spike.Lib.A64.Alloc (subs_c)

/-- **The byte count**: `min(n, m·8)`. -/
theorem wcC_x1 (lab : String → Int64) (σ : AS) :
    (wcC lab σ).regs.X1.toBitVec.toNat = min (σ.slot (-72)).toNat (σ.slot (-80) * 8#64).toNat := by
  rw [wcC_eq, wcE_run]
  simp only [subs_c]
  by_cases h : (σ.slot (-80) * 8#64).toNat ≤ (σ.slot (-72)).toNat
  · simp only [h, decide_true, Bool.true_eq_false, ite_false]; omega
  · simp only [h, decide_false, ite_true]; omega

/-- The count is at most `n`. -/
theorem wcC_x1_le (lab : String → Int64) (σ : AS) :
    (wcC lab σ).regs.X1.toBitVec.toNat ≤ (σ.slot (-72)).toNat := by
  rw [wcC_x1]; exact Nat.min_le_left _ _

/-- The count is below `2^63` when `8·m` is. -/
theorem wcC_x1_lt (lab : String → Int64) (σ : AS) (hm : (σ.slot (-80)).toNat * 8 < 2 ^ 63) :
    (wcC lab σ).regs.X1.toBitVec.toNat < 2 ^ 63 := by
  rw [wcC_x1]
  have : (σ.slot (-80) * 8#64).toNat = (σ.slot (-80)).toNat * 8 := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]; omega
  omega

/-- **The buffer**: the slice's base plus the offset's low word. -/
theorem wcC_x0 (lab : String → Int64) (σ : AS) :
    (wcC lab σ).regs.X0.toBitVec = σ.slot (-96) + BitVec.setWidth 64 ((σ.slot (-88)).take 32) := by
  rw [wcC_eq, wcE_run]; rfl

end Spike.Lib.A64.Flow.Hello1
