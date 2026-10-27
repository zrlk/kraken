/-
**`print`'s arguments at `hello1`'s call site** (x64): the block `wcE2`
(`wc_main`'s `.entry` after its multiply) hands `scc_rt_print` the byte
count `min(n, 8·m)` that `Scc/Lower/Term.lean`'s `callBlock` clamps to
(`cap = m·8`, `k = select ult n cap`, a `cmpq; cmovb`), in `%rsi`, and the
slice's first byte in `%rdi`: the x64 twin of
`Spike/Lib/A64Hello1PrintLen.lean`.

The frame's words at the block's entry are the extern's arguments
`(((b, o), m), n)` (`wcJ`): `b` at `-16`, `o` at `-24`, `m` at `-32`, `n` at
`-40`.

- `wcC_rsi`: `%rsi = min(n, m·8)` (the product as the 64-bit word the code
  computes), whatever the multiply's flags;
- `wcC_rsi_le`: the count is at most `n`;
- `wcC_rsi_lt`: the count is below `2^63` when `8·m` is (the bound
  `seg_printA_ofW` asks of `len0`);
- `wcC_rdi`: `%rdi = b + lo32(o)`.
-/
import Spike.Lib.X64Hello1Body

namespace Spike.Lib.X64.Flow.Hello1

open Kraken.Promising.X64 Spike.Lib.X64

/-- **The byte count**: `min(n, m·8)`. -/
theorem wcC_rsi (lab : String → Int64) (σ : AS) (fl : StatusFlags) :
    ((wcC lab σ fl).regs.get64 .rsi).toNat = min (σ.slot (-40)).toNat (σ.slot (-32) * 8#64).toNat := by
  rw [wcC_eq, wcE2_run]
  simp only [FI.step, wcS1, wcE1_run, FI.regs, Reg64s.get64_set64_self, Spike.Lib.upd_apply]
  simp
  have h8 : (σ.slot (-32) * 8#64).toNat = (σ.slot (-32)).toNat * 8 % 18446744073709551616 := by
    rw [BitVec.toNat_mul]; rfl
  split <;> rename_i h <;> simp only [UInt64.toNat_ofNat] at h <;> omega

/-- The count is at most `n`. -/
theorem wcC_rsi_le (lab : String → Int64) (σ : AS) (fl : StatusFlags) :
    ((wcC lab σ fl).regs.get64 .rsi).toNat ≤ (σ.slot (-40)).toNat := by
  rw [wcC_rsi]; exact Nat.min_le_left _ _

/-- The count is below `2^63` when `8·m` is. -/
theorem wcC_rsi_lt (lab : String → Int64) (σ : AS) (fl : StatusFlags) (hm : (σ.slot (-32)).toNat * 8 < 2 ^ 63) :
    ((wcC lab σ fl).regs.get64 .rsi).toNat < 2 ^ 63 := by
  rw [wcC_rsi]
  have : (σ.slot (-32) * 8#64).toNat = (σ.slot (-32)).toNat * 8 := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]; omega
  omega

/-- **The buffer**: the slice's base plus the offset's low word. -/
theorem wcC_rdi (lab : String → Int64) (σ : AS) (fl : StatusFlags) :
    (wcC lab σ fl).regs.get64 .rdi = σ.slot (-16) + BitVec.setWidth 64 ((σ.slot (-24)).take 32) := by
  rw [wcC_eq, wcE2_run]
  simp only [FI.step, wcS1, wcE1_run, FI.regs, Reg64s.get64_set64_self, Spike.Lib.upd_apply]
  simp only [Reg64s.get]
  simp [Reg.base, Reg.offset]
  rw [BitVec.add_comm]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.drop, BitVec.take]

end Spike.Lib.X64.Flow.Hello1
