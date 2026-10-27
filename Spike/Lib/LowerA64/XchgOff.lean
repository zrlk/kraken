/-
**scc's word accesses at `[b + disp]` as `LdAt`/`StAt`** (AArch64):
`ldrOff .W64 t (xs b) disp` and `strOff .W64 t (xs b) disp`
(`Scc/Emit/A64.lean`) are a prefix `pre` (none, or `movImm x16, disp`) then
one plain word access (`Spike/Lib/A64XchgSeg.lean`'s `LdAt`, `StAt`) whose
address, after `pre`'s run, is `b + disp`, in every form: scaled, unscaled,
register offset.

- `rAddr_ofInt`: `[Xn, #i]`'s address at an `Int64.ofInt` displacement;
- `ldrOff_form`, `strOff_form`.
-/
import Spike.Lib.A64XchgSeg
import Spike.Lib.LowerA64.Construct

namespace Spike.Lib.LowerA64

open Kraken Kraken.AArch64.Parser Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64

/-- **`[Xn, #i]`'s address at the displacement `ofInt d`** is `Xn + d`. -/
theorem rAddr_ofInt (r : Reg64s) (b : XReg) (d : Int) :
    rAddr r b (Int64.ofInt d) = (r.getXReg b).toBitVec + BitVec.ofInt 64 d := by
  unfold rAddr
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt]
  congr 1
  exact BitVec.ofInt_toInt

/-- The address `[Xn, Xm]` after `Xm := d` is `Xn + d` (`n ≠ m`). -/
theorem xAddr_set (r : Reg64s) {b m : XReg} (h : b ≠ m) (d : Int) :
    xAddr (r.setXReg m (BitVec.ofInt 64 d)) b m = (r.getXReg b).toBitVec + BitVec.ofInt 64 d := by
  simp [xAddr, h]

/-- **A word load `ldrOff .W64 t (xs b) disp`** is a prefix `pre` (none,
or `x16 := disp`), then a plain load into `Xt` at an address function
`ad` that reads `b + disp` after `pre`'s run (`b` not `x16`). -/
theorem ldrOff_form (t : XReg) {b : XReg} (hb : b ≠ scratch0) (disp : Int) :
    ∃ (pre : List Item) (dL : Directive) (ad : Reg64s → BitVec 64),
      directives (ldrOff .W64 t (xs b) disp) = directives pre ++ [dL] ∧ LdAt dL t ad ∧
      (pre = [] ∨ pre = movImm scratch0 disp) ∧
      ∀ lab pc o σ, ad (arun lab (directives pre) ⟨pc, o, σ⟩).σ.regs =
        (σ.regs.getXReg b).toBitVec + BitVec.ofInt 64 disp := by
  unfold ldrOff
  split
  · exact ⟨[], ldrDir t b (Int64.ofInt disp), (rAddr · b (Int64.ofInt disp)), rfl, ldAt_ldr _ _ _, .inl rfl,
      fun _ _ _ σ => rAddr_ofInt σ.regs b disp⟩
  · split
    · exact ⟨[], ldurDir t b (Int64.ofInt disp), (rAddr · b (Int64.ofInt disp)), rfl, ldAt_ldur _ _ _,
        .inl rfl, fun _ _ _ σ => rAddr_ofInt σ.regs b disp⟩
    · refine ⟨movImm scratch0 disp, ldrXDir t b scratch0, (xAddr · b scratch0), ?_, ldAt_ldrX _ _ _, .inr rfl,
        fun lab pc o σ => ?_⟩
      · simp [directives, ldrXDir, ins, xz, rz, xs]
      · rw [arun_movImm]; exact xAddr_set σ.regs hb disp

/-- **A word store `strOff .W64 t (xs b) disp`** is a prefix `pre` (none,
or `x16 := disp`), then a plain store of `Xt` at an address function `ad`
that reads `b + disp` after `pre`'s run (`b` not `x16`). -/
theorem strOff_form (t : XReg) {b : XReg} (hb : b ≠ scratch0) (disp : Int) :
    ∃ (pre : List Item) (dS : Directive) (ad : Reg64s → BitVec 64),
      directives (strOff .W64 t (xs b) disp) = directives pre ++ [dS] ∧ StAt dS t ad ∧
      (pre = [] ∨ pre = movImm scratch0 disp) ∧
      ∀ lab pc o σ, ad (arun lab (directives pre) ⟨pc, o, σ⟩).σ.regs =
        (σ.regs.getXReg b).toBitVec + BitVec.ofInt 64 disp := by
  unfold strOff
  split
  · exact ⟨[], strDir t b (Int64.ofInt disp), (rAddr · b (Int64.ofInt disp)), rfl, stAt_str _ _ _, .inl rfl,
      fun _ _ _ σ => rAddr_ofInt σ.regs b disp⟩
  · split
    · exact ⟨[], sturDir t b (Int64.ofInt disp), (rAddr · b (Int64.ofInt disp)), rfl, stAt_stur _ _ _,
        .inl rfl, fun _ _ _ σ => rAddr_ofInt σ.regs b disp⟩
    · refine ⟨movImm scratch0 disp, strXDir t b scratch0, (xAddr · b scratch0), ?_, stAt_strX _ _ _, .inr rfl,
        fun lab pc o σ => ?_⟩
      · simp [directives, strXDir, ins, xz, rz, xs]
      · rw [arun_movImm]; exact xAddr_set σ.regs hb disp

end Spike.Lib.LowerA64
