/-
**A region seen from a base `d` bytes higher** (ISA-neutral: imports only
`Spike.Lib.Region`): `R.fp d` is `R` based at `R.addr d` with its offsets
shifted by `-d`, i.e. `R.callee d (R.lo - d) (R.hi - d)`, which covers the same
address range. The ISA-specific node transport (`At.rebase`) is in
`Spike/Lib/X64AtRebase.lean`. It is ISA-specific because each ISA has its own
`At`/`Abs`.

- `Region.fp`;
- `Region.fp_addr`, `Region.fp_off`, `Region.fp_base`: its cells are `R`'s;
- `Region.fp_ok`: it is a region;
- `Region.fp_out`: an address range off `R` is off `R.fp d`, and the
  converse (`Region.fp_out'`).
-/
import Spike.Lib.Region

namespace Spike.Lib

/-- **`R` based `d` bytes higher**: the same cells, offsets shifted by `-d`. -/
def Region.fp (R : Region) (d : Int) : Region := R.callee d (R.lo - d) (R.hi - d)

variable {R : Region} {d : Int}

theorem Region.fp_addr (R : Region) (d k : Int) : (R.fp d).addr k = R.addr (d + k) :=
  Region.callee_addr R d _ _ k

theorem Region.fp_off (hd8 : d % 8 = 0) {k : Int} (hk : (R.fp d).Off k) : R.Off (d + k) :=
  Region.callee_off (by omega) (by omega) hd8 hk

theorem Region.fp_base (hR : R.OK) (h1 : R.lo ≤ d) (h2 : d < R.hi) :
    ((R.fp d).base.toNat : Int) = R.base.toNat + d :=
  Region.callee_base (hi' := R.hi - d) hR (show R.lo ≤ d + (R.lo - d) by omega) (by omega) h2

/-- The re-based region is a region. -/
theorem Region.fp_ok (hR : R.OK) (h1 : R.lo ≤ d) (h2 : d < R.hi) : (R.fp d).OK :=
  Region.callee_ok hR (show R.lo ≤ d + (R.lo - d) by omega) (by omega) h2 (by omega)

/-- **An address range off `R` is off `R.fp d`** (the same range). -/
theorem Region.fp_out (hR : R.OK) (h1 : R.lo ≤ d) (h2 : d < R.hi) {a : Nat}
    (h : ((a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)) :
    (a : Int) + 8 ≤ (R.fp d).base.toNat + (R.fp d).lo ∨ ((R.fp d).base.toNat : Int) + (R.fp d).hi ≤ a := by
  have hb := Region.fp_base hR h1 h2
  simp only [Region.fp, Region.callee] at hb ⊢
  omega

/-- **An address range off `R.fp d` is off `R`** (the same range). -/
theorem Region.fp_out' (hR : R.OK) (h1 : R.lo ≤ d) (h2 : d < R.hi) {a : Nat}
    (h : (a : Int) + 8 ≤ (R.fp d).base.toNat + (R.fp d).lo ∨ ((R.fp d).base.toNat : Int) + (R.fp d).hi ≤ a) :
    ((a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a) := by
  have hb := Region.fp_base hR h1 h2
  simp only [Region.fp, Region.callee] at hb h
  omega

end Spike.Lib

/-- info: 'Spike.Lib.Region.fp_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Region.fp_ok

/-- info: 'Spike.Lib.Region.fp_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Region.fp_out
