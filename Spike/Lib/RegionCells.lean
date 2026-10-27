/-
**A region's cells as a range**, on any ISA: the addresses `base + lo …
base + hi` of a `Region` (`Spike/Lib/Region.lean`) as a `Scc.Sem.Range`,
for the side condition of `wordsNone_and_fstable`
(`Spike/Lib/{A64,X64}Hello1SetupPriv.lean`): the frame region lies in the
entry stack or the stack pool.

- `cellsR`: the range;
- `cellsR_entry`: the entry stack's region `⟨E.sp, -65536, 0⟩` (`entryR E`
  of `Spike/Lib/Rt/{A64,X64}Layout.lean`) lies in the entry stack;
- `cellsR_callee`: a callee's region (`Region.callee`, under
  `FStable.callee`'s bounds) lies in its caller's;
- `sub_trans`: inclusion is transitive.
-/
import Spike.Lib.Region
import Scc.Sem.CorrectE

namespace Spike.Lib

/-- **The cells of a region** as a range. -/
abbrev cellsR (R : Region) : Scc.Sem.Range := ⟨(R.base.toNat + R.lo).toNat, (R.hi - R.lo).toNat⟩

/-- **The entry stack's region lies in the entry stack**, at an admissible
entry. -/
theorem cellsR_entry {E : Scc.Sem.Entry} {Λ : Scc.Sem.Layout} (hE : E.Ok Λ) :
    (cellsR ⟨BitVec.ofNat 64 E.sp, -65536, 0⟩).Sub E.stack := by
  have h1 := hE.2.2.1
  have h2 := hE.2.2.2
  simp only [Scc.Sem.Range.Sub, BitVec.toNat_ofNat, Scc.Sem.Entry.sp] at *
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- **A callee's region lies in its caller's**, under `FStable.callee`'s
bounds. -/
theorem cellsR_callee {R : Region} {kc lo' hi' : Int} (hR : R.OK) (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0)
    (hkc : kc < R.hi) (hhi : kc + hi' ≤ R.hi) : (cellsR (R.callee kc lo' hi')).Sub (cellsR R) := by
  have hb := Region.addr_toNat_of hR (by omega : R.lo ≤ kc) hkc
  have := hR.lo
  have := hR.hi
  simp only [Region.callee, Scc.Sem.Range.Sub] at *
  omega

/-- Range inclusion is transitive. -/
theorem sub_trans {r s u : Scc.Sem.Range} (h₁ : r.Sub s) (h₂ : s.Sub u) : r.Sub u := by
  unfold Scc.Sem.Range.Sub at *; omega

end Spike.Lib
