/-
**The landing's units premise at the arena of a placement** (x86-64):
`landStk_hxa`'s `hfu` (`Spike/Lib/LowerX64/LandStk2.lean`) at the
allocator's arena `arOf Λ` (`Spike/Lib/Rt/X64ArenaOfPlaceOK.lean`): an
object's units within the arena's cells are its words and the header's
(`Arena.ofWords_units_fit`, the units saturating past `2^63 - 1`).

- `arOf_units_fit`: `hfu` at `arOf Λ`.
-/
import Spike.Lib.Rt.X64ArenaOfPlaceOK

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm

/-- **`arOf Λ`'s units within its cells are the object's** (`landStk_hxa`'s
`hfu`): its `allocCells` cells are below `2^63 - 1`. -/
theorem arOf_units_fit (Λ : Scc.Sem.Layout) :
    ∀ k τ us, TermRun.accs (TermRun.close [] τ) = some us →
      (Spike.Lib.X64.Rt.arOf Λ).units k τ ≤ (Spike.Lib.X64.Rt.arOf Λ).cells →
      (Spike.Lib.X64.Rt.arOf Λ).units k τ = k * TermRun.nWords us + 1 :=
  fun _ _ _ hus h => Spike.Lib.Arena.ofWords_units_fit (by decide) hus h

/-- info: 'Spike.Lib.LowerX64.arOf_units_fit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.arOf_units_fit

end Spike.Lib.LowerX64
