/-
**An allocator's landing is one the arena hands out** (ISA-neutral): the
allocator's return node (`Ea` of `Spike/Lib/A64Alloc.lean` and its x86-64
twin) gives the base `b = heap + 16 · old + off k τ` with `old + units k τ`
within the cells and the object's words `w = k · nWords us`; with the
arena's laws (`Arena.OK`: the units of an object that fits and its base
offset) and the object fitting the cells that is `AllocLand heap cells b w`, the allocation fragment's
(`msOfA`'s `xa`) and `AllocReach.Reach.step`'s premise.

- `allocLand_of_ea`: `AllocLand` from the landing's arithmetic.
-/
import Spike.Lib.Arena
import Spike.Lib.HeapLand

namespace Spike.Lib.AllocReach

open CoreLang CoreTerm
open Spike.Lib.HeapLand (AllocLand)

/-- **The landing of an object of `k · nWords us` words** at the old count
`old` (its base `b` past `16 · old` cells and its offset, `old` plus its
units within the cells) lands in the arena (`AllocLand`), under the arena's
laws (`Arena.OK`), the object fitting the cells (`hfit`: the laws constrain
the units of a fitting object only). -/
theorem allocLand_of_ea {ar : Arena} (hok : ar.OK) {k : Nat} {τ : Ty} {us : List TermRun.Acc}
    (hus : TermRun.accs (TermRun.close [] τ) = some us) {old b w : Nat}
    (hb : b = ar.heap + 16 * old + ar.off k τ) (hold : old + ar.units k τ ≤ ar.cells)
    (hw : w = k * TermRun.nWords us) (hfit : k * TermRun.nWords us + 1 ≤ ar.cells) :
    AllocLand ar.heap ar.cells b w := by
  have hu := hok.units k τ us hus hfit
  obtain ⟨-, h8, hoff⟩ := hok.off k τ us hus hfit
  subst hb hw
  refine ⟨by omega, by omega, by omega⟩

/--
info: 'Spike.Lib.AllocReach.allocLand_of_ea' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms allocLand_of_ea

end Spike.Lib.AllocReach
