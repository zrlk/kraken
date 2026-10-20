/-
Following a schedule through the machine: `runSched A fuel c is` takes, at
each step, the successor of the given index in `succs`; a run that ends in
`some c'` is a `Reachable` run (`runSched_reachable`). Used for the
non-vacuity witnesses of `SLR/SwpConcrete.lean` and
`SLR/X64SpinConcrete.lean`. ISA-neutral.
-/
import Kraken.Promising.Machine

namespace Kraken.Promising.SLR

open Kraken.Promising

/-- Follow a schedule: at each step the successor of the given index. -/
def runSched {I : ISA} (A : Arch) (fuel : Nat) : Config I → List Nat → Option (Config I)
  | c, [] => some c
  | c, i :: is => ((succs A c fuel).1[i]?).bind (runSched A fuel · is)

theorem runSched_reachable {I : ISA} {A : Arch} {fuel : Nat} :
    ∀ {c c' : Config I} {is : List Nat}, runSched A fuel c is = some c' → Reachable A fuel c c'
  | c, c', [], h => by cases h; exact .refl c
  | c, c', i :: is, h => by
    simp only [runSched, Option.bind_eq_some_iff] at h
    obtain ⟨c₁, h₁, h₂⟩ := h
    exact .step (List.mem_of_getElem? h₁) (runSched_reachable h₂)

end Kraken.Promising.SLR
