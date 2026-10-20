/-
**Executable ⊆ semantic for x64, binder-free.**
`stepSemOfSuccs` and `reachableSem_of_reachable'` (`StepSemOfSuccs.lean`)
at `Arch.tso` and the x64 ISA, whose `ISA.LawfulState` instance is in
`CertifyX64.lean`: every executable reachability fact (reach theorems,
witnesses) for x64 programs from a bounded start, e.g. `Config.init`, is a
reachability fact of the semantic machine at the same fuel.
-/
import Kraken.Promising.StepSemOfSuccs
import Kraken.Promising.CertifyX64

namespace Kraken.Promising.Live.Bridge

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem

/-- **Executable ⊆ semantic** (one step) for x64. -/
theorem stepSemOfSuccs_x64 : StepSemOfSuccs Arch.tso X64.isa :=
  stepSemOfSuccs Arch.tso

/-- **Executable reachability is semantic reachability** for x64, from a
bounded configuration. -/
theorem reachableSem_of_reachable_x64 {fuel : Nat} {c c' : Config X64.isa} (hb : c.Bnd)
    (h : Reachable Arch.tso fuel c c') : ReachableSem Arch.tso fuel c c' :=
  reachableSem_of_reachable' hb h

/-- **Executable reachability from an initial configuration is semantic
reachability** for x64. -/
theorem reachableSem_of_reachable_init_x64 {fuel : Nat} (states : List X64.isa.State)
    (initMem : List (Loc × Val)) {c' : Config X64.isa}
    (h : Reachable Arch.tso fuel (Config.init states initMem) c') :
    ReachableSem Arch.tso fuel (Config.init states initMem) c' :=
  reachableSem_of_reachable' (Config.init_bnd states initMem) h

end Kraken.Promising.Live.Bridge
