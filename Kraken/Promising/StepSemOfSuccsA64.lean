/-
**Executable ⊆ semantic for AArch64, binder-free.**
`stepSemOfSuccs` and `reachableSem_of_reachable'` (`StepSemOfSuccs.lean`)
at `Arch.armv8` and the AArch64 ISA, whose `ISA.LawfulState` instance is in
`CertifyAArch64.lean`: every executable reachability fact (reach theorems,
witnesses) for AArch64 programs from a bounded start, e.g. `Config.init`, is a
reachability fact of the semantic machine at the same fuel.
-/
import Kraken.Promising.StepSemOfSuccs
import Kraken.Promising.CertifyAArch64

namespace Kraken.Promising.Live.Bridge

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem

/-- **Executable ⊆ semantic** (one step) for AArch64. -/
theorem stepSemOfSuccs_a64 : StepSemOfSuccs Arch.armv8 AArch64.isa :=
  stepSemOfSuccs Arch.armv8

/-- **Executable reachability is semantic reachability** for AArch64, from a
bounded configuration. -/
theorem reachableSem_of_reachable_a64 {fuel : Nat} {c c' : Config AArch64.isa} (hb : c.Bnd)
    (h : Reachable Arch.armv8 fuel c c') : ReachableSem Arch.armv8 fuel c c' :=
  reachableSem_of_reachable' hb h

/-- **Executable reachability from an initial configuration is semantic
reachability** for AArch64. -/
theorem reachableSem_of_reachable_init_a64 {fuel : Nat} (states : List AArch64.isa.State)
    (initMem : List (Loc × Val)) {c' : Config AArch64.isa}
    (h : Reachable Arch.armv8 fuel (Config.init states initMem) c') :
    ReachableSem Arch.armv8 fuel (Config.init states initMem) c' :=
  reachableSem_of_reachable' (Config.init_bnd states initMem) h

end Kraken.Promising.Live.Bridge
