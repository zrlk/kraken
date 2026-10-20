/-
**Stage 4: the concrete instance of
`x64_treiber2_termBoundSem_of_noEmptyRead`**: the `.kl` runner's executable
for `treiber2.kl` (`SLR/EnvG/X64Treiber2Concrete.lean`: layout
`treiber2LayoutV`, threads `treiber2P0`/`treiber2P1`, initial memory
`treiber2InitMemV`).

The theorem keeps the hypothesis `NoEmptyRead` (no pop reads an empty stack
at a reachable configuration); it is not discharged (`KNOWN_GAPS.md`). Not
covered: the runner's own declarations (`decls`), as in
`x64_treiber2_envG_verbatim_concrete` (`StartWV` asks for none).
-/
import Kraken.Promising.LiveTermX64Treiber2
import Kraken.Promising.SLR.EnvG.X64Treiber2Concrete

namespace Kraken.Promising.Live.TermX64Treiber2.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.Term
open Kraken.Promising.Live.TermX64Treiber2
open Kraken.Promising.X64.EnvG.Treiber2X (symT2)
open Kraken.Promising.X64.EnvG.Treiber2X.Concrete

section
attribute [local instance] treiber2LayoutV

/-- **The x64 `treiber2.kl` worker terminates, in the runner's executable,
given `NoEmptyRead`**: at every fuel at which no pop reads an empty stack
from the start, one bound on every semantic trace under `Arch.tso`. -/
theorem x64_treiber2_termBoundSem_concrete_of_noEmptyRead {fuel : Nat}
    (hne : NoEmptyRead fuel (Config.init [treiber2P0, treiber2P1] treiber2InitMemV)) :
    TermBoundSem Arch.tso fuel (Config.init [treiber2P0, treiber2P1] treiber2InitMemV : Config isa) :=
  x64_treiber2_termBoundSem_of_noEmptyRead (fun s hs => by
    have h0 : symT2 "n1" ≠ symT2 "top" := by rw [symT2_n1, symT2_top]; decide
    have h1 : symT2 "n2" ≠ symT2 "top" := by rw [symT2_n2, symT2_top]; decide
    rcases List.mem_cons.1 hs with e | hs
    · exact ⟨_, e ▸ treiber2P0_start, h0⟩
    rcases List.mem_cons.1 hs with e | hs
    · exact ⟨_, e ▸ treiber2P1_start, h1⟩
    · exact absurd hs List.not_mem_nil) hne

end

end Kraken.Promising.Live.TermX64Treiber2.Concrete

#print axioms Kraken.Promising.Live.TermX64Treiber2.Concrete.x64_treiber2_termBoundSem_concrete_of_noEmptyRead
