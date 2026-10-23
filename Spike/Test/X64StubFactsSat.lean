/-
**`Spike/Lib/X64StubFacts.lean` on `overflow.w`'s addition** (`cOvf`,
`Spike/Test/OvfAbortSat.lean`): its control without the environment has
`CFacts` at every layout and placement, and the abort facts at the overflow
site hold for an `exit_group` with the abort status.
-/
import Spike.Lib.X64StubFacts
import Spike.Test.OvfAbortSat

namespace Spike.Test.X64StubFactsSat

open CoreLang CoreTerm Spike.Lib Spike.Lib.X64Consumer Spike.Test.OvfAbortSat
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64

example (Λ : Scc.Sem.Layout) (lbl : Lbl) : CFacts Λ lbl (noEnv cOvf) := cfacts_noEnv cOvf_ok.1

example : (noEnv cOvf).env = [] ∧ (noEnv cOvf).term = cOvf.term := ⟨rfl, rfl⟩

example (μ : Marks) (s : State) (hk : ∀ k a, μ.abortAt k = some a → pcOf s = a → k = .overflow)
    (hd : Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup 101)) :
    ∀ k a, μ.abortAt k = some a → pcOf s = a → k = .overflow ∧ OvfReady cOvf ∧ EnvSmall cOvf.env ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus :=
  abortOk_ovf hk cOvf_ok.1 cOvf_ok.2 fun v hv => by
    rw [hd] at hv; cases hv; rfl

end Spike.Test.X64StubFactsSat
