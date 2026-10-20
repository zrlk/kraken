/-
**Part 3: adequacy for x64 programs with
taking threads** (the x64 counterpart of `EnvG/TakeFinal.lean`, which
imports `RelPureEnvA64` and so cannot serve x64 files).

- `final_of_relWritesJSX`: an alias (formerly a verbatim copy) of the ISA-neutral
  `SLR.final_of_relWritesJS` (`EnvG/TakeFinal.lean`): `final_of_relWritesJ`
  at `NPSafeP … G₀ (K2Scope AllocIds)`, through `theorem1IIPure_G₀_S`.
- **`final_of_relPureSafelyQX_tsoS`**: `final_of_relPureSafelyQX_tso`
  (`EnvG/RelPureEnvX64.lean`) at `NPSafeP … G₀ (K2Scope AllocIds)`: one
  all-release specification per thread (`RelPureSpecQX Arch.tso (fun _ _ =>
  False)`) gives the scope `NTFree Arch.tso` and purity for any ghost at once
  (under `Arch.tso` every plain store is a release; a take never changes
  `rel`, so no take-specific purity is needed, as on AArch64).

`final_of_relWritesJS` now lives in the ISA-neutral
`EnvG/TakeFinalCommon.lean`; `final_of_relWritesJSX` is an alias of it.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnvX64
import Kraken.Promising.SLR.EnvG.TakeFinalCommon
import Kraken.Promising.SLR.EnvG.Alias
import Kraken.Promising.SLR.TakeRuleThread
import Kraken.Promising.SLR.Theorem1FinalP

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike

/-! `final_of_relWritesJSX` was a verbatim local copy of the ISA-neutral
`SLR.final_of_relWritesJS`; that theorem is in
`EnvG/TakeFinalCommon.lean` and this name is its alias (`hoist_alias`, same
statement). -/

hoist_alias [Kraken.Promising.SLR.final_of_relWritesJS ↦ Kraken.Promising.X64.EnvG.final_of_relWritesJSX]

/-- **Adequacy for x64 programs with taking threads under `Arch.tso`**:
`final_of_relPureSafelyQX_tso` at `NPSafeP … G₀ (K2Scope AllocIds)`. -/
theorem final_of_relPureSafelyQX_tsoS (fuel : Nat) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop}
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False) (h0 : ∀ tid s, states[tid]? = some s → (sp tid).Holds s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeP (model isa) Arch.tso B tid G₀ (K2Scope (model isa) AllocIds) n m True (Config.init states initMem)
        (rF tid) g₀)
    {c : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  have hs : ∀ s ∈ states, ∃ tid, (sp tid).Holds s := fun s hs => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
    exact ⟨i, h0 i _ (List.getElem?_eq_getElem hi)⟩
  exact final_of_relWritesJSX Arch.tso fuel (fun _ hc' => Config.ntFree_of_noNTInv (noNTInv_of_specQX sp) hs hc')
    hE hpend (fun tid st => (sp tid).Holds st)
    (fun tid _ tree h hex => ⟨EvTree.NoNT.relWrites tso_storeKind_rel
      (EvTree.noNT_tso_of_relWrites_false (relPureSpecQX_step (sp tid) h tree hex).1),
      (relPureSpecQX_step (sp tid) h tree hex).2⟩) h0 hsafe hc hf hfin

end Kraken.Promising.X64.EnvG

#print axioms Kraken.Promising.X64.EnvG.final_of_relWritesJSX
#print axioms Kraken.Promising.X64.EnvG.final_of_relPureSafelyQX_tsoS
