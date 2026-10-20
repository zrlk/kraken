/-
The value-restricted AArch64 lowering kit on `isaLSE2` and on the semantic
machines.

As `Lower/KitLSE2.lean` does for `Kit.lower_promising(_vals)`, this file
moves `KitVals.lower_promising_valsW` (executable machine of `isa`) to the
FEAT_LSE2 target `isaLSE2` once, for every `LowerThreadW` instance:

1. `lower_promising_valsWK`: the `#chaink_clone'` of the kit theorem, about
   `ReachableKF` (= `ReachableK isa`), with the clones of its proof's chain
   in `SLR/PromisePureVals.lean` (`promisePure_of_relWritesVK`, cloned once
   for both ISAs in `SLR/ChainK/ValsChainN.lean`) and
   `Lower/KitValsPure.lean` (`final_of_relPureSafelyFVPK`,
   `envGValsBridge_ofSpecsPK`), on the
   K twins of the generic purity and value chains. Proof texts are the
   source files', re-elaborated.
2. `lower_promising_valsW_lse2` and `_semInf`: `lower_promising_valsW`'s
   hypotheses, with `hH` along `ReachableK`, `hfree` (no 64-bit `LDP`/`STP`
   in any text) and `hfin` for every final configuration, give
   `Φ (ofL cfg)` for every final `cfg` of `isaLSE2` reachable on the
   executable and fuel-free semantic machines (a `ReachableSem` form is the
   same one-liner through `final_lse2_sem_of_K`).

x64 counterpart: `KitX.lower_promising_x64_vals` on the semantic machines
needs a K clone of `Vals.envGValsBridgeX_ofSpecs` (no LSE2 step there).
Limits: `Phase1TreeF`, and `NoLSE2Pairs` (`LSE2Final.lean`).
-/
import Kraken.Promising.Lower.KitVals
import Kraken.Promising.Lower.KitLSE2

open Kraken.Promising.Live.Bridge

#chaink_clone' "KitValsPure.lean"
  only ["final_of_relPureSafelyFVP", "envGValsBridge_ofSpecsP"]

#chaink_clone' "KitVals.lean"
  only ["lower_promising_valsW"]

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.KitVals

open Kraken.Promising.Lower.Kit (FinalReading)

variable {A : Arch} {states : List isa.State} {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost}
  {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop} {S : SharedEnv.Layout} {G : Loc → Val → Prop}

/-- Threads at their starts whose texts have no LSE2 pair start a
configuration with no LSE2 pair. -/
theorem noLSE2Pairs_of_startsW (T : ∀ tid, tid < states.length → LowerThreadW A tid g₀.rel B S G)
    {σ : Nat → EStateA} (hS : ∀ tid (h : tid < states.length), (T tid h).Start (σ tid) states[tid])
    (hfree : ∀ tid (h : tid < states.length), ∀ d ∈ (T tid h).p, d.LSE2Free) :
    ∀ s ∈ states, NoLSE2Pairs s.exe := by
  intro s hs
  obtain ⟨i, h, rfl⟩ := List.mem_iff_getElem.mp hs
  exact noLSE2Pairs_of_exe (hS i h).exe (hfree i h)

section LSE2

variable (A) (G)
  (hH : ∀ c, ReachableK A (Config.init states initMem) c → c.NTFree A)
  (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : g₀.pend = [])
  (hm0 : MemInv G (Config.init states initMem).mem)
  (T : ∀ tid, tid < states.length → LowerThreadW A tid g₀.rel B S G)
  (hS : ∀ tid (h : tid < states.length),
    (T tid h).Start (σInit (Config.init states initMem) (rF tid) g₀) states[tid])
  (hfree : ∀ tid (h : tid < states.length), ∀ d ∈ (T tid h).p, d.LSE2Free)
  (hfin : FinalReading states g₀ B Φ)

include hH hE hpend hm0 hS hfree hfin

/-- **The value-restricted lowering kit on `isaLSE2`** (executable machine):
the hypotheses of `lower_promising_valsW` (with `hH` along `ReachableK` and
`hfin` for every final configuration) and no LSE2 pair in any thread's text
give `Φ` (through `ofL`) of every final configuration of `isaLSE2` reachable
from the start. -/
theorem lower_promising_valsW_lse2 {fuel : Nat} {cfg : Config isaLSE2}
    (hc : Reachable A fuel (Config.init states initMem : Config isaLSE2) cfg) (hf : cfg.final = true) :
    Φ (ofL cfg) :=
  final_lse2_of_K (noLSE2Pairs_of_startsW T hS hfree)
    (fun c hK hfc => lower_promising_valsWK A 0 G hH hE hpend hm0 T hS hK hfc (hfin c hfc)) hc hf

/-- **`lower_promising_valsW_lse2`, fuel-free semantic machine**
(`ReachableSemInf`), the form the lowering consumes. -/
theorem lower_promising_valsW_lse2_semInf {cfg : Config isaLSE2}
    (hc : Live.Inf.ReachableSemInf A (Config.init states initMem : Config isaLSE2) cfg) (hf : cfg.final = true) :
    Φ (ofL cfg) :=
  final_lse2_semInf_of_K (noLSE2Pairs_of_startsW T hS hfree)
    (fun c hK hfc => lower_promising_valsWK A 0 G hH hE hpend hm0 T hS hK hfc (hfin c hfc)) hc hf

end LSE2

end Kraken.Promising.Lower.KitVals

#print axioms Kraken.Promising.Lower.KitVals.lower_promising_valsWK
#print axioms Kraken.Promising.Lower.KitVals.lower_promising_valsW_lse2
#print axioms Kraken.Promising.Lower.KitVals.lower_promising_valsW_lse2_semInf
