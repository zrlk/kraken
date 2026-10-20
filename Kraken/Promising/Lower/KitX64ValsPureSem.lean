/-
The x64 value bridge with value-restricted purity on the semantic machines.

`Vals.envGValsBridgeX_ofPure` (`Lower/KitX64ValsPure.lean`) is on the
executable machine (`Reachable Arch.tso fuel`). Here, as
`Lower/KitX64ValsSem.lean` does for `lower_promising_x64_vals`:

1. K clones (`#chaink_clone'`, statements about `ReachableKF` =
   `ReachableK`, proof texts re-elaborated from the source file), on the
   ISA-neutral clone `final_of_chainVPK` of `ChainK/ValsChainN.lean`:
   `final_of_relPureSafelyQX_tsoFVPK` and `envGValsBridgeX_ofPureK`.
2. `envGValsBridgeX_ofPure_sem` (`ReachableSem Arch.tso fuel`) and
   `envGValsBridgeX_ofPure_semInf` (`Live.Inf.ReachableSemInf Arch.tso`):
   `envGValsBridgeX_ofPure`'s hypotheses and conclusion, with only the
   machine changed (the `fuel` binder dropped in `_semInf`), by
   `ReachableK.of_reachableSem'` / `ReachableK.of_reachableSemInf` from the
   bounded start `Config.init_bnd`.

Program-generic: any x64 program whose purity specifications are judgments
in `relInvX S G` (for instance one with a call stack in `dmem`) gets the
semantic-machine forms from the same premises as the executable one. Scope
and limits: as for `envGValsBridgeX_ofPure` (phase-1 code, `Phase1TreeFX`).
-/
import Kraken.Promising.Lower.KitX64ValsPure
import Kraken.Promising.SLR.ChainK.ValsChainN
import Kraken.Promising.LiveSemInf

open Kraken.Promising.Live.Bridge

#chaink_clone' "KitX64ValsPure.lean"
  only ["final_of_relPureSafelyQX_tsoFVP", "envGValsBridgeX_ofPure"]

namespace Kraken.Promising.X64.EnvG.Vals

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64
open Kraken.Promising.X64.EnvG

/-- **The x64 bridge with value-restricted purity, semantic machine**
(`ReachableSem Arch.tso fuel`, `fuel` the certification fuel):
`envGValsBridgeX_ofPure`'s hypotheses and conclusion, with only the machine
changed. -/
theorem envGValsBridgeX_ofPure_sem {S : SharedEnv.Layout} (hS : Le16 S) (G : Loc → Val → Prop)
    {fuel : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    {pl : Nat → SLR.EnvG.Plan} {e : Nat → Kraken.Executable Directive} {endPc : Nat → Int64}
    {post : Nat → MachineState × EStateX → Prop}
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False) (hshape : ∀ tid, Phase1TreeFX (sp tid).e)
    (h0 : ∀ tid s, states[tid]? = some s → (sp tid).HoldsV G s)
    (hm0 : MemInv G (Config.init states initMem).mem)
    (hthr : ∀ tid, tid < states.length →
      Kraken.Executable.ValidLayout (e tid) ∧ (pl tid).Valid ∧ Phase1TreeFX (e tid) ∧
      (∀ y, post tid y → y.1.2 = endPc tid) ∧
      (∀ x R, x.1.2 = endPc tid → ¬ (e tid).instrStepEnv (EnvGCAdjXV Arch.tso tid (pl tid) S G) x R) ∧
      (∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post tid (t.st.st, σ) → t.prom = [] →
        EnvRel tid (pl tid) σ c t r g cl → cl → B c r g) ∧
      ∃ s, states[tid]? = some s ∧
        QX64CAdjV Arch.tso tid (pl tid) S G (e tid) (endPc tid) (post tid) s
          (σInitX (Config.init states initMem) (rF tid) g₀))
    {c : Config isa} (hc : ReachableSem Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  envGValsBridgeX_ofPureK (fuel := fuel) hS G hE hpend sp hshape h0 hm0 hthr
    (ReachableK.of_reachableSem' (Config.init_bnd _ _) hc) hf hfin

/-- **The x64 bridge with value-restricted purity, fuel-free semantic
machine** (`Live.Inf.ReachableSemInf Arch.tso`): `envGValsBridgeX_ofPure`'s
hypotheses (the `fuel` binder dropped) and conclusion, with only the machine
changed. -/
theorem envGValsBridgeX_ofPure_semInf {S : SharedEnv.Layout} (hS : Le16 S) (G : Loc → Val → Prop)
    {states : List isa.State} {initMem : List (Loc × Val)}
    {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    {pl : Nat → SLR.EnvG.Plan} {e : Nat → Kraken.Executable Directive} {endPc : Nat → Int64}
    {post : Nat → MachineState × EStateX → Prop}
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False) (hshape : ∀ tid, Phase1TreeFX (sp tid).e)
    (h0 : ∀ tid s, states[tid]? = some s → (sp tid).HoldsV G s)
    (hm0 : MemInv G (Config.init states initMem).mem)
    (hthr : ∀ tid, tid < states.length →
      Kraken.Executable.ValidLayout (e tid) ∧ (pl tid).Valid ∧ Phase1TreeFX (e tid) ∧
      (∀ y, post tid y → y.1.2 = endPc tid) ∧
      (∀ x R, x.1.2 = endPc tid → ¬ (e tid).instrStepEnv (EnvGCAdjXV Arch.tso tid (pl tid) S G) x R) ∧
      (∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post tid (t.st.st, σ) → t.prom = [] →
        EnvRel tid (pl tid) σ c t r g cl → cl → B c r g) ∧
      ∃ s, states[tid]? = some s ∧
        QX64CAdjV Arch.tso tid (pl tid) S G (e tid) (endPc tid) (post tid) s
          (σInitX (Config.init states initMem) (rF tid) g₀))
    {c : Config isa} (hc : Live.Inf.ReachableSemInf Arch.tso (Config.init states initMem) c)
    (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  envGValsBridgeX_ofPureK (fuel := 0) hS G hE hpend sp hshape h0 hm0 hthr
    (ReachableK.of_reachableSemInf (Config.init_bnd _ _) hc) hf hfin

end Kraken.Promising.X64.EnvG.Vals

#print axioms Kraken.Promising.X64.EnvG.Vals.final_of_relPureSafelyQX_tsoFVPK
#print axioms Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofPureK
#print axioms Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofPure_sem
#print axioms Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofPure_semInf
