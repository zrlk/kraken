/-
The value-restricted x64 lowering kit on the semantic machines.

`KitX.lower_promising_x64_vals` (`Lower/KitX64.lean`) is on the executable
machine (`Reachable Arch.tso fuel`). Here, as `Lower/KitX64Sem.lean` does for
the frameless kit:

1. K clones (`#chaink_clone'`, statements about `ReachableKF` =
   `ReachableK`, proof texts re-elaborated from the source files), on the
   ISA-neutral value chain clone of `ChainK/ValsChainN.lean`
   (`promiseFresh_of_allInvK`, `theorem1FChainVK`, `final_of_chainVK`):
   - the x64 value bridge of `EnvG/ValsX64.lean`
     (`final_of_relPureSafelyQX_tsoFVK`, `envGValsBridgeX_ofSpecsK`);
   - the kit theorem itself (`lower_promising_x64_valsK`).
2. `lower_promising_x64_vals_sem` (`ReachableSem Arch.tso fuel`) and
   `lower_promising_x64_vals_semInf` (`Live.Inf.ReachableSemInf Arch.tso`):
   `lower_promising_x64_vals`'s hypotheses and conclusion, with only the
   machine changed, by `ReachableK.of_reachableSem'` /
   `ReachableK.of_reachableSemInf` from the bounded start `Config.init_bnd`.

No program instantiates `lower_promising_x64_vals` yet (the x64
pilots use the frameless kit, `Lower/PilotsX64Sem.lean`), so there is no
instance to move here; a program built with `LowerThreadXV.ofFrag`
(`Lower/KitFragX.lean`) gets both forms by the same arguments.

Scope and limits: as for `lower_promising_x64_vals` (unrestricted purity
judgments, `Phase1TreeFX`; see `KitX64.lean`).
-/
import Kraken.Promising.Lower.KitX64
import Kraken.Promising.SLR.ChainK.TwinsCloneX64a
import Kraken.Promising.SLR.ChainK.ValsChainN
import Kraken.Promising.LiveSemInf

open Kraken.Promising.Live.Bridge

#chaink_clone' "../SLR/EnvG/ValsX64.lean"
  only ["final_of_relPureSafelyQX_tsoFV", "envGValsBridgeX_ofSpecs"]

#chaink_clone' "KitX64.lean"
  only ["lower_promising_x64_vals"]

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.KitX

/-- **The frame + value-bridge x64 lowering kit, semantic machine**
(`ReachableSem Arch.tso fuel`, `fuel` the certification fuel):
`lower_promising_x64_vals`'s hypotheses and conclusion, with only the machine
changed. -/
theorem lower_promising_x64_vals_sem (fuel : Nat) {states : List isa.State} {initMem : List (Loc × Val)}
    {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    {S : SharedEnv.Layout} (hS : Le16 S) (G : Loc → Val → Prop)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : g₀.pend = [])
    (hm0 : MemInv G (Config.init states initMem).mem)
    (T : ∀ tid, tid < states.length → LowerThreadXV tid S B G)
    (hT : ∀ tid (h : tid < states.length),
      (T tid h).Start (σInitX (Config.init states initMem) (rF tid) g₀) states[tid])
    {c : Config isa} (hc : ReachableSem Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  lower_promising_x64_valsK fuel hS G hE hpend hm0 T hT (ReachableK.of_reachableSem' (Config.init_bnd _ _) hc) hf
    hfin

/-- **The frame + value-bridge x64 lowering kit, fuel-free semantic machine**
(`Live.Inf.ReachableSemInf Arch.tso`), the form the WeakCore lowering
consumes: `lower_promising_x64_vals`'s hypotheses (the `fuel` binder dropped)
and conclusion, with only the machine changed. -/
theorem lower_promising_x64_vals_semInf {states : List isa.State} {initMem : List (Loc × Val)}
    {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    {S : SharedEnv.Layout} (hS : Le16 S) (G : Loc → Val → Prop)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : g₀.pend = [])
    (hm0 : MemInv G (Config.init states initMem).mem)
    (T : ∀ tid, tid < states.length → LowerThreadXV tid S B G)
    (hT : ∀ tid (h : tid < states.length),
      (T tid h).Start (σInitX (Config.init states initMem) (rF tid) g₀) states[tid])
    {c : Config isa} (hc : Live.Inf.ReachableSemInf Arch.tso (Config.init states initMem) c)
    (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  lower_promising_x64_valsK 0 hS G hE hpend hm0 T hT (ReachableK.of_reachableSemInf (Config.init_bnd _ _) hc) hf
    hfin

end Kraken.Promising.Lower.KitX

#print axioms Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofSpecsK
#print axioms Kraken.Promising.Lower.KitX.lower_promising_x64_valsK
#print axioms Kraken.Promising.Lower.KitX.lower_promising_x64_vals_sem
#print axioms Kraken.Promising.Lower.KitX.lower_promising_x64_vals_semInf
