/-
**The x64 lowering kit on the semantic machines.**
ISA: x64 (`isa`); `Arch.tso`.

`KitX.lower_promising_x64` (`Lower/KitX64.lean`) is on the executable
machine (`Reachable Arch.tso fuel`). Here, as `Lower/KitLSE2.lean` does for
the AArch64 kit:

1. `lower_promising_x64K`: the `#chaink_clone'` of the kit theorem, the same
   statement about `ReachableKF Arch.tso fuel` (= `ReachableK Arch.tso`),
   through the K clone `CmpxPublic.final_of_relPureSafelyQX_tsoF'K`
   (`ChainK/TwinsCloneX64a.lean`); the proof text is `KitX64.lean`'s,
   re-elaborated (nothing restated by hand);
2. `lower_promising_x64_sem` (`ReachableSem Arch.tso fuel`, the semantic
   machine) and `lower_promising_x64_semInf`
   (`Live.Inf.ReachableSemInf Arch.tso`, the fuel-free semantic machine the
   WeakCore lowering consumes): `lower_promising_x64`'s hypotheses and
   conclusion verbatim, with only the machine changed, by the generic
   transfers `ReachableK.of_reachableSem'` / `ReachableK.of_reachableSemInf`
   from the bounded start `Config.init_bnd` (the route of the x64
   `#sem_twin`/`#inf_twin` twins, `ChainK/SemTwin.lean`, `ChainK/InfTwin.lean`).

Only the frameless kit is moved: every x64 pilot uses it. The frame +
value-bridge variant `lower_promising_x64_vals` would need a K clone of
`Vals.envGValsBridgeX_ofSpecs` (not done).

Scope and phase-1 limits: as for `lower_promising_x64` (see `KitX64.lean`).
-/
import Kraken.Promising.Lower.KitX64
import Kraken.Promising.SLR.ChainK.TwinsCloneX64a
import Kraken.Promising.LiveSemInf

open Kraken.Promising.Live.Bridge

#chaink_clone' "KitX64.lean"
  only ["lower_promising_x64"]

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.KitX

/-- **The frameless x64 lowering kit, semantic machine** (`ReachableSem
Arch.tso fuel`, `fuel` the certification fuel): `lower_promising_x64`'s
hypotheses and conclusion, with only the machine changed. -/
theorem lower_promising_x64_sem (fuel : Nat) {states : List isa.State} {initMem : List (Loc × Val)}
    {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    {S : SharedEnv.Layout} (hS : Le16 S)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : g₀.pend = [])
    (T : ∀ tid, tid < states.length → LowerThreadX tid S B)
    (hT : ∀ tid (h : tid < states.length),
      (T tid h).Start (σInitX (Config.init states initMem) (rF tid) g₀) states[tid])
    {c : Config isa} (hc : ReachableSem Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  lower_promising_x64K fuel hS hE hpend T hT (ReachableK.of_reachableSem' (Config.init_bnd _ _) hc) hf hfin

/-- **The frameless x64 lowering kit, fuel-free semantic machine**
(`Live.Inf.ReachableSemInf Arch.tso`), the form the WeakCore lowering
consumes: `lower_promising_x64`'s hypotheses (the `fuel` binder dropped) and
conclusion, with only the machine changed. -/
theorem lower_promising_x64_semInf {states : List isa.State} {initMem : List (Loc × Val)}
    {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    {S : SharedEnv.Layout} (hS : Le16 S)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : g₀.pend = [])
    (T : ∀ tid, tid < states.length → LowerThreadX tid S B)
    (hT : ∀ tid (h : tid < states.length),
      (T tid h).Start (σInitX (Config.init states initMem) (rF tid) g₀) states[tid])
    {c : Config isa} (hc : Live.Inf.ReachableSemInf Arch.tso (Config.init states initMem) c)
    (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  lower_promising_x64K 0 hS hE hpend T hT (ReachableK.of_reachableSemInf (Config.init_bnd _ _) hc) hf hfin

end Kraken.Promising.Lower.KitX

#print axioms Kraken.Promising.Lower.KitX.lower_promising_x64K
#print axioms Kraken.Promising.Lower.KitX.lower_promising_x64_sem
#print axioms Kraken.Promising.Lower.KitX.lower_promising_x64_semInf
