/-
**The lowering kit on `isaLSE2`.**

The lowering kit's kit (`Lower/Kit.lean`) proves the whole-program theorem of any
lowered AArch64 program once (`lower_promising`, frameless;
`lower_promising_vals`, with a `dmem` frame and the value bridge), on the
executable machine of `isa`. This file moves both to the FEAT_LSE2 target
`isaLSE2` once, so that **every kit instance gets its `isaLSE2` headline
with no per-program clone**:

1. `lower_promisingK`, `lower_promising_valsK`: the `#chaink_clone'` of the
   two kit theorems, the same statements about `ReachableKF`
   (= `ReachableK isa`), through `final_of_relPureSafelyFK` and
   `envGValsBridge_ofSpecsK` (`Lower/LSE2Final.lean`);
2. `lower_promising_lse2` (`_sem`, `_semInf`) and `lower_promising_vals_lse2`
   (`_sem`, `_semInf`): the kit's hypotheses, with
   - `hH` along `ReachableK` (under `Arch.armv8`: `fun _ h =>
     Config.ntFree_armv8K h`),
   - `hfree`: no thread's text has a 64-bit `LDP`/`STP` (per text, `by
     decide`),
   - `hfin` for every final configuration (the kit's `hfin` is for the one
     `c` at hand; an instance's final reading is proved for all `c` anyway),
   give `Φ (ofL cfg)` for every final configuration of `isaLSE2` reachable
   from the start on the executable, semantic and fuel-free semantic machines
   (`final_lse2_of_K` and its forms).

**Per program**: an instance that calls `lower_promising A fuel hH hE hpend T
hS hc hf (hfin c hf)` calls `lower_promising_lse2 A hH' hE hpend T hS hfree
hfin hc hf` instead (`hfree := fun tid h => by decide`-style, once per
text): one line, no clone, no restated proof.

Phase-1 limits apply as for the kit (`Phase1TreeF`), and the `NoLSE2Pairs`
limit of `LSE2Final.lean` (no 64-bit `LDP`/`STP` in any thread's text).
-/
import Kraken.Promising.Lower.Kit
import Kraken.Promising.Lower.LSE2Final

open Kraken.Promising.Live.Bridge

#chaink_clone' "Kit.lean"
  only ["lower_promising", "lower_promising_vals"]

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Kit

variable {A : Arch} {states : List isa.State} {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost}
  {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}

/-- Threads at their starts whose texts have no LSE2 pair start a
configuration with no LSE2 pair. -/
theorem noLSE2Pairs_of_startCs (T : ∀ tid, tid < states.length → LowerCore A tid g₀.rel B)
    (hS : ∀ tid (h : tid < states.length), (T tid h).StartC states[tid])
    (hfree : ∀ tid (h : tid < states.length), ∀ d ∈ (T tid h).p, d.LSE2Free) :
    ∀ s ∈ states, NoLSE2Pairs s.exe := by
  intro s hs
  obtain ⟨i, h, rfl⟩ := List.mem_iff_getElem.mp hs
  exact noLSE2Pairs_of_exe (hS i h).exe (hfree i h)

/-- The final reading of the kit, for every final configuration. -/
abbrev FinalReading (states : List isa.State) (g₀ : Ghost) (B : Config isa → Res → Ghost → Prop)
    (Φ : Config isa → Prop) : Prop :=
  ∀ c : Config isa, c.final = true → ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c →
    g₀.Le g' → c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c

section Frameless

variable (A) (hH : ∀ c, ReachableK A (Config.init states initMem) c → c.NTFree A)
  (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : g₀.pend = [])
  (T : ∀ tid, tid < states.length → LowerThread A tid g₀.rel B)
  (hS : ∀ tid (h : tid < states.length),
    (T tid h).Start (σInit (Config.init states initMem) (rF tid) g₀) states[tid])
  (hfree : ∀ tid (h : tid < states.length), ∀ d ∈ (T tid h).p, d.LSE2Free)
  (hfin : FinalReading states g₀ B Φ)

include hH hE hpend hS hfree hfin

/-- **The frameless lowering kit on `isaLSE2`** (executable machine): the
hypotheses of `lower_promising` (with `hH` along `ReachableK` and `hfin` for
every final configuration) and no LSE2 pair in any thread's text give `Φ`
(through `ofL`) of every final configuration of `isaLSE2` reachable from the
start. -/
theorem lower_promising_lse2 {fuel : Nat} {cfg : Config isaLSE2}
    (hc : Reachable A fuel (Config.init states initMem : Config isaLSE2) cfg) (hf : cfg.final = true) :
    Φ (ofL cfg) :=
  final_lse2_of_K (noLSE2Pairs_of_startCs (fun tid h => (T tid h).toLowerCore) (fun tid h => (hS tid h).toStartC)
    hfree) (fun c hK hfc => lower_promisingK A 0 hH hE hpend T hS hK hfc (hfin c hfc)) hc hf

/-- **`lower_promising_lse2`, semantic machine** (`ReachableSem`). -/
theorem lower_promising_lse2_sem {fuel : Nat} {cfg : Config isaLSE2}
    (hc : ReachableSem A fuel (Config.init states initMem : Config isaLSE2) cfg) (hf : cfg.final = true) :
    Φ (ofL cfg) :=
  final_lse2_sem_of_K (noLSE2Pairs_of_startCs (fun tid h => (T tid h).toLowerCore)
    (fun tid h => (hS tid h).toStartC) hfree)
    (fun c hK hfc => lower_promisingK A 0 hH hE hpend T hS hK hfc (hfin c hfc)) hc hf

/-- **`lower_promising_lse2`, fuel-free semantic machine**
(`ReachableSemInf`), the form the lowering consumes. -/
theorem lower_promising_lse2_semInf {cfg : Config isaLSE2}
    (hc : Live.Inf.ReachableSemInf A (Config.init states initMem : Config isaLSE2) cfg) (hf : cfg.final = true) :
    Φ (ofL cfg) :=
  final_lse2_semInf_of_K (noLSE2Pairs_of_startCs (fun tid h => (T tid h).toLowerCore)
    (fun tid h => (hS tid h).toStartC) hfree)
    (fun c hK hfc => lower_promisingK A 0 hH hE hpend T hS hK hfc (hfin c hfc)) hc hf

end Frameless

section Vals

variable (A) {S : SharedEnv.Layout} (G : Loc → Val → Prop)
  (hH : ∀ c, ReachableK A (Config.init states initMem) c → c.NTFree A)
  (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : g₀.pend = [])
  (hm0 : MemInv G (Config.init states initMem).mem)
  (T : ∀ tid, tid < states.length → LowerThreadV A tid g₀.rel B S G)
  (hS : ∀ tid (h : tid < states.length),
    (T tid h).Start (σInit (Config.init states initMem) (rF tid) g₀) states[tid])
  (hfree : ∀ tid (h : tid < states.length), ∀ d ∈ (T tid h).p, d.LSE2Free)
  (hfin : FinalReading states g₀ B Φ)

include hH hE hpend hm0 hS hfree hfin

/-- **The frame + value-bridge lowering kit on `isaLSE2`** (executable
machine): `lower_promising_lse2` for `LowerThreadV` threads, from `MemInv G`
of the initial memory in addition. -/
theorem lower_promising_vals_lse2 {fuel : Nat} {cfg : Config isaLSE2}
    (hc : Reachable A fuel (Config.init states initMem : Config isaLSE2) cfg) (hf : cfg.final = true) :
    Φ (ofL cfg) :=
  final_lse2_of_K (noLSE2Pairs_of_startCs (fun tid h => (T tid h).toLowerCore)
    (fun tid h => (hS tid h).toStartC) hfree)
    (fun c hK hfc => lower_promising_valsK A 0 G hH hE hpend hm0 T hS hK hfc (hfin c hfc)) hc hf

/-- **`lower_promising_vals_lse2`, semantic machine** (`ReachableSem`). -/
theorem lower_promising_vals_lse2_sem {fuel : Nat} {cfg : Config isaLSE2}
    (hc : ReachableSem A fuel (Config.init states initMem : Config isaLSE2) cfg) (hf : cfg.final = true) :
    Φ (ofL cfg) :=
  final_lse2_sem_of_K (noLSE2Pairs_of_startCs (fun tid h => (T tid h).toLowerCore)
    (fun tid h => (hS tid h).toStartC) hfree)
    (fun c hK hfc => lower_promising_valsK A 0 G hH hE hpend hm0 T hS hK hfc (hfin c hfc)) hc hf

/-- **`lower_promising_vals_lse2`, fuel-free semantic machine**
(`ReachableSemInf`), the form the lowering consumes. -/
theorem lower_promising_vals_lse2_semInf {cfg : Config isaLSE2}
    (hc : Live.Inf.ReachableSemInf A (Config.init states initMem : Config isaLSE2) cfg) (hf : cfg.final = true) :
    Φ (ofL cfg) :=
  final_lse2_semInf_of_K (noLSE2Pairs_of_startCs (fun tid h => (T tid h).toLowerCore)
    (fun tid h => (hS tid h).toStartC) hfree)
    (fun c hK hfc => lower_promising_valsK A 0 G hH hE hpend hm0 T hS hK hfc (hfin c hfc)) hc hf

end Vals

end Kraken.Promising.Lower.Kit

#print axioms Kraken.Promising.Lower.Kit.lower_promising_lse2
#print axioms Kraken.Promising.Lower.Kit.lower_promising_lse2_sem
#print axioms Kraken.Promising.Lower.Kit.lower_promising_lse2_semInf
#print axioms Kraken.Promising.Lower.Kit.lower_promising_vals_lse2
#print axioms Kraken.Promising.Lower.Kit.lower_promising_vals_lse2_sem
#print axioms Kraken.Promising.Lower.Kit.lower_promising_vals_lse2_semInf
