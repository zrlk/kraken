/-
**`pilot2_promising` on `isaLSE2`.**

The unconditional stack-frame pilot's unconditional `pilot2_promising` (`Lower/Pilot2ValsWhole.lean`, the
Treiber client with a `dmem` frame) moved to the FEAT_LSE2 target by the
generic route of `Lower/LSE2Final.lean`:

1. `pilot2_promisingK`, the `#chaink_clone'` of `pilot2_promising`: the same
   statement, elaborated from the same source, about `ReachableKF`
   (= `ReachableK isa`); its value bridge is `envGValsBridge_ofSpecsK`
   (`LSE2Final.lean`);
2. `pilot2` has no 64-bit `LDP`/`STP` (`pilot2_lse2Free`, by `decide`);
3. `final_lse2_of_K` and its semantic forms give the conclusion for every
   final configuration of `isaLSE2` reachable from the start (read through
   `ofL`, which copies the threads and memory unchanged).

Phase-1 limits apply as for `pilot2_promising` (`Phase1TreeF`).
-/
import Kraken.Promising.Lower.Pilot2ValsWhole
import Kraken.Promising.Lower.LSE2Final

open Kraken.Promising.Live.Bridge

#chaink_clone' "Pilot2ValsWhole.lean"
  only ["pilot2_promising"]

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.Variant

namespace Kraken.Promising.Lower.Pilot2

open Kraken.Promising.SLR.EnvG.Treiber2

/-- **`pilot2` has no LSE2 pair** (no 64-bit `LDP`/`STP`). -/
theorem pilot2_lse2Free : ∀ d ∈ pilot2, d.LSE2Free := by decide

section Whole

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilot2)]

omit [Executable.ValidLayout (layout pilot2)] in
/-- The two start states run executables with no LSE2 pair. -/
theorem noLSE2Pairs_start2 {P : Params} {d0 d1 : BitVec 32} {lo0 lo1 : BitVec 64} {nb0 nb1 : Nat}
    {s0 s1 : isa.State} (h0 : StartP2 P 0 d0 lo0 nb0 s0) (h1 : StartP2 P 1 d1 lo1 nb1 s1) :
    ∀ s ∈ [s0, s1], NoLSE2Pairs s.exe :=
  noLSE2Pairs_pair (noLSE2Pairs_of_exe h0.exe pilot2_lse2Free) (noLSE2Pairs_of_exe h1.exe pilot2_lse2Free)

/-- **`pilot2_promising` on `isaLSE2`** (AArch64 with FEAT_LSE2,
`Arch.armv8`, the executable machine): for the hypotheses of
`pilot2_promising`, every final configuration of `isaLSE2` reachable from the
two start states satisfies `Treiber2DFinal n0 n1` (read in `Config isa`
through `ofL`). -/
theorem pilot2_promising_lse2 {t n0 n1 : BitVec 64} {fuel : Nat}
    (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} {lo0 lo1 : BitVec 64} {nb0 nb1 : Nat}
    (h0 : StartP2 (tPD t n0 n1) 0 1 lo0 nb0 s0) (h1 : StartP2 (tPD t n0 n1) 1 2 lo1 nb1 s1)
    (hT0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨n0 + 8, 8⟩ = 0)
    (hN1 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨n1 + 8, 8⟩ = 0)
    {cfg : Config isaLSE2} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 (ofL cfg) :=
  final_lse2_of_K (noLSE2Pairs_start2 h0 h1)
    (fun _ hK hf => pilot2_promisingK (fuel := 0) ht0 ht1 hn hn0 hn1 h0 h1 hT0 hN0 hN1 hK hf) hc hf

/-- **`pilot2_promising` on `isaLSE2`, semantic machine** (`ReachableSem`). -/
theorem pilot2_promising_lse2_sem {t n0 n1 : BitVec 64} {fuel : Nat}
    (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} {lo0 lo1 : BitVec 64} {nb0 nb1 : Nat}
    (h0 : StartP2 (tPD t n0 n1) 0 1 lo0 nb0 s0) (h1 : StartP2 (tPD t n0 n1) 1 2 lo1 nb1 s1)
    (hT0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨n0 + 8, 8⟩ = 0)
    (hN1 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨n1 + 8, 8⟩ = 0)
    {cfg : Config isaLSE2} (hc : ReachableSem Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 (ofL cfg) :=
  final_lse2_sem_of_K (noLSE2Pairs_start2 h0 h1)
    (fun _ hK hf => pilot2_promisingK (fuel := 0) ht0 ht1 hn hn0 hn1 h0 h1 hT0 hN0 hN1 hK hf) hc hf

/-- **`pilot2_promising` on `isaLSE2`, fuel-free semantic machine**
(`ReachableSemInf`), the form the lowering consumes. -/
theorem pilot2_promising_lse2_semInf {t n0 n1 : BitVec 64}
    (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} {lo0 lo1 : BitVec 64} {nb0 nb1 : Nat}
    (h0 : StartP2 (tPD t n0 n1) 0 1 lo0 nb0 s0) (h1 : StartP2 (tPD t n0 n1) 1 2 lo1 nb1 s1)
    (hT0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨n0 + 8, 8⟩ = 0)
    (hN1 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨n1 + 8, 8⟩ = 0)
    {cfg : Config isaLSE2}
    (hc : Live.Inf.ReachableSemInf Arch.armv8 (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 (ofL cfg) :=
  final_lse2_semInf_of_K (noLSE2Pairs_start2 h0 h1)
    (fun _ hK hf => pilot2_promisingK (fuel := 0) ht0 ht1 hn hn0 hn1 h0 h1 hT0 hN0 hN1 hK hf) hc hf

end Whole

section
attribute [local instance] pLayout2

/-- **Non-vacuity**: `pilot2_promising_lse2` at the explorer's configuration
of `pilot2_promising_concrete'` (`top` at `0x1000`, arenas at
`0x2000`/`0x3000`, payloads `1`/`2`, stacks `[0x8000, 0x8040)` and
`[0x9000, 0x9040)`), on `isaLSE2`. -/
theorem pilot2_promising_lse2_concrete {fuel : Nat} {c : Config isaLSE2}
    (hc : Reachable Arch.armv8 fuel
      (Config.init [thread2 0x2000 1 0x8040, thread2 0x3000 2 0x9040] Pilot.initMem : Config isaLSE2) c)
    (hf : c.final = true) : Treiber2DFinal 0x2000 0x3000 (ofL c) :=
  pilot2_promising_lse2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (thread2_start _ _ _ _ rfl (by decide) (by decide) (by decide) (heap_far (.inl (by decide))))
    (thread2_start _ _ _ _ rfl (by decide) (by decide) (by decide) (heap_far (.inr (by decide))))
    (by simp only [Config.init_mem]; decide) (by simp only [Config.init_mem]; decide)
    (by simp only [Config.init_mem]; decide) hc hf

end

end Kraken.Promising.Lower.Pilot2

#print axioms Kraken.Promising.Lower.Pilot2.pilot2_promising_lse2
#print axioms Kraken.Promising.Lower.Pilot2.pilot2_promising_lse2_sem
#print axioms Kraken.Promising.Lower.Pilot2.pilot2_promising_lse2_semInf
#print axioms Kraken.Promising.Lower.Pilot2.pilot2_promising_lse2_concrete
