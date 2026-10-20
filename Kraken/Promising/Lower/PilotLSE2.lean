/-
**Part A3: `pilot_promising` on `isaLSE2`.**

The WeakCore lowering target is `isaLSE2` (FEAT_LSE2). The pilot has no
`LDP`/`STP` (`pilot_lse2Free`, by `decide`), so every thread state of a run
from `StartP` runs an executable with no LSE2 pair (`GoodL`), on which `isa`
and `isaLSE2` take the same steps (`Lower/LSE2Transfer.lean`).

`pilot_promising` is a theorem about the executable machine (`Reachable`,
`succs`) of `isa`, and `Reachable` itself is not transferred (see
`LSE2Transfer.lean`). The transfer goes through the K world instead:

1. `pilot_promisingK`, the `#chaink_clone` of `pilot_promising`: the same
   statement, elaborated from the same source, about `ReachableK isa` (which
   contains both machines' reachability);
2. a `Reachable` run of `isaLSE2` from the start is a `ReachableK` run of
   `isa` (`reachableK_of_reachable_lse2`), and a semantic (`ReachableSem`) one
   is too (`reachableSem_ofL` and `ReachableK.of_reachableSem'`);
3. `pilot_promising_lse2`, `pilot_promising_lse2_sem`: the conclusion of
   `pilot_promising` for every final configuration of `isaLSE2` reachable
   from the start, read through `ofL` (the field-by-field copy into
   `Config isa`; it changes no data).
-/
import Kraken.Promising.Lower.PilotWhole
import Kraken.Promising.Lower.LSE2Transfer
import Kraken.Promising.SLR.ChainK.TwinsCloneA64a

open Kraken.Promising.Live.Bridge

#chaink_clone' "PilotWhole.lean"
  only ["pilot_promising"]

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.Variant

namespace Kraken.Promising.Lower.Pilot

open Kraken.Promising.SLR.EnvG.Treiber2

/-- **The pilot has no LSE2 pair** (no 64-bit `LDP`/`STP`). -/
theorem pilot_lse2Free : ∀ d ∈ pilot, d.LSE2Free := by decide

/-- The two start states run executables with no LSE2 pair. -/
theorem goodC_start (l0 l1 : _root_.Layout) {t n0 n1 : BitVec 64} {s0 s1 : isa.State}
    (h0 : StartP (layout := l0) t n0 1 s0) (h1 : StartP (layout := l1) t n1 2 s1) (initMem : List (Loc × Val)) :
    GoodC GoodL (Config.init [s0, s1] initMem : Config isa) := by
  obtain ⟨he0, -⟩ := h0
  obtain ⟨he1, -⟩ := h1
  refine goodC_init (fun s hs => ?_) initMem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · show NoLSE2Pairs s.exe
    rw [he0]; exact noLSE2Pairs_apply l0 pilot_lse2Free
  · show NoLSE2Pairs s.exe
    rw [he1]; exact noLSE2Pairs_apply l1 pilot_lse2Free

/-- **`pilot_promising` on `isaLSE2`** (AArch64 with FEAT_LSE2, `Arch.armv8`,
the executable machine): for the hypotheses of `pilot_promising`, every final
configuration of `isaLSE2` reachable from the two start states satisfies
`Treiber2DFinal n0 n1` (read in `Config isa` through `ofL`, which copies the
threads and memory unchanged). -/
theorem pilot_promising_lse2 {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 pilot)]
    [Executable.ValidLayout (l1 pilot)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartP (layout := l0) t n0 1 s0) (h1 : StartP (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isaLSE2} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 (ofL cfg) := by
  have hg := goodC_start l0 l1 h0 h1 initMem
  have hc' : Reachable Arch.armv8 fuel (toL (Config.init [s0, s1] initMem)) cfg := (toL_init _ _).symm ▸ hc
  have hK := reachableK_of_reachable_lse2 hg hc'
  exact pilot_promisingK (fuel := 0) l0 l1 t n0 n1 ht0 ht1 hn hn0 hn1 h0 h1 hT0 hK
    (final_ofL_of_reachableK hg (ReachableK.of_reachable (I := isaLSE2) hc') hf)

/-- **`pilot_promising` on `isaLSE2`, semantic machine** (`ReachableSem`:
certification within `fuel` instructions, no `certify` search). -/
theorem pilot_promising_lse2_sem {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 pilot)]
    [Executable.ValidLayout (l1 pilot)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartP (layout := l0) t n0 1 s0) (h1 : StartP (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isaLSE2} (hc : ReachableSem Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 (ofL cfg) := by
  have hg := goodC_start l0 l1 h0 h1 initMem
  have hc' : ReachableSem Arch.armv8 fuel (toL (Config.init [s0, s1] initMem)) cfg := (toL_init _ _).symm ▸ hc
  have hK := ReachableK.of_reachableSem' (Config.init_bnd _ _) (reachableSem_ofL hg hc')
  have hKL : ReachableK Arch.armv8 (toL (Config.init [s0, s1] initMem)) cfg :=
    (toL_init _ _).symm ▸ ReachableK.of_reachableSem' (Config.init_bnd _ _) hc
  exact pilot_promisingK (fuel := 0) l0 l1 t n0 n1 ht0 ht1 hn hn0 hn1 h0 h1 hT0 hK (final_ofL_of_reachableK hg hKL hf)

/-- **`pilot_promising` on `isaLSE2`, fuel-free semantic machine**
(`ReachableSemInf`: unbounded certification), the form the lowering
consumes. -/
theorem pilot_promising_lse2_semInf (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 pilot)]
    [Executable.ValidLayout (l1 pilot)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartP (layout := l0) t n0 1 s0) (h1 : StartP (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isaLSE2} (hc : Live.Inf.ReachableSemInf Arch.armv8 (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 (ofL cfg) := by
  obtain ⟨fuel, hc⟩ := Live.Inf.reachableSemInf_iff.mp hc
  exact pilot_promising_lse2_sem (fuel := fuel) l0 l1 t n0 n1 ht0 ht1 hn hn0 hn1 h0 h1 hT0 hc hf

/-- **Non-vacuity**: `pilot_promising_lse2` at the explorer's configuration
(`PilotProg.lean`'s `exploreFinals true` runs this machine). -/
theorem pilot_promising_lse2_concrete {fuel : Nat} {c : Config isaLSE2}
    (hc : Reachable Arch.armv8 fuel (Config.init [thread 0x2000 1, thread 0x3000 2] initMem : Config isaLSE2) c)
    (hf : c.final = true) : Treiber2DFinal 0x2000 0x3000 (ofL c) :=
  pilot_promising_lse2 pLayout pLayout 0x1000 0x2000 0x3000 (by decide) (by decide) (by decide) (by decide)
    (by decide) (thread_start _ _ _ _ rfl (by decide) (by decide))
    (thread_start _ _ _ _ rfl (by decide) (by decide)) (by simp only [Config.init_mem]; decide) hc hf

end Kraken.Promising.Lower.Pilot

#print axioms Kraken.Promising.Lower.Pilot.pilot_promising_lse2
#print axioms Kraken.Promising.Lower.Pilot.pilot_promising_lse2_sem
#print axioms Kraken.Promising.Lower.Pilot.pilot_promising_lse2_semInf
#print axioms Kraken.Promising.Lower.Pilot.pilot_promising_lse2_concrete
