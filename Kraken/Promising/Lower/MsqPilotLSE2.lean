/-
**`msqPilot_promising` on `isaLSE2`.**

The MS queue pilot's `msqPilot_promising` (`Lower/MsqPilotWhole.lean`, the lowered
two-thread Michael–Scott queue, FIFO) moved to the FEAT_LSE2 target by the
generic route of `Lower/LSE2Final.lean`:

1. `msqPilot_promisingK`, the `#chaink_clone'` of `msqPilot_promising`: the
   same statement, elaborated from the same source, about `ReachableKF`
   (= `ReachableK isa`); its adequacy step is the K twin
   `final_of_relPureSafelyFK`;
2. `progE` and `progD` have no 64-bit `LDP`/`STP` (`progE_lse2Free`,
   `progD_lse2Free`, by `decide`);
3. `final_lse2_of_K` and its semantic forms give the conclusion for every
   final configuration of `isaLSE2` reachable from the start (read through
   `ofL`, which copies the threads and memory unchanged).

Phase-1 limits apply as for `msqPilot_promising`.
-/
import Kraken.Promising.Lower.MsqPilotWhole
import Kraken.Promising.Lower.LSE2Final

open Kraken.Promising.Live.Bridge

#chaink_clone' "MsqPilotWhole.lean"
  only ["msqPilot_promising"]

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.Variant

namespace Kraken.Promising.Lower.MsqPilot

open Kraken.Promising.SLR.EnvG.MsQueue

/-- **The enqueuer's text has no LSE2 pair** (no 64-bit `LDP`/`STP`). -/
theorem progE_lse2Free : ∀ d ∈ progE, d.LSE2Free := by decide

/-- **The dequeuer's text has no LSE2 pair** (no 64-bit `LDP`/`STP`). -/
theorem progD_lse2Free : ∀ d ∈ progD, d.LSE2Free := by decide

/-- The two start states run executables with no LSE2 pair. -/
theorem noLSE2Pairs_startED (l0 l1 : _root_.Layout) {h n1 n2 : BitVec 64} {s0 s1 : isa.State}
    (h0 : StartE (layout := l0) h n1 n2 s0) (h1 : StartD (layout := l1) h s1) :
    ∀ s ∈ [s0, s1], NoLSE2Pairs s.exe :=
  noLSE2Pairs_pair (noLSE2Pairs_of_exe (StartE.exe (layout := l0) h0) progE_lse2Free)
    (noLSE2Pairs_of_exe (StartD.exe (layout := l1) h1) progD_lse2Free)

/-- **`msqPilot_promising` on `isaLSE2`** (AArch64 with FEAT_LSE2,
`Arch.armv8`, the executable machine): for the hypotheses of
`msqPilot_promising`, every final configuration of `isaLSE2` reachable from
the two start states satisfies `MsQueue2Final` (the dequeuer's `x10 = 1`,
`x11 = 2`; read in `Config isa` through `ofL`). -/
theorem msqPilot_promising_lse2 {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 progE)]
    [Executable.ValidLayout (l1 progD)] (h t d n1 n2 : BitVec 64) (ht : t = h + 8) (hht : h ≠ t)
    (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8) (htd : t ≠ d + 8) (htn : t ≠ n1 + 8)
    (htn2 : t ≠ n2 + 8) (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2) (hn1 : n1 ≠ 0) (hn2 : n2 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartE (layout := l0) h n1 n2 s0)
    (h1 : StartD (layout := l1) h s1)
    (hi : InitV2 (Config.init [s0, s1] initMem : Config isa).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isaLSE2} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : MsQueue2Final (ofL cfg) :=
  final_lse2_of_K (noLSE2Pairs_startED l0 l1 h0 h1)
    (fun _ hK hf => msqPilot_promisingK (fuel := 0) l0 l1 h t d n1 n2 ht hht hhd hhn hhn2 htd htn htn2 hdn
      hdn2 hn12 hn1 hn2 h0 h1 hi hK hf) hc hf

/-- **`msqPilot_promising` on `isaLSE2`, semantic machine** (`ReachableSem`). -/
theorem msqPilot_promising_lse2_sem {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 progE)]
    [Executable.ValidLayout (l1 progD)] (h t d n1 n2 : BitVec 64) (ht : t = h + 8) (hht : h ≠ t)
    (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8) (htd : t ≠ d + 8) (htn : t ≠ n1 + 8)
    (htn2 : t ≠ n2 + 8) (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2) (hn1 : n1 ≠ 0) (hn2 : n2 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartE (layout := l0) h n1 n2 s0)
    (h1 : StartD (layout := l1) h s1)
    (hi : InitV2 (Config.init [s0, s1] initMem : Config isa).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isaLSE2} (hc : ReachableSem Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : MsQueue2Final (ofL cfg) :=
  final_lse2_sem_of_K (noLSE2Pairs_startED l0 l1 h0 h1)
    (fun _ hK hf => msqPilot_promisingK (fuel := 0) l0 l1 h t d n1 n2 ht hht hhd hhn hhn2 htd htn htn2 hdn
      hdn2 hn12 hn1 hn2 h0 h1 hi hK hf) hc hf

/-- **`msqPilot_promising` on `isaLSE2`, fuel-free semantic machine**
(`ReachableSemInf`), the form the lowering consumes. -/
theorem msqPilot_promising_lse2_semInf (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 progE)]
    [Executable.ValidLayout (l1 progD)] (h t d n1 n2 : BitVec 64) (ht : t = h + 8) (hht : h ≠ t)
    (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8) (htd : t ≠ d + 8) (htn : t ≠ n1 + 8)
    (htn2 : t ≠ n2 + 8) (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2) (hn1 : n1 ≠ 0) (hn2 : n2 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartE (layout := l0) h n1 n2 s0)
    (h1 : StartD (layout := l1) h s1)
    (hi : InitV2 (Config.init [s0, s1] initMem : Config isa).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isaLSE2}
    (hc : Live.Inf.ReachableSemInf Arch.armv8 (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : MsQueue2Final (ofL cfg) :=
  final_lse2_semInf_of_K (noLSE2Pairs_startED l0 l1 h0 h1)
    (fun _ hK hf => msqPilot_promisingK (fuel := 0) l0 l1 h t d n1 n2 ht hht hhd hhn hhn2 htd htn htn2 hdn
      hdn2 hn12 hn1 hn2 h0 h1 hi hK hf) hc hf

/-- **Non-vacuity**: `msqPilot_promising_lse2` at the explorer's
configuration of `msqPilot_promising_concrete` (`head` at `0x1000`, `tail`
at `0x1008`, both initially the dummy `0x1100`; the nodes at `0x1200`,
`0x1300`), on `isaLSE2`. -/
theorem msqPilot_promising_lse2_concrete {fuel : Nat} {c : Config isaLSE2}
    (hc : Reachable Arch.armv8 fuel (Config.init [threadE, threadD] initMem : Config isaLSE2) c)
    (hf : c.final = true) : MsQueue2Final (ofL c) :=
  msqPilot_promising_lse2 layoutE layoutD 0x1000 0x1008 0x1100 0x1200 0x1300 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) threadE_start threadD_start
    (by refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [Config.init] <;> decide) hc hf

end Kraken.Promising.Lower.MsqPilot

#print axioms Kraken.Promising.Lower.MsqPilot.msqPilot_promising_lse2
#print axioms Kraken.Promising.Lower.MsqPilot.msqPilot_promising_lse2_sem
#print axioms Kraken.Promising.Lower.MsqPilot.msqPilot_promising_lse2_semInf
#print axioms Kraken.Promising.Lower.MsqPilot.msqPilot_promising_lse2_concrete
