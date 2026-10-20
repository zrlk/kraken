/-
**A generic route from a whole-program `isa` headline
to `isaLSE2`.**

The WeakCore lowering target is `isaLSE2` (FEAT_LSE2). A lowered program's
headline is stated on the executable machine of `isa` (`Reachable`,
`succs`), and `Reachable isa ↔ Reachable isaLSE2` is not proved
(`Lower/LSE2Transfer.lean`: `certify`'s caches are keyed on `Thread I`). So
the headline itself cannot be transferred; its *proof* can, through the K
world (`ReachableK isa`, which contains the executable and the semantic
machines of both ISAs on programs with no LSE2 pair). This file does the
parts that do not depend on the program, once:

1. **The value bridge at the K world.** `#chaink_clone'` of the AArch64 value
   bridge (`EnvG/ValsA64.lean`), on the ISA-neutral chain clone
   `final_of_chainVK` (`ChainK/ValsChainN.lean`):
   `final_of_relPureSafelyFVK`, `EnvGValsBridgeJK`/`envGValsBridgeJK` and
   `envGValsBridge_ofSpecsK`, the same statements about `ReachableKF`
   (= `ReachableK`, fuel ignored). With the K twins of the
   adequacy chain (`final_of_relPureSafelyFK`, `…SK`, `…FDK`, `…SDK`), every
   whole-program adequacy entry point of the AArch64 EnvG chain now has a K
   twin.
2. **The transfer.** `final_lse2_of_K`, `final_lse2_sem_of_K`,
   `final_lse2_semInf_of_K`: a conclusion `Φ` of every final configuration
   that is `ReachableK isa` from `Config.init states initMem`, where no start
   state's executable has an LSE2 pair (`NoLSE2Pairs`), holds (through
   `ofL`, which copies the threads and memory unchanged) of every final
   configuration of `isaLSE2` reachable from the same start on the
   executable (`Reachable`), the semantic (`ReachableSem`) and the fuel-free
   semantic (`ReachableSemInf`) machine. Any `Arch`.

**Moving a lowered program to `isaLSE2`** (the pattern of
`Lower/PilotLSE2.lean`, `Lower/Pilot2LSE2.lean` and
`Lower/MsqPilotLSE2.lean`). For a headline
`x_promising … (hc : Reachable A fuel (Config.init states initMem) cfg)
(hf : cfg.final = true) : Φ cfg` in module `M.lean`:

```
#chaink_clone' "M.lean" only ["x_promising"]      -- x_promisingK, on ReachableKF
theorem x_lse2Free : ∀ d ∈ prog, d.LSE2Free := by decide
theorem x_promising_lse2 … (hc : Reachable A fuel (Config.init states initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : Φ (ofL cfg) :=
  final_lse2_of_K (… noLSE2Pairs_of_exe hS.exe x_lse2Free …)
    (fun _ hK hf => x_promisingK (fuel := 0) … hK hf) hc hf
```

and the same with `final_lse2_sem_of_K` / `final_lse2_semInf_of_K` for the
semantic forms. The clone directive needs every executable-machine lemma
the headline's proof uses to have a K twin; for proofs that end in one of
the adequacy entry points above it does (one directive, no file chain).
Limits: programs with no 64-bit `LDP`/`STP` at all (`NoLSE2Pairs`; the
`(A4)` note of `LSE2Transfer.lean` says what a pair would need).
-/
import Kraken.Promising.SLR.EnvG.ValsA64
import Kraken.Promising.Lower.LSE2Transfer
import Kraken.Promising.SLR.ChainK.TwinsCloneA64a
import Kraken.Promising.SLR.ChainK.ValsChainN

open Kraken.Promising.Live.Bridge

#chaink_clone' "../SLR/EnvG/ValsA64.lean"
  only ["final_of_relPureSafelyFV", "EnvGValsBridgeJ", "envGValsBridgeJ", "envGValsBridge_ofSpecs"]

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.Variant

namespace Kraken.Promising.AArch64

/-- A start state running a laid-out program with no LSE2 pair has
`NoLSE2Pairs` (the `exe` field of a start-state structure). -/
theorem noLSE2Pairs_of_exe {s : isa.State} {l : _root_.Layout} {prog : Program} (he : s.exe = l prog)
    (h : ∀ d ∈ prog, d.LSE2Free) : NoLSE2Pairs s.exe :=
  he ▸ noLSE2Pairs_apply l h

/-- `NoLSE2Pairs` of every state of a two-thread start. -/
theorem noLSE2Pairs_pair {s0 s1 : isa.State} (h0 : NoLSE2Pairs s0.exe) (h1 : NoLSE2Pairs s1.exe) :
    ∀ s ∈ [s0, s1], NoLSE2Pairs s.exe := by
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact h0
  · exact h1

section Transfer

variable {A : Arch} {states : List isa.State} {initMem : List (Loc × Val)} {Φ : Config isa → Prop}

/-- **A K-world whole-program conclusion holds on `isaLSE2`'s executable
machine** (`Reachable`, `succs`): if no start state has an LSE2 pair and `Φ`
holds of every final configuration `ReachableK isa` from the start, then it
holds (read through `ofL`) of every final configuration of `isaLSE2`
reachable from the start. -/
theorem final_lse2_of_K (hg : ∀ s ∈ states, NoLSE2Pairs s.exe)
    (hK : ∀ cfg, ReachableK A (Config.init states initMem) cfg → cfg.final = true → Φ cfg)
    {fuel : Nat} {cfg : Config isaLSE2} (hc : Reachable A fuel (Config.init states initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : Φ (ofL cfg) := by
  have hgc : GoodC GoodL (Config.init states initMem : Config isa) := goodC_init hg initMem
  have hc' : Reachable A fuel (toL (Config.init states initMem)) cfg := (toL_init _ _).symm ▸ hc
  exact hK _ (reachableK_of_reachable_lse2 hgc hc')
    (final_ofL_of_reachableK hgc (ReachableK.of_reachable (I := isaLSE2) hc') hf)

/-- **`final_lse2_of_K` on the semantic machine** (`ReachableSem`:
certification within `fuel` instructions, no `certify` search). -/
theorem final_lse2_sem_of_K (hg : ∀ s ∈ states, NoLSE2Pairs s.exe)
    (hK : ∀ cfg, ReachableK A (Config.init states initMem) cfg → cfg.final = true → Φ cfg)
    {fuel : Nat} {cfg : Config isaLSE2} (hc : ReachableSem A fuel (Config.init states initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : Φ (ofL cfg) := by
  have hgc : GoodC GoodL (Config.init states initMem : Config isa) := goodC_init hg initMem
  have hc' : ReachableSem A fuel (toL (Config.init states initMem)) cfg := (toL_init _ _).symm ▸ hc
  have hKL : ReachableK A (toL (Config.init states initMem)) cfg :=
    (toL_init _ _).symm ▸ ReachableK.of_reachableSem' (Config.init_bnd _ _) hc
  exact hK _ (ReachableK.of_reachableSem' (Config.init_bnd _ _) (reachableSem_ofL hgc hc'))
    (final_ofL_of_reachableK hgc hKL hf)

/-- **`final_lse2_of_K` on the fuel-free semantic machine**
(`ReachableSemInf`: unbounded certification), the form the lowering
consumes. -/
theorem final_lse2_semInf_of_K (hg : ∀ s ∈ states, NoLSE2Pairs s.exe)
    (hK : ∀ cfg, ReachableK A (Config.init states initMem) cfg → cfg.final = true → Φ cfg)
    {cfg : Config isaLSE2} (hc : Live.Inf.ReachableSemInf A (Config.init states initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : Φ (ofL cfg) := by
  obtain ⟨fuel, hc⟩ := Live.Inf.reachableSemInf_iff.mp hc
  exact final_lse2_sem_of_K hg hK hc hf

end Transfer

end Kraken.Promising.AArch64

#print axioms Kraken.Promising.AArch64.EnvG.Vals.envGValsBridge_ofSpecsK
#print axioms Kraken.Promising.AArch64.final_lse2_of_K
#print axioms Kraken.Promising.AArch64.final_lse2_sem_of_K
#print axioms Kraken.Promising.AArch64.final_lse2_semInf_of_K
