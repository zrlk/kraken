/-
**Liveness under a state map, with promises: a
trace-level simulation of the semantic machine, ISA-neutral.**

`LiveRunnerSim` transfers the promise-free liveness theorems (over `TraceS`)
from `decls = {}` to the runner's declarations along a thread-state map `f`
that commutes with `exec` on a step-closed set `G` (`ExecSim f G`). This file
does the same for the with-promises theorems, which are stated on the
semantic machine of `LiveSem` (`TraceSem`, `InstrSem`, `PromSem`, `CertOkN`,
`WeakFairSem`), reusing `ExecSim` and the one-instruction lemmas of
`LiveRunnerSim` unchanged:

- `GoodS G c`: every thread's state is in `G` (promises are allowed; this is
  `RunnerSim.GoodC` without its `prom = []` clause), with `mapC_injS`,
  `mapC_finalS`;
- solo runs: `threadNPn_mapT` (a run of `t` maps to a run of `mapT f t`) and
  `threadNPn_of_mapT` (every run of `mapT f t` is the map of a run of `t`),
  so `certOkN_mapT_iff`: certification within `fuel` is the same on both
  sides. `ExecSim` is a property of states only (the leaves of a `G`-state's
  tree are in `G` whatever the memory), so the solo runs of certification
  stay in `G`;
- steps: an instruction step (`InstrSem`) and a promise step (`PromSem`:
  appending a message does not read the thread's state) map forward
  (`stepSem_mapC`), and enabledness reflects (`enabledSem_of_mapC`);
- traces: `mapTraceSem` (a `TraceSem`), `mapTraceSem_weakFairSem`,
  `mapTraceSem_memFair`;
- **`liveFromSem_transfer`**, **`progressFromSem_transfer`**: `LiveFromSem` /
  `SpinSem.ProgressFromSem` under `WeakFairSem ∧ MemFair` (the fairness of
  the existing with-promises theorems) at the mapped initial configuration give
  the same at the original one, for `Waiting` / `Done` predicates that read a
  thread only through the map.
-/
import Kraken.Promising.LiveRunnerSim
import Kraken.Promising.LiveSem

namespace Kraken.Promising.Live.RunnerSemSim

open Kraken Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.RunnerSim Kraken.Promising.Live.Sem

variable {I : ISA}

/-! ## The configuration invariant -/

/-- **The configuration invariant with promises**: every thread's state is
in `G` (`RunnerSim.GoodC` without `prom = []`). -/
def GoodS (G : I.State → Prop) (c : Config I) : Prop :=
  ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → G t.st

theorem goodS_init {G : I.State → Prop} {states : List I.State} (initMem : List (Loc × Val))
    (h : ∀ s ∈ states, G s) : GoodS G (Config.init states initMem) :=
  fun i t ht => (goodC_init (G := G) initMem h i t ht).1

theorem goodS_withThread {G : I.State → Prop} {c : Config I} {tid : Nat} {t t' : Thread I} {mem : Memory}
    (hg : GoodS G c) (ht : c.threads[tid]? = some t) (hG : G t'.st) : GoodS G (c.withThread tid t' mem) := by
  intro i u hu
  rw [Config.withThread_get? c _ _ (lt_size_of_get? ht)] at hu
  split at hu
  · cases hu; exact hG
  · exact hg i u hu

section Sim

variable {f : I.State → I.State} {G : I.State → Prop} (hS : ExecSim f G)
include hS

/-- `mapC f` is injective on `GoodS G` (as `RunnerSim.mapC_inj`). -/
theorem mapC_injS {c c' : Config I} (hg : GoodS G c) (hg' : GoodS G c') (h : mapC f c = mapC f c') : c = c' := by
  obtain ⟨ths, mem⟩ := c
  obtain ⟨ths', mem'⟩ := c'
  simp only [mapC, Config.mk.injEq] at h
  obtain ⟨h1, rfl⟩ := h
  have hsz : ths.size = ths'.size := by simpa using congrArg Array.size h1
  refine Config.mk.injEq _ _ _ _ |>.mpr ⟨Array.ext hsz fun i hi hi' => ?_, rfl⟩
  have e := congrArg (fun a => a[i]?) h1
  simp only [Array.getElem?_map, Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi',
    Option.map_some, Option.some.injEq] at e
  have hG := hg i _ (Array.getElem?_eq_getElem hi)
  have hG' := hg' i _ (Array.getElem?_eq_getElem hi')
  have est : ths[i].st = ths'[i].st := hS.inj _ _ hG hG' (congrArg Thread.st e)
  have e' := e
  revert e' est
  generalize ths[i] = a
  generalize ths'[i] = b
  intro est e'
  cases a; cases b
  simp only [mapT, Thread.mk.injEq] at e' est ⊢
  exact ⟨est, e'.2⟩

theorem mapC_finalS {c : Config I} (hg : GoodS G c) (hf : c.final = true) : (mapC f c).final = true := by
  simp only [Config.final, Array.all_eq_true] at hf ⊢
  intro i hi
  have hi' : i < c.threads.size := by simpa [mapC] using hi
  have := hf i hi'
  have hG := hg i _ (Array.getElem?_eq_getElem hi')
  simp only [mapC, Array.getElem_map, mapT_prom]
  rw [halted_mapT hS hG]
  exact this

/-! ## Solo runs and certification -/

/-- A successful step from a `G`-state ends in `G`. -/
theorem leafG {A : Arch} {t : Thread I} (hG : G t.st) {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hs : stepOne A t tid mem = some outs) {o : Outcome I}
    (ho : .ok o ∈ outs) : G o.thread.st :=
  stepOne_leaf A hs ho (hS.leaves _ hG)

/-- **A solo run of `t`, mapped, is a solo run of `mapT f t`.** -/
theorem threadNPn_mapT {A : Arch} {tid : Nat} : ∀ {n : Nat} {p q : Thread I × Memory},
    ThreadNPn A tid n p q → G p.1.st → ThreadNPn A tid n (mapT f p.1, p.2) (mapT f q.1, q.2) ∧ G q.1.st := by
  intro n p q h
  induction h with
  | refl => intro hG; exact ⟨.refl _ _, hG⟩
  | step hs _ ih =>
    intro hG
    obtain ⟨outs, o, hs, ho, rfl⟩ := hs
    obtain ⟨h1, h2⟩ := ih (leafG hS hG hs ho)
    exact ⟨.step ⟨_, mapO f o, by rw [stepOne_mapT hS A hG, hs]; rfl, List.mem_map.mpr ⟨_, ho, rfl⟩, rfl⟩ h1, h2⟩

/-- **Every solo run of `mapT f t` is a solo run of `t`, mapped**, ending in
`G`. -/
theorem threadNPn_of_mapT {A : Arch} {tid : Nat} : ∀ {n : Nat} {p q : Thread I × Memory},
    ThreadNPn A tid n p q → ∀ t, p.1 = mapT f t → G t.st →
      ∃ t', q.1 = mapT f t' ∧ G t'.st ∧ ThreadNPn A tid n (t, p.2) (t', q.2) := by
  intro n p q h
  induction h with
  | refl n p => intro t ht hG; exact ⟨t, ht, hG, .refl _ _⟩
  | step hs _ ih =>
    intro t ht hG
    obtain ⟨outs', o', hs', ho', rfl⟩ := hs
    rw [ht] at hs'
    obtain ⟨outs, o, hs, ho, rfl⟩ := ok_mem_mapT hS hG hs' ho'
    obtain ⟨t', h1, h2, h3⟩ := ih o.thread rfl (leafG hS hG hs ho)
    exact ⟨t', h1, h2, .step ⟨outs, o, hs, ho, rfl⟩ h3⟩

/-- **Certification within `n` instructions is the same for `t` and
`mapT f t`.** -/
theorem certOkN_mapT_iff {A : Arch} {tid : Nat} {t : Thread I} (hG : G t.st) {mem : Memory} {n : Nat} :
    CertOkN A tid (mapT f t) mem n ↔ CertOkN A tid t mem n := by
  constructor
  · rintro ⟨t', mem', h, hp⟩
    obtain ⟨t'', e, -, h'⟩ := threadNPn_of_mapT hS h t rfl hG
    have e' : t' = mapT f t'' := e
    subst e'
    exact ⟨t'', mem', h', hp⟩
  · rintro ⟨t', mem', h, hp⟩
    exact ⟨mapT f t', mem', (threadNPn_mapT hS h hG).1, hp⟩

/-! ## Steps -/

/-- **A semantic step, mapped** (instruction or promise). -/
theorem stepSem_mapC {A : Arch} {fuel tid : Nat} {c c' : Config I} (hg : GoodS G c)
    (h : StepSem A fuel tid c c') : StepSem A fuel tid (mapC f c) (mapC f c') := by
  rcases h with ⟨t, outs, o, ht, hs, ho, hc, rfl⟩ | ⟨t, w, ht, hw, hc, rfl⟩
  · have hG := hg tid t ht
    exact .inl ⟨mapT f t, outs.map (Except.map (mapO f)), mapO f o, by simp [ht],
      by rw [mapC_mem, stepOne_mapT hS A hG, hs]; rfl, List.mem_map.mpr ⟨_, ho, rfl⟩,
      (certOkN_mapT_iff hS (leafG hS hG hs ho)).mpr hc, mapC_withThread f c tid _ _⟩
  · exact .inr ⟨mapT f t, w, by simp [ht], hw,
      (certOkN_mapT_iff hS (t := promThread t c.mem w) (hg tid t ht)).mpr hc, mapC_withThread f c tid _ _⟩

/-- A semantic step keeps the invariant. -/
theorem goodS_stepSem {A : Arch} {fuel tid : Nat} {c c' : Config I} (hg : GoodS G c)
    (h : StepSem A fuel tid c c') : GoodS G c' := by
  rcases h with ⟨t, outs, o, ht, hs, ho, -, rfl⟩ | ⟨t, w, ht, -, -, rfl⟩
  · exact goodS_withThread hg ht (leafG hS (hg tid t ht) hs ho)
  · exact goodS_withThread hg ht (hg tid t ht)

/-- **Enabledness reflects**: a thread enabled in the mapped configuration
is enabled in the configuration. -/
theorem enabledSem_of_mapC {A : Arch} {fuel tid : Nat} {c : Config I} (hg : GoodS G c)
    (he : EnabledSem A fuel tid (mapC f c)) : EnabledSem A fuel tid c := by
  obtain ⟨c', ⟨t', outs', o', ht', hs', ho', hc', -⟩ | ⟨t', w, ht', hw, hc', -⟩⟩ := he
  · simp only [mapC_get?, Option.map_eq_some_iff] at ht'
    obtain ⟨t, ht, rfl⟩ := ht'
    have hG := hg tid t ht
    obtain ⟨outs, o, hs, ho, rfl⟩ := ok_mem_mapT hS hG hs' ho'
    exact ⟨_, .inl ⟨t, outs, o, ht, hs, ho, (certOkN_mapT_iff hS (leafG hS hG hs ho)).mp hc', rfl⟩⟩
  · simp only [mapC_get?, Option.map_eq_some_iff] at ht'
    obtain ⟨t, ht, rfl⟩ := ht'
    exact ⟨_, .inr ⟨t, w, ht, hw, (certOkN_mapT_iff hS (t := promThread t c.mem w) (hg tid t ht)).mp hc', rfl⟩⟩

end Sim

/-! ## Traces -/

section Trace

variable {f : I.State → I.State} {G : I.State → Prop} (hS : ExecSim f G)
  {A : Arch} {fuel : Nat} {tr : TraceSem A fuel I} (hg0 : GoodS G (tr.cfg 0))

include hS hg0

/-- **Every configuration of a semantic trace from a `GoodS` start is
`GoodS`.** -/
theorem traceSem_good (i : Nat) : GoodS G (tr.cfg i) := by
  induction i with
  | zero => exact hg0
  | succ i ih =>
    rcases tr.step i with ⟨_, h⟩ | ⟨-, he⟩
    · exact goodS_stepSem hS ih h
    · rw [he]; exact ih

/-- **The mapped trace.** -/
def mapTraceSem : TraceSem A fuel I where
  cfg i := mapC f (tr.cfg i)
  step i := by
    rcases tr.step i with ⟨tid, h⟩ | ⟨hf, he⟩
    · exact .inl ⟨tid, stepSem_mapC hS (traceSem_good hS hg0 i) h⟩
    · exact .inr ⟨mapC_finalS hS (traceSem_good hS hg0 i) hf, by rw [he]⟩

@[simp] theorem mapTraceSem_cfg (i : Nat) : (mapTraceSem hS hg0).cfg i = mapC f (tr.cfg i) := rfl

theorem mapTraceSem_weakFairSem (hwf : WeakFairSem A fuel tr.cfg) :
    WeakFairSem A fuel (mapTraceSem hS hg0).cfg := by
  intro tid ⟨n, hn⟩ m
  obtain ⟨i, hi, hs⟩ := hwf tid ⟨n, fun i hi => enabledSem_of_mapC hS (traceSem_good hS hg0 i) (hn i hi)⟩ m
  exact ⟨i, hi, stepSem_mapC hS (traceSem_good hS hg0 i) hs⟩

theorem mapTraceSem_memFair (hmf : MemFair A tr.cfg) : MemFair A (mapTraceSem hS hg0).cfg := by
  intro tid l hinf i ts w hw hl
  have hinf' : InfOften (fun i => ∃ ts, ReadsAt A tr.cfg tid l ts i) := by
    intro n
    obtain ⟨j, hj, ts', t', outs', o', ht', hs', ho', he', hr⟩ := hinf n
    refine ⟨j, hj, ts', ?_⟩
    simp only [mapTraceSem_cfg, mapC_get?, Option.map_eq_some_iff] at ht'
    obtain ⟨t, ht, rfl⟩ := ht'
    have hg := traceSem_good hS hg0 j
    have hG := hg tid t ht
    obtain ⟨outs, o, hs, ho, rfl⟩ := ok_mem_mapT hS hG hs' ho'
    have he : tr.cfg (j + 1) = (tr.cfg j).withThread tid o.thread o.mem :=
      mapC_injS hS (traceSem_good hS hg0 (j + 1)) (goodS_withThread hg ht (leafG hS hG hs ho))
        (by rw [mapC_withThread]; exact he')
    exact ⟨t, outs, o, ht, hs, ho, he, hr⟩
  obtain ⟨j, hij, t, ht, hle⟩ := hmf tid l hinf' i ts w hw hl
  exact ⟨j, hij, mapT f t, by simp [ht], hle⟩

end Trace

/-! ## Transfer of liveness statements -/

section Transfer

variable {f : I.State → I.State} {G : I.State → Prop} (hS : ExecSim f G)

include hS in
/-- **Transfer of `LiveFromSem`** (with promises; `Fair = WeakFairSem ∧
MemFair`, the fairness of the existing with-promises theorems). If every
thread of `c0` is in `G`, and `Waiting`/`Done` read a configuration only
through `mapC f`, then liveness from `mapC f c0` gives liveness from `c0`. -/
theorem liveFromSem_transfer {A : Arch} {fuel : Nat} {c0 : Config I} (hg0 : GoodS G c0)
    {W D : Nat → Config I → Prop} (hW : ∀ tid c, W tid (mapC f c) ↔ W tid c)
    (hD : ∀ tid c, D tid (mapC f c) ↔ D tid c)
    (h : LiveFromSem A fuel (mapC f c0) (fun cfg => WeakFairSem A fuel cfg ∧ MemFair A cfg) W D) :
    LiveFromSem A fuel c0 (fun cfg => WeakFairSem A fuel cfg ∧ MemFair A cfg) W D := by
  intro tr h0 ⟨hwf, hmf⟩ tid i hw
  have hg0' : GoodS G (tr.cfg 0) := h0 ▸ hg0
  obtain ⟨j, hij, hd⟩ := h (mapTraceSem hS hg0') (by simp [h0])
    ⟨mapTraceSem_weakFairSem hS hg0' hwf, mapTraceSem_memFair hS hg0' hmf⟩ tid i ((hW _ _).mpr hw)
  exact ⟨j, hij, (hD _ _).mp hd⟩

include hS in
/-- **Transfer of `SpinSem.ProgressFromSem`** (with promises; `Fair =
WeakFairSem ∧ MemFair`). -/
theorem progressFromSem_transfer {A : Arch} {fuel : Nat} {c0 : Config I} (hg0 : GoodS G c0)
    {W D : Nat → Config I → Prop} (hW : ∀ tid c, W tid (mapC f c) ↔ W tid c)
    (hD : ∀ tid c, D tid (mapC f c) ↔ D tid c)
    (h : SpinSem.ProgressFromSem A fuel (mapC f c0) (fun cfg => WeakFairSem A fuel cfg ∧ MemFair A cfg) W D) :
    SpinSem.ProgressFromSem A fuel c0 (fun cfg => WeakFairSem A fuel cfg ∧ MemFair A cfg) W D := by
  intro tr h0 ⟨hwf, hmf⟩ tid i hw
  have hg0' : GoodS G (tr.cfg 0) := h0 ▸ hg0
  obtain ⟨j, hij, tid', hn, hd⟩ := h (mapTraceSem hS hg0') (by simp [h0])
    ⟨mapTraceSem_weakFairSem hS hg0' hwf, mapTraceSem_memFair hS hg0' hmf⟩ tid i ((hW _ _).mpr hw)
  exact ⟨j, hij, tid', fun h' => hn ((hD _ _).mpr h'), (hD _ _).mp hd⟩

end Transfer

end Kraken.Promising.Live.RunnerSemSim

#print axioms Kraken.Promising.Live.RunnerSemSim.liveFromSem_transfer
#print axioms Kraken.Promising.Live.RunnerSemSim.progressFromSem_transfer
