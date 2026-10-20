/-
**Bounded certification and the fuel-free
semantic machine** (ISA-neutral, architecture-neutral, program-independent).
Nothing existing is changed.

Every existing liveness and termination theorem on the *semantic* machine
(`StepSem`/`TraceSem`, `LiveSem.lean`) is stated for one certification fuel
`fuel`, the same for every step of the trace ("fixed-fuel caveat"). Finite
runs need no fixed fuel (`reachableSem_mono`), but infinite traces do: a
trace whose `i`-th step needs certification length `i` is a trace at no
fixed fuel. This file defines the **fuel-free semantic machine**, where each
step may use its own certification length, and transfers the fixed-fuel
theorems to it under one per-program hypothesis:

- `CertBoundedFrom A c0 F`: whatever a thread of a
  configuration reachable from `c0` (at any fuel) can certify, it can certify
  within `F` instructions.
- The fuel-free machine: `StepSemU`, `InstrSemU`, `TraceSemU`, `EnabledSemU`,
  `WeakFairSemU`, `LiveFromSemU`, `ProgressFromSemU`, `TermFromSemU`,
  `TermBoundSemU`. All of them are on the semantic machine; none mentions
  `succs` or `certify`.
- Transfers (theorems; `CertBoundedFrom` is an explicit argument):
  `traceSemUToSem` (every fuel-free trace from `c0` is a `TraceSem F`),
  `weakFairSem_of_weakFairSemU`, `liveTransfer`, `progressTransfer`,
  `termTransfer`, `termFromTransfer`, and the fairness-generic forms
  `liveTransferG`, `progressTransferG`, `termFromTransferG`.
- Converses that need no hypothesis: `TraceSem.toU`, `TermBoundSemU.toSem`
  (a fuel-free bound is a bound at every fuel).
- Proving `CertBoundedFrom` (route R2, generic part): `ThreadNPn.shorten`
  (a solo run along which a rank drops is no longer than the rank) and
  `certBoundedFrom_of_soloRank` (a fuel-free invariant of the reachable
  configurations plus a solo-run rank bounded by `F`).

`MemFair` (`LiveTrace.lean`) is fuel-free (it mentions only `stepOne`,
`withThread` and the trace), so it is shared by both machines unchanged.

Proof (prototype §2.2): a step at fuel `n` from a configuration reachable at fuel
`f` ends in a configuration reachable at `max f n` (`reachableSem_mono`,
`NoStuck.reachableSem_snoc`), so `CertBoundedFrom` applies to the stepping
thread's post-state and the step is a step at `F`. By induction every
configuration of a fuel-free trace from `c0` is reachable at some fuel.
-/
import Kraken.Promising.LiveNoStuck
import Kraken.Promising.LiveTerm

namespace Kraken.Promising.Live.CertBounded

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem Kraken.Promising.Live.Bridge

variable {I : ISA}

/-! ## Bounded certification -/

/-- **Bounded certification from `c0`** (semantic machine): whatever a thread
of a configuration reachable from `c0` (at any fuel) can certify, it can
certify within `F` instructions. -/
def CertBoundedFrom (A : Arch) (c0 : Config I) (F : Nat) : Prop :=
  ∀ fuel c, ReachableSem A fuel c0 c → ∀ tid t n, c.threads[tid]? = some t →
    CertOkN A tid t c.mem n → CertOkN A tid t c.mem F

/-! ## Proving `CertBoundedFrom`: a rank on solo runs -/

/-- **A solo run along which a rank drops is no longer than the rank**: if
every step of the thread alone from a state satisfying `P` keeps `P` and
lowers `μ`, then a run of any length from `p` is a run of length `μ p`. -/
theorem _root_.Kraken.Promising.Live.ThreadNPn.shorten {A : Arch} {tid : Nat} (P : Thread I × Memory → Prop)
    (μ : Thread I × Memory → Nat) (hstep : ∀ p q, P p → ThreadStep A tid p q → P q ∧ μ q < μ p) :
    ∀ {n : Nat} {p q : Thread I × Memory}, ThreadNPn A tid n p q → P p → ThreadNPn A tid (μ p) p q := by
  intro n p q h
  induction h with
  | refl => intro _; exact .refl _ _
  | step hs _ ih =>
    intro hp
    obtain ⟨hq, hlt⟩ := hstep _ _ hp hs
    exact (ThreadNPn.step hs (ih hq)).mono hlt

/-- **`CertBoundedFrom` from a solo-run rank** (route R2, generic part). `Inv`
holds along every semantic run from `c0`, at
every fuel; at an `Inv` configuration `c`, every thread alone runs under a
step invariant `P c tid` along which a rank `μ c tid` drops, and starts with
rank at most `F`. Then every certification of a reachable thread is within
`F` instructions. -/
theorem certBoundedFrom_of_soloRank {A : Arch} {c0 : Config I} {F : Nat} (Inv : Config I → Prop)
    (h0 : Inv c0) (hinv : ∀ fuel tid c c', Inv c → StepSem A fuel tid c c' → Inv c')
    (P : Config I → Nat → Thread I × Memory → Prop) (μ : Config I → Nat → Thread I × Memory → Nat)
    (hP : ∀ c tid t, Inv c → c.threads[tid]? = some t → P c tid (t, c.mem))
    (hstep : ∀ c tid p q, Inv c → P c tid p → ThreadStep A tid p q → P c tid q ∧ μ c tid q < μ c tid p)
    (hF : ∀ c tid t, Inv c → c.threads[tid]? = some t → μ c tid (t, c.mem) ≤ F) :
    CertBoundedFrom A c0 F := by
  intro fuel c hr tid t n ht ⟨t', mem', hrun, hp⟩
  have hI := NoStuck.reachableSem_inv Inv (hinv fuel) hr h0
  exact ⟨t', mem', (hrun.shorten (P c tid) (μ c tid) (hstep c tid · · hI) (hP c tid t hI ht)).mono
    (hF c tid t hI ht), hp⟩

/-! ## The fuel-free semantic machine -/

/-- A semantic step of `tid` at some certification fuel (the fuel may differ
from step to step). -/
def StepSemU (A : Arch) (tid : Nat) (c c' : Config I) : Prop := ∃ fuel, StepSem A fuel tid c c'

/-- A semantic instruction step of `tid` at some certification fuel. -/
def InstrSemU (A : Arch) (tid : Nat) (c c' : Config I) : Prop := ∃ fuel, InstrSem A fuel tid c c'

/-- **A trace of the fuel-free semantic machine**, stuttering only at a final
configuration (as `TraceSem`). -/
structure TraceSemU (A : Arch) (I : ISA) where
  cfg : Nat → Config I
  step : ∀ i, (∃ tid, StepSemU A tid (cfg i) (cfg (i + 1))) ∨ ((cfg i).final = true ∧ cfg (i + 1) = cfg i)

/-- Thread `tid` can take a step (at some fuel). -/
def EnabledSemU (A : Arch) (tid : Nat) (c : Config I) : Prop := ∃ c', StepSemU A tid c c'

/-- **Weak fairness** on the fuel-free semantic machine. -/
def WeakFairSemU (A : Arch) (cfg : Nat → Config I) : Prop :=
  ∀ tid, EvAlways (fun i => EnabledSemU A tid (cfg i)) →
    InfOften (fun i => StepSemU A tid (cfg i) (cfg (i + 1)))

/-- **Liveness from `c0`** on the fuel-free semantic machine. -/
def LiveFromSemU (A : Arch) (c0 : Config I) (Fair : (Nat → Config I) → Prop)
    (Waiting Done : Nat → Config I → Prop) : Prop :=
  ∀ tr : TraceSemU A I, tr.cfg 0 = c0 → Fair tr.cfg →
    ∀ tid i, Waiting tid (tr.cfg i) → ∃ j, i ≤ j ∧ Done tid (tr.cfg j)

/-- **Deadlock-freedom from `c0`** on the fuel-free semantic machine (the
`SpinSem.ProgressFromSem` shape over `TraceSemU`). -/
def ProgressFromSemU (A : Arch) (c0 : Config I) (Fair : (Nat → Config I) → Prop)
    (Waiting Done : Nat → Config I → Prop) : Prop :=
  ∀ tr : TraceSemU A I, tr.cfg 0 = c0 → Fair tr.cfg →
    ∀ tid i, Waiting tid (tr.cfg i) → ∃ j, i ≤ j ∧ ∃ tid', ¬ Done tid' (tr.cfg i) ∧ Done tid' (tr.cfg j)

/-- **Termination under `Fair`** on the fuel-free semantic machine. -/
def TermFromSemU (A : Arch) (c0 : Config I) (Fair : (Nat → Config I) → Prop) : Prop :=
  ∀ tr : TraceSemU A I, tr.cfg 0 = c0 → Fair tr.cfg → ∃ j, (tr.cfg j).final = true

/-- **Bounded termination under every schedule** on the fuel-free semantic
machine: one index `K` at which every fuel-free trace from `c0` is final. -/
def TermBoundSemU (A : Arch) (c0 : Config I) : Prop :=
  ∃ K, ∀ tr : TraceSemU A I, tr.cfg 0 = c0 → (tr.cfg K).final = true

/-! ## Fixed fuel inside the fuel-free machine -/

theorem stepSemU_of_stepSem {A : Arch} {fuel tid : Nat} {c c' : Config I} (h : StepSem A fuel tid c c') :
    StepSemU A tid c c' := ⟨fuel, h⟩

/-- A trace at fixed fuel is a fuel-free trace. -/
def _root_.Kraken.Promising.Live.Sem.TraceSem.toU {A : Arch} {fuel : Nat} (tr : TraceSem A fuel I) :
    TraceSemU A I where
  cfg := tr.cfg
  step i := (tr.step i).imp (fun ⟨tid, h⟩ => ⟨tid, fuel, h⟩) id

/-- **A fuel-free termination bound is a bound at every fuel.** -/
theorem TermBoundSemU.toSem {A : Arch} {c0 : Config I} (h : TermBoundSemU A c0) (fuel : Nat) :
    Term.TermBoundSem A fuel c0 := by
  obtain ⟨K, hK⟩ := h
  exact ⟨K, fun tr h0 => hK tr.toU h0⟩

/-! ## Steps at reachable configurations -/

/-- A step at fuel `n` from a configuration reachable at fuel `f` ends in a
configuration reachable at `max f n`. -/
theorem reachableSem_snoc_max {A : Arch} {f n tid : Nat} {c0 c c' : Config I}
    (hr : ReachableSem A f c0 c) (hs : StepSem A n tid c c') : ReachableSem A (max f n) c0 c' :=
  NoStuck.reachableSem_snoc (reachableSem_mono (Nat.le_max_left _ _) hr)
    (stepSem_mono (Nat.le_max_right _ _) hs)

/-- **Under `CertBoundedFrom`, a step from a reachable configuration is a step
at `F`.** -/
theorem stepSem_of_certBounded {A : Arch} {c0 : Config I} {F f n tid : Nat} {c c' : Config I}
    (hcb : CertBoundedFrom A c0 F) (hr : ReachableSem A f c0 c) (hs : StepSem A n tid c c') :
    StepSem A F tid c c' := by
  have hr' := reachableSem_snoc_max hr hs
  rcases hs with ⟨t, outs, o, ht, hs, ho, hc, rfl⟩ | ⟨t, w, ht, hw, hc, rfl⟩
  · exact .inl ⟨t, outs, o, ht, hs, ho, hcb _ _ hr' tid o.thread n (withThread_get_self ht) hc, rfl⟩
  · exact .inr ⟨t, w, ht, hw, hcb _ _ hr' tid _ n (withThread_get_self ht) hc, rfl⟩

theorem stepSemU_iff {A : Arch} {c0 : Config I} {F f tid : Nat} {c c' : Config I}
    (hcb : CertBoundedFrom A c0 F) (hr : ReachableSem A f c0 c) :
    StepSemU A tid c c' ↔ StepSem A F tid c c' :=
  ⟨fun ⟨_, hs⟩ => stepSem_of_certBounded hcb hr hs, stepSemU_of_stepSem⟩

theorem enabledSemU_iff {A : Arch} {c0 : Config I} {F f tid : Nat} {c : Config I}
    (hcb : CertBoundedFrom A c0 F) (hr : ReachableSem A f c0 c) :
    EnabledSemU A tid c ↔ EnabledSem A F tid c :=
  ⟨fun ⟨c', h⟩ => ⟨c', (stepSemU_iff hcb hr).1 h⟩, fun ⟨c', h⟩ => ⟨c', stepSemU_of_stepSem h⟩⟩

/-- Under `CertBoundedFrom`, an instruction step from a reachable
configuration is an instruction step at `F`. -/
theorem instrSem_of_certBounded {A : Arch} {c0 : Config I} {F f n tid : Nat} {c c' : Config I}
    (hcb : CertBoundedFrom A c0 F) (hr : ReachableSem A f c0 c) (hs : InstrSem A n tid c c') :
    InstrSem A F tid c c' := by
  have hr' := reachableSem_snoc_max hr (.inl hs)
  obtain ⟨t, outs, o, ht, hs, ho, hc, rfl⟩ := hs
  exact ⟨t, outs, o, ht, hs, ho, hcb _ _ hr' tid o.thread n (withThread_get_self ht) hc, rfl⟩

theorem instrSemU_iff {A : Arch} {c0 : Config I} {F f tid : Nat} {c c' : Config I}
    (hcb : CertBoundedFrom A c0 F) (hr : ReachableSem A f c0 c) :
    InstrSemU A tid c c' ↔ InstrSem A F tid c c' :=
  ⟨fun ⟨_, hs⟩ => instrSem_of_certBounded hcb hr hs, fun h => ⟨F, h⟩⟩

/-! ## Fuel-free traces are traces at `F` -/

namespace TraceSemU

variable {A : Arch}

/-- Every configuration of a fuel-free trace from `c0` is reachable from `c0`
at some fuel. -/
theorem reach (tr : TraceSemU A I) {c0 : Config I} (h0 : tr.cfg 0 = c0) :
    ∀ i, ∃ f, ReachableSem A f c0 (tr.cfg i)
  | 0 => ⟨0, h0 ▸ .refl _⟩
  | i + 1 => by
    obtain ⟨f, hf⟩ := tr.reach h0 i
    rcases tr.step i with ⟨tid, n, hs⟩ | ⟨-, he⟩
    · exact ⟨_, reachableSem_snoc_max hf hs⟩
    · exact ⟨f, he ▸ hf⟩

/-- **A fuel-free trace from `c0` is a trace at `F`**, under
`CertBoundedFrom A c0 F` (same configurations). -/
def toSem (tr : TraceSemU A I) {c0 : Config I} {F : Nat} (hcb : CertBoundedFrom A c0 F)
    (h0 : tr.cfg 0 = c0) : TraceSem A F I where
  cfg := tr.cfg
  step i := (tr.step i).imp (fun ⟨tid, _, hs⟩ =>
    ⟨tid, stepSem_of_certBounded hcb (tr.reach h0 i).choose_spec hs⟩) id

end TraceSemU

/-- **Transfer of traces** (prototype §2.1 `TraceSemUToSem`, proved). -/
theorem traceSemUToSem {A : Arch} {c0 : Config I} {F : Nat} (hcb : CertBoundedFrom A c0 F)
    (tr : TraceSemU A I) (h0 : tr.cfg 0 = c0) : ∃ tr' : TraceSem A F I, tr'.cfg = tr.cfg :=
  ⟨tr.toSem hcb h0, rfl⟩

/-- **Weak fairness transfers** along a fuel-free trace from `c0`. -/
theorem weakFairSem_of_weakFairSemU {A : Arch} {c0 : Config I} {F : Nat} (hcb : CertBoundedFrom A c0 F)
    (tr : TraceSemU A I) (h0 : tr.cfg 0 = c0) (hf : WeakFairSemU A tr.cfg) : WeakFairSem A F tr.cfg := by
  intro tid ⟨n, hn⟩
  have hinf := hf tid ⟨n, fun i hi => let ⟨c', h⟩ := hn i hi; ⟨c', stepSemU_of_stepSem h⟩⟩
  intro m
  obtain ⟨i, hi, hs⟩ := hinf m
  exact ⟨i, hi, (stepSemU_iff hcb (tr.reach h0 i).choose_spec).1 hs⟩

/-- The converse: on a fuel-free trace from `c0`, weak fairness at `F` is
fuel-free weak fairness. -/
theorem weakFairSemU_of_weakFairSem {A : Arch} {c0 : Config I} {F : Nat} (hcb : CertBoundedFrom A c0 F)
    (tr : TraceSemU A I) (h0 : tr.cfg 0 = c0) (hf : WeakFairSem A F tr.cfg) : WeakFairSemU A tr.cfg := by
  intro tid ⟨n, hn⟩
  have hinf := hf tid ⟨n, fun i hi => (enabledSemU_iff hcb (tr.reach h0 i).choose_spec).1 (hn i hi)⟩
  intro m
  obtain ⟨i, hi, hs⟩ := hinf m
  exact ⟨i, hi, stepSemU_of_stepSem hs⟩

/-! ## Transfer of liveness, progress and termination -/

/-- **Liveness transfer, any fairness**: a fixed-fuel liveness theorem at `F`
under `Fair` gives the fuel-free one under any `FairU` that implies `Fair`
on fuel-free traces from `c0`. -/
theorem liveTransferG {A : Arch} {c0 : Config I} {F : Nat} {Fair FairU : (Nat → Config I) → Prop}
    {W D : Nat → Config I → Prop} (hcb : CertBoundedFrom A c0 F)
    (hfair : ∀ tr : TraceSemU A I, tr.cfg 0 = c0 → FairU tr.cfg → Fair tr.cfg)
    (h : LiveFromSem A F c0 Fair W D) : LiveFromSemU A c0 FairU W D :=
  fun tr h0 hf => h (tr.toSem hcb h0) h0 (hfair tr h0 hf)

/-- **Liveness transfer** (prototype §2.1 `LiveTransfer`, proved). -/
theorem liveTransfer {A : Arch} {c0 : Config I} {F : Nat} {W D : Nat → Config I → Prop}
    (hcb : CertBoundedFrom A c0 F)
    (h : LiveFromSem A F c0 (fun cfg => WeakFairSem A F cfg ∧ MemFair A cfg) W D) :
    LiveFromSemU A c0 (fun cfg => WeakFairSemU A cfg ∧ MemFair A cfg) W D :=
  liveTransferG hcb (fun tr h0 hf => ⟨weakFairSem_of_weakFairSemU hcb tr h0 hf.1, hf.2⟩) h

/-- **Progress transfer, any fairness.** -/
theorem progressTransferG {A : Arch} {c0 : Config I} {F : Nat} {Fair FairU : (Nat → Config I) → Prop}
    {W D : Nat → Config I → Prop} (hcb : CertBoundedFrom A c0 F)
    (hfair : ∀ tr : TraceSemU A I, tr.cfg 0 = c0 → FairU tr.cfg → Fair tr.cfg)
    (h : SpinSem.ProgressFromSem A F c0 Fair W D) : ProgressFromSemU A c0 FairU W D :=
  fun tr h0 hf => h (tr.toSem hcb h0) h0 (hfair tr h0 hf)

/-- **Progress transfer.** -/
theorem progressTransfer {A : Arch} {c0 : Config I} {F : Nat} {W D : Nat → Config I → Prop}
    (hcb : CertBoundedFrom A c0 F)
    (h : SpinSem.ProgressFromSem A F c0 (fun cfg => WeakFairSem A F cfg ∧ MemFair A cfg) W D) :
    ProgressFromSemU A c0 (fun cfg => WeakFairSemU A cfg ∧ MemFair A cfg) W D :=
  progressTransferG hcb (fun tr h0 hf => ⟨weakFairSem_of_weakFairSemU hcb tr h0 hf.1, hf.2⟩) h

/-- **Termination-under-fairness transfer, any fairness.** -/
theorem termFromTransferG {A : Arch} {c0 : Config I} {F : Nat} {Fair FairU : (Nat → Config I) → Prop}
    (hcb : CertBoundedFrom A c0 F)
    (hfair : ∀ tr : TraceSemU A I, tr.cfg 0 = c0 → FairU tr.cfg → Fair tr.cfg)
    (h : Term.TermFromSem A F c0 Fair) : TermFromSemU A c0 FairU :=
  fun tr h0 hf => h (tr.toSem hcb h0) h0 (hfair tr h0 hf)

/-- **Termination-under-fairness transfer.** -/
theorem termFromTransfer {A : Arch} {c0 : Config I} {F : Nat} (hcb : CertBoundedFrom A c0 F)
    (h : Term.TermFromSem A F c0 (fun cfg => WeakFairSem A F cfg ∧ MemFair A cfg)) :
    TermFromSemU A c0 (fun cfg => WeakFairSemU A cfg ∧ MemFair A cfg) :=
  termFromTransferG hcb (fun tr h0 hf => ⟨weakFairSem_of_weakFairSemU hcb tr h0 hf.1, hf.2⟩) h

/-- **Bounded-termination transfer** (prototype §2.1 `TermTransfer`, proved): the
bound `K` at fuel `F` bounds every fuel-free trace from `c0`. -/
theorem termTransfer {A : Arch} {c0 : Config I} {F : Nat} (hcb : CertBoundedFrom A c0 F)
    (h : Term.TermBoundSem A F c0) : TermBoundSemU A c0 := by
  obtain ⟨K, hK⟩ := h
  exact ⟨K, fun tr h0 => hK (tr.toSem hcb h0) h0⟩

end Kraken.Promising.Live.CertBounded
