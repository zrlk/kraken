/-
**The fuel-free semantic machine `…SemInf`, the
lowering target** (ISA-neutral, architecture-neutral, program-independent).
Nothing existing is changed.

The semantic machine of `LiveSem.lean` (`InstrSem`/`PromSem`/`StepSem A fuel
tid`) certifies within `fuel` instructions (`CertOkN`, `LiveWfInstr.lean`).
This file restates it rule for rule with the **unbounded** certification
`CertOk` (`PromiseSafe.lean`: some promise-free solo run `ThreadNP` empties
the promise set), so that a source machine that certifies unboundedly (the
WeakCore promise machine) can be related to Kraken without mentioning fuel:

- `InstrSemInf`, `PromSemInf`, `StepSemInf`: `InstrSem`/`PromSem`/`StepSem`
  with `CertOk A tid t mem` for `CertOkN A tid t mem fuel`;
- `ReachableSemInf` (as `ReachableSem`), `TraceSemInf` (as `TraceSem`,
  stuttering only at final configurations), `EnabledSemInf`,
  `WeakFairSemInf`, and the liveness/termination predicates
  `LiveFromSemInf`, `ProgressFromSemInf`, `TermFromSemInf`,
  `TermBoundSemInf`;
- `Config.FaultFreeSemInf A init`: no `ReachableSemInf`-reachable
  configuration has a faulting step.

**Exact relation to the other machines** (all unconditional unless noted):

- `threadNP_iff_exists_threadNPn`, `certOk_iff_exists_certOkN`: an unbounded
  solo run is a run of some length;
- `instrSemInf_iff_instrSemU`, `promSemInf_iff`, `stepSemInf_iff_stepSemU`:
  one `…SemInf` step is one `StepSem` step at some fuel (`CertBounded.StepSemU`);
- `reachableSemInf_iff`: `ReachableSemInf A c c' ↔ ∃ fuel, ReachableSem A
  fuel c c'` (a finite run has a maximal certification length,
  `stepSem_mono`);
- `ReachableK.of_reachableSemInf`: from a bounded start (`Config.Bnd`), the
  Inf machine is inside `ReachableK` (`SuccKind`, `PromProjection.lean`);
- `configInv_reachableSemInf`: per-thread invariants (`StepPreserves`,
  `InvLink.lean`) hold at every `ReachableSemInf`-reachable configuration
  from a `Config.init` start;
- `TraceSemInf.toU`/`TraceSemU.toInf` (same configurations),
  `weakFairSemInf_iff`, and `liveFromSemInf_iff`, `progressFromSemInf_iff`,
  `termFromSemInf_iff`, `termBoundSemInf_iff`: the Inf machine's traces and
  liveness predicates are those of the fuel-free `…SemU` machine of
  `LiveCertBounded.lean`, for every fairness predicate.

**Transfers** of the `∀ fuel` statements: `forall_reachableSemInf_iff`
(safety over reachable configurations), `TermBoundSemInf.toSem`, and the
`CertBoundedFrom` forms `liveTransferInf`, `progressTransferInf`,
`termFromTransferInf`, `termTransferInf`. (`∀ fuel, TermBoundSem A fuel c0`
alone does **not** give `TermBoundSemInf A c0`: the bound may grow with the
fuel, and a trace that needs ever larger certifications is a trace at no
fixed fuel; `termTransferInf` needs `CertBoundedFrom`.) Fault freedom:
`Config.FaultFreeSemInf.iff_forall` (`ChainK/InfTwin.lean`).
-/
import Kraken.Promising.LiveCertBounded
import Kraken.Promising.PromProjection
import Kraken.Promising.Faults
import Kraken.Promising.InvLink

namespace Kraken.Promising.Live.Inf

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem Kraken.Promising.Live.Bridge
open Kraken.Promising.Live.CertBounded

variable {I : ISA}

/-! ## Unbounded solo runs are bounded solo runs of some length -/

/-- A run of some length is a promise-free run. -/
theorem _root_.Kraken.Promising.Live.ThreadNPn.threadNP {A : Arch} {tid n : Nat} {p q : Thread I × Memory} (h : ThreadNPn A tid n p q) :
    ThreadNP A tid p q := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step hs ih

/-- **An unbounded promise-free solo run is a run of some length.** -/
theorem threadNP_iff_exists_threadNPn {A : Arch} {tid : Nat} {p q : Thread I × Memory} :
    ThreadNP A tid p q ↔ ∃ n, ThreadNPn A tid n p q := by
  refine ⟨fun h => ?_, fun ⟨_, h⟩ => h.threadNP⟩
  induction h with
  | refl p => exact ⟨0, .refl _ _⟩
  | step hs _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .step hs h⟩

/-- **Unbounded certification is certification within some fuel.** -/
theorem certOk_iff_exists_certOkN {A : Arch} {tid : Nat} {t : Thread I} {mem : Memory} :
    CertOk A tid t mem ↔ ∃ n, CertOkN A tid t mem n := by
  constructor
  · rintro ⟨t', mem', h, hp⟩
    obtain ⟨n, h⟩ := threadNP_iff_exists_threadNPn.mp h
    exact ⟨n, t', mem', h, hp⟩
  · rintro ⟨n, t', mem', h, hp⟩
    exact ⟨t', mem', h.threadNP, hp⟩

theorem certOk_of_certOkN {A : Arch} {tid n : Nat} {t : Thread I} {mem : Memory}
    (h : CertOkN A tid t mem n) : CertOk A tid t mem :=
  certOk_iff_exists_certOkN.mpr ⟨n, h⟩

/-! ## Steps with unbounded certification -/

/-- **An instruction step of `tid` with unbounded certification**: some
successful outcome of its next instruction, after which the thread can empty
its promise set alone (`InstrSem` with `CertOk` for `CertOkN … fuel`). -/
def InstrSemInf (A : Arch) (tid : Nat) (c c' : Config I) : Prop :=
  ∃ t outs o, c.threads[tid]? = some t ∧ stepOne A t tid c.mem = some outs ∧ .ok o ∈ outs ∧
    CertOk A tid o.thread o.mem ∧ c' = c.withThread tid o.thread o.mem

/-- **A promise step of `tid` (the paper's rule) with unbounded
certification**: append any message of `tid` and promise it; the thread must
then be certifiable (`PromSem` with `CertOk` for `CertOkN … fuel`). -/
def PromSemInf (A : Arch) (tid : Nat) (c c' : Config I) : Prop :=
  ∃ (t : Thread I) (w : Msg), c.threads[tid]? = some t ∧ w.tid = tid ∧
    CertOk A tid (promThread t c.mem w) (c.mem.append w).1 ∧
    c' = c.withThread tid (promThread t c.mem w) (c.mem.append w).1

/-- A step of thread `tid` (fuel-free). -/
def StepSemInf (A : Arch) (tid : Nat) (c c' : Config I) : Prop :=
  InstrSemInf A tid c c' ∨ PromSemInf A tid c c'

/-- Reachability along fuel-free semantic steps (`StepSemInf`). -/
inductive ReachableSemInf (A : Arch) : Config I → Config I → Prop
  | refl (c : Config I) : ReachableSemInf A c c
  | step {c c' c'' : Config I} (tid : Nat) : StepSemInf A tid c c' → ReachableSemInf A c' c'' →
      ReachableSemInf A c c''

/-- **A trace of the fuel-free semantic machine**, stuttering only at a final
configuration (as `TraceSem`). -/
structure TraceSemInf (A : Arch) (I : ISA) where
  cfg : Nat → Config I
  step : ∀ i, (∃ tid, StepSemInf A tid (cfg i) (cfg (i + 1))) ∨ ((cfg i).final = true ∧ cfg (i + 1) = cfg i)

/-- Thread `tid` can take a step. -/
def EnabledSemInf (A : Arch) (tid : Nat) (c : Config I) : Prop :=
  ∃ c', StepSemInf A tid c c'

/-- **Weak fairness** (fuel-free): a thread enabled from some point on takes
a step (instruction or promise) infinitely often. -/
def WeakFairSemInf (A : Arch) (cfg : Nat → Config I) : Prop :=
  ∀ tid, EvAlways (fun i => EnabledSemInf A tid (cfg i)) →
    InfOften (fun i => StepSemInf A tid (cfg i) (cfg (i + 1)))

/-- **Liveness from `c0`** on the fuel-free semantic machine (as `LiveFromSem`). -/
def LiveFromSemInf (A : Arch) (c0 : Config I) (Fair : (Nat → Config I) → Prop)
    (Waiting Done : Nat → Config I → Prop) : Prop :=
  ∀ tr : TraceSemInf A I, tr.cfg 0 = c0 → Fair tr.cfg →
    ∀ tid i, Waiting tid (tr.cfg i) → ∃ j, i ≤ j ∧ Done tid (tr.cfg j)

/-- **Deadlock-freedom from `c0`** on the fuel-free semantic machine (as
`SpinSem.ProgressFromSem`). -/
def ProgressFromSemInf (A : Arch) (c0 : Config I) (Fair : (Nat → Config I) → Prop)
    (Waiting Done : Nat → Config I → Prop) : Prop :=
  ∀ tr : TraceSemInf A I, tr.cfg 0 = c0 → Fair tr.cfg →
    ∀ tid i, Waiting tid (tr.cfg i) → ∃ j, i ≤ j ∧ ∃ tid', ¬ Done tid' (tr.cfg i) ∧ Done tid' (tr.cfg j)

/-- **Termination under `Fair`** on the fuel-free semantic machine (as
`Term.TermFromSem`). -/
def TermFromSemInf (A : Arch) (c0 : Config I) (Fair : (Nat → Config I) → Prop) : Prop :=
  ∀ tr : TraceSemInf A I, tr.cfg 0 = c0 → Fair tr.cfg → ∃ j, (tr.cfg j).final = true

/-- **Bounded termination under every schedule** on the fuel-free semantic
machine (as `Term.TermBoundSem`). -/
def TermBoundSemInf (A : Arch) (c0 : Config I) : Prop :=
  ∃ K, ∀ tr : TraceSemInf A I, tr.cfg 0 = c0 → (tr.cfg K).final = true

end Kraken.Promising.Live.Inf

namespace Kraken.Promising

open Kraken.Promising.Live.Inf

variable {I : ISA}

/-- **Fault freedom on the fuel-free semantic machine**: no configuration
`ReachableSemInf`-reachable from `init` has a faulting step
(`Config.FaultFreeSem` with `ReachableSemInf` for `ReachableSem A fuel`). -/
def Config.FaultFreeSemInf (A : Arch) (init : Config I) : Prop :=
  ∀ c, ReachableSemInf A init c → ∀ tid m, ¬ c.FaultStep A tid m

end Kraken.Promising

namespace Kraken.Promising.Live.Inf

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem Kraken.Promising.Live.Bridge
open Kraken.Promising.Live.CertBounded

variable {I : ISA}

/-! ## One step: Inf = some fuel -/

theorem instrSemInf_of_instrSem {A : Arch} {fuel tid : Nat} {c c' : Config I}
    (h : InstrSem A fuel tid c c') : InstrSemInf A tid c c' := by
  obtain ⟨t, outs, o, ht, hs, ho, hc, rfl⟩ := h
  exact ⟨t, outs, o, ht, hs, ho, certOk_of_certOkN hc, rfl⟩

theorem promSemInf_of_promSem {A : Arch} {fuel tid : Nat} {c c' : Config I}
    (h : PromSem A fuel tid c c') : PromSemInf A tid c c' := by
  obtain ⟨t, w, ht, hw, hc, rfl⟩ := h
  exact ⟨t, w, ht, hw, certOk_of_certOkN hc, rfl⟩

theorem stepSemInf_of_stepSem {A : Arch} {fuel tid : Nat} {c c' : Config I}
    (h : StepSem A fuel tid c c') : StepSemInf A tid c c' :=
  h.imp instrSemInf_of_instrSem promSemInf_of_promSem

/-- **A fuel-free instruction step is an instruction step at some fuel.** -/
theorem instrSemInf_iff_instrSemU {A : Arch} {tid : Nat} {c c' : Config I} :
    InstrSemInf A tid c c' ↔ InstrSemU A tid c c' := by
  refine ⟨fun h => ?_, fun ⟨_, h⟩ => instrSemInf_of_instrSem h⟩
  obtain ⟨t, outs, o, ht, hs, ho, hc, rfl⟩ := h
  obtain ⟨n, hn⟩ := certOk_iff_exists_certOkN.mp hc
  exact ⟨n, t, outs, o, ht, hs, ho, hn, rfl⟩

/-- **A fuel-free promise step is a promise step at some fuel.** -/
theorem promSemInf_iff {A : Arch} {tid : Nat} {c c' : Config I} :
    PromSemInf A tid c c' ↔ ∃ fuel, PromSem A fuel tid c c' := by
  refine ⟨fun h => ?_, fun ⟨_, h⟩ => promSemInf_of_promSem h⟩
  obtain ⟨t, w, ht, hw, hc, rfl⟩ := h
  obtain ⟨n, hn⟩ := certOk_iff_exists_certOkN.mp hc
  exact ⟨n, t, w, ht, hw, hn, rfl⟩

/-- **A fuel-free step is a step at some fuel** (`StepSemU`). -/
theorem stepSemInf_iff_stepSemU {A : Arch} {tid : Nat} {c c' : Config I} :
    StepSemInf A tid c c' ↔ StepSemU A tid c c' := by
  refine ⟨fun h => ?_, fun ⟨_, h⟩ => stepSemInf_of_stepSem h⟩
  rcases h with h | h
  · obtain ⟨n, hn⟩ := instrSemInf_iff_instrSemU.mp h; exact ⟨n, .inl hn⟩
  · obtain ⟨n, hn⟩ := promSemInf_iff.mp h; exact ⟨n, .inr hn⟩

theorem enabledSemInf_iff {A : Arch} {tid : Nat} {c : Config I} :
    EnabledSemInf A tid c ↔ EnabledSemU A tid c := by
  simp only [EnabledSemInf, EnabledSemU, stepSemInf_iff_stepSemU]

/-! ## Reachability: Inf = some fuel -/

theorem ReachableSemInf.of_reachableSem {A : Arch} {fuel : Nat} {c c' : Config I}
    (h : ReachableSem A fuel c c') : ReachableSemInf A c c' := by
  induction h with
  | refl c => exact .refl c
  | step tid hs _ ih => exact .step tid (stepSemInf_of_stepSem hs) ih

/-- **Fuel-free reachability is reachability at some fuel**: a finite run
has a maximal certification length (`stepSem_mono`, `reachableSem_mono`). -/
theorem reachableSemInf_iff {A : Arch} {c c' : Config I} :
    ReachableSemInf A c c' ↔ ∃ fuel, ReachableSem A fuel c c' := by
  refine ⟨fun h => ?_, fun ⟨_, h⟩ => .of_reachableSem h⟩
  induction h with
  | refl c => exact ⟨0, .refl c⟩
  | step tid hs _ ih =>
    obtain ⟨n, hn⟩ := stepSemInf_iff_stepSemU.mp hs
    obtain ⟨f, hf⟩ := ih
    exact ⟨max n f, .step tid (stepSem_mono (Nat.le_max_left _ _) hn)
      (reachableSem_mono (Nat.le_max_right _ _) hf)⟩

/-- **The fuel-free machine is inside `ReachableK`**, from a bounded start
(`ReachableK.of_reachableSem'`, no open hypothesis). -/
theorem _root_.Kraken.Promising.Live.Bridge.ReachableK.of_reachableSemInf {A : Arch} {c c' : Config I}
    (hb : c.Bnd) (h : ReachableSemInf A c c') : ReachableK A c c' :=
  let ⟨_, hf⟩ := reachableSemInf_iff.mp h
  ReachableK.of_reachableSem' hb hf

/-- **Per-thread invariants along fuel-free runs**: `configInv_reachableK`
(`InvLink.lean`) on the `ReachableSemInf` machine from a `Config.init` start,
which is bounded (`Config.init_bnd`). -/
theorem _root_.Kraken.Promising.configInv_reachableSemInf {A : Arch} {G : Loc → Val → Prop}
    {J : Nat → I.State → Prop} (hJ : StepPreserves A G J) {sts : List I.State} {im : List (Loc × Val)}
    {c : Config I} (h0 : ConfigInv G J (Config.init sts im)) (hr : ReachableSemInf A (Config.init sts im) c) :
    ConfigInv G J c :=
  configInv_reachableK hJ h0 (ReachableK.of_reachableSemInf (Config.init_bnd _ _) hr)

/-- **Safety transfer**: a property of every configuration reachable at every
fuel is a property of every `ReachableSemInf`-reachable configuration, and
conversely. -/
theorem forall_reachableSemInf_iff {A : Arch} {c0 : Config I} {P : Config I → Prop} :
    (∀ c, ReachableSemInf A c0 c → P c) ↔ ∀ fuel c, ReachableSem A fuel c0 c → P c :=
  ⟨fun h _ c hc => h c (.of_reachableSem hc),
   fun h c hc => let ⟨f, hf⟩ := reachableSemInf_iff.mp hc; h f c hf⟩

theorem reachableSemInf_snoc {A : Arch} {tid : Nat} {c0 c c' : Config I} (hr : ReachableSemInf A c0 c)
    (hs : StepSemInf A tid c c') : ReachableSemInf A c0 c' := by
  induction hr with
  | refl => exact .step tid hs (.refl _)
  | step j h _ ih => exact .step j h (ih hs)

/-! ## Traces and fairness: Inf = U -/

/-- A fuel-free (`…SemU`) trace is an Inf trace (same configurations). -/
def _root_.Kraken.Promising.Live.CertBounded.TraceSemU.toInf {A : Arch} (tr : TraceSemU A I) :
    TraceSemInf A I where
  cfg := tr.cfg
  step i := (tr.step i).imp (fun ⟨tid, h⟩ => ⟨tid, stepSemInf_iff_stepSemU.mpr h⟩) id

/-- An Inf trace is a fuel-free (`…SemU`) trace (same configurations). -/
def TraceSemInf.toU {A : Arch} (tr : TraceSemInf A I) : TraceSemU A I where
  cfg := tr.cfg
  step i := (tr.step i).imp (fun ⟨tid, h⟩ => ⟨tid, stepSemInf_iff_stepSemU.mp h⟩) id

/-- A trace at fixed fuel is an Inf trace. -/
def _root_.Kraken.Promising.Live.Sem.TraceSem.toInf {A : Arch} {fuel : Nat} (tr : TraceSem A fuel I) :
    TraceSemInf A I :=
  tr.toU.toInf

/-- **The Inf and `…SemU` traces are the same sequences.** -/
theorem traceSemInf_iff_traceSemU {A : Arch} {cfg : Nat → Config I} :
    (∃ tr : TraceSemInf A I, tr.cfg = cfg) ↔ ∃ tr : TraceSemU A I, tr.cfg = cfg :=
  ⟨fun ⟨tr, h⟩ => ⟨tr.toU, h⟩, fun ⟨tr, h⟩ => ⟨tr.toInf, h⟩⟩

/-- Every configuration of an Inf trace from `c0` is reachable from `c0`. -/
theorem TraceSemInf.reach {A : Arch} (tr : TraceSemInf A I) {c0 : Config I} (h0 : tr.cfg 0 = c0) :
    ∀ i, ReachableSemInf A c0 (tr.cfg i)
  | 0 => h0 ▸ .refl _
  | i + 1 => by
    rcases tr.step i with ⟨tid, hs⟩ | ⟨-, he⟩
    · exact reachableSemInf_snoc (tr.reach h0 i) hs
    · rw [he]; exact tr.reach h0 i

/-- **Weak fairness on the Inf machine is fuel-free weak fairness.** -/
theorem weakFairSemInf_iff {A : Arch} {cfg : Nat → Config I} :
    WeakFairSemInf A cfg ↔ WeakFairSemU A cfg := by
  simp only [WeakFairSemInf, WeakFairSemU, enabledSemInf_iff, stepSemInf_iff_stepSemU]

/-! ## Liveness predicates: Inf = U, for every fairness -/

theorem liveFromSemInf_iff {A : Arch} {c0 : Config I} {Fair : (Nat → Config I) → Prop}
    {W D : Nat → Config I → Prop} : LiveFromSemInf A c0 Fair W D ↔ LiveFromSemU A c0 Fair W D :=
  ⟨fun h tr => h tr.toInf, fun h tr => h tr.toU⟩

theorem progressFromSemInf_iff {A : Arch} {c0 : Config I} {Fair : (Nat → Config I) → Prop}
    {W D : Nat → Config I → Prop} : ProgressFromSemInf A c0 Fair W D ↔ ProgressFromSemU A c0 Fair W D :=
  ⟨fun h tr => h tr.toInf, fun h tr => h tr.toU⟩

theorem termFromSemInf_iff {A : Arch} {c0 : Config I} {Fair : (Nat → Config I) → Prop} :
    TermFromSemInf A c0 Fair ↔ TermFromSemU A c0 Fair :=
  ⟨fun h tr => h tr.toInf, fun h tr => h tr.toU⟩

theorem termBoundSemInf_iff {A : Arch} {c0 : Config I} : TermBoundSemInf A c0 ↔ TermBoundSemU A c0 :=
  ⟨fun ⟨K, h⟩ => ⟨K, fun tr => h tr.toInf⟩, fun ⟨K, h⟩ => ⟨K, fun tr => h tr.toU⟩⟩

/-- The standard fairness (`WeakFairSemU ∧ MemFair`) restated on the Inf
machine: a fuel-free liveness result under it holds on the Inf machine. -/
theorem liveFromSemInf_of_semU {A : Arch} {c0 : Config I} {W D : Nat → Config I → Prop}
    (h : LiveFromSemU A c0 (fun cfg => WeakFairSemU A cfg ∧ MemFair A cfg) W D) :
    LiveFromSemInf A c0 (fun cfg => WeakFairSemInf A cfg ∧ MemFair A cfg) W D :=
  fun tr h0 hf => h tr.toU h0 ⟨weakFairSemInf_iff.mp hf.1, hf.2⟩

/-- `ProgressFromSemU` under `WeakFairSemU ∧ MemFair`, on the Inf machine. -/
theorem progressFromSemInf_of_semU {A : Arch} {c0 : Config I} {W D : Nat → Config I → Prop}
    (h : ProgressFromSemU A c0 (fun cfg => WeakFairSemU A cfg ∧ MemFair A cfg) W D) :
    ProgressFromSemInf A c0 (fun cfg => WeakFairSemInf A cfg ∧ MemFair A cfg) W D :=
  fun tr h0 hf => h tr.toU h0 ⟨weakFairSemInf_iff.mp hf.1, hf.2⟩

/-- `TermFromSemU` under `WeakFairSemU ∧ MemFair`, on the Inf machine. -/
theorem termFromSemInf_of_semU {A : Arch} {c0 : Config I}
    (h : TermFromSemU A c0 (fun cfg => WeakFairSemU A cfg ∧ MemFair A cfg)) :
    TermFromSemInf A c0 (fun cfg => WeakFairSemInf A cfg ∧ MemFair A cfg) :=
  fun tr h0 hf => h tr.toU h0 ⟨weakFairSemInf_iff.mp hf.1, hf.2⟩

/-! ## Transfers from fixed fuel -/

/-- **A fuel-free termination bound is a bound at every fuel.** -/
theorem TermBoundSemInf.toSem {A : Arch} {c0 : Config I} (h : TermBoundSemInf A c0) (fuel : Nat) :
    Term.TermBoundSem A fuel c0 :=
  (termBoundSemInf_iff.mp h).toSem fuel

/-- **Liveness transfer** under `CertBoundedFrom` (`liveTransfer` on the Inf
machine). -/
theorem liveTransferInf {A : Arch} {c0 : Config I} {F : Nat} {W D : Nat → Config I → Prop}
    (hcb : CertBoundedFrom A c0 F)
    (h : LiveFromSem A F c0 (fun cfg => WeakFairSem A F cfg ∧ MemFair A cfg) W D) :
    LiveFromSemInf A c0 (fun cfg => WeakFairSemInf A cfg ∧ MemFair A cfg) W D :=
  liveFromSemInf_of_semU (liveTransfer hcb h)

/-- **Progress transfer** under `CertBoundedFrom`. -/
theorem progressTransferInf {A : Arch} {c0 : Config I} {F : Nat} {W D : Nat → Config I → Prop}
    (hcb : CertBoundedFrom A c0 F)
    (h : SpinSem.ProgressFromSem A F c0 (fun cfg => WeakFairSem A F cfg ∧ MemFair A cfg) W D) :
    ProgressFromSemInf A c0 (fun cfg => WeakFairSemInf A cfg ∧ MemFair A cfg) W D :=
  progressFromSemInf_of_semU (progressTransfer hcb h)

/-- **Termination-under-fairness transfer** under `CertBoundedFrom`. -/
theorem termFromTransferInf {A : Arch} {c0 : Config I} {F : Nat} (hcb : CertBoundedFrom A c0 F)
    (h : Term.TermFromSem A F c0 (fun cfg => WeakFairSem A F cfg ∧ MemFair A cfg)) :
    TermFromSemInf A c0 (fun cfg => WeakFairSemInf A cfg ∧ MemFair A cfg) :=
  termFromSemInf_of_semU (termFromTransfer hcb h)

/-- **Bounded-termination transfer** under `CertBoundedFrom`. -/
theorem termTransferInf {A : Arch} {c0 : Config I} {F : Nat} (hcb : CertBoundedFrom A c0 F)
    (h : Term.TermBoundSem A F c0) : TermBoundSemInf A c0 :=
  termBoundSemInf_iff.mpr (termTransfer hcb h)

end Kraken.Promising.Live.Inf
