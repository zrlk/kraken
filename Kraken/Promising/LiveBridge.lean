/-
**The bridge between the
executable and the semantic machine, as statements.** ISA-neutral. Nothing
existing is changed; nothing here is used elsewhere.

Two machines:
- the **executable machine**: `succs` (`Machine.lean`), `Reachable`,
  `TraceS`, `Enabled`, `WeakFair`; a step of a thread with promises is kept
  iff `certify` (a DFS whose visited set ignores the remaining fuel) says
  `certified`, and a promise is a write recorded by `certify` on the
  *pre*-promise state with constraining view `≤ |M|`;
- the **semantic machine**: `StepSem` (`LiveSem.lean`), certification is
  `CertOkN` (some run within `fuel` empties the promise set) and the promise
  rule is the paper's (any message of the thread, the *post*-promise thread
  must be `CertOkN`). `ReachableSem` below is its reachability.

This file states (as `Prop`s; open) the facts Q1–Q4 below and proves the
reductions that need no new machine lemma:

- `ReachableK`: reachability along `SuccKind` steps (an instruction step, or
  a promise of a `CertWrite`), fuel-free. **Both machines are inside it**:
  `ReachableK.of_reachable` (proved, `succs_cases`) and
  `ReachableK.of_reachableSem` (proved from `PromProjection`, Q3). Every
  Stage 2 proof uses `succs` only through `succs_cases`, so the Stage 2
  chain can be proved once over `ReachableK`.
- `PromProjection` (Q3; **proved**: `Proj.promProjection`, `PromProjection.lean`, no hypothesis): a semantic promise is a `CertWriteN` of the
  pre-promise state with `ν ≤ |M|` (SLR's Lemma 1, projection direction).
- `PromReplay` (Q2, open): the converse (replay direction).
- `CertifySoundN'` (Q1, open; the `certified` half and the per-write
  `CertWriteN` refinement of the existing `certify_soundN`).
- `StepSemOfSuccs`, `MemSuccsOfStepSem`, `EnabledIff`, `ReachableIff`,
  `TraceToSem`, `WeakFairOfWeakFairSem` (Q4, open); `reachableSem_of_reachable`
  (proved from `StepSemOfSuccs`).
- `MemSuccsOfStepSem` is **false** for today's `certify`: concrete Toy
  counterexamples (an instruction step and a promise step that `succs`
  drops although the semantic machine takes them) are evaluated in
  `LiveBridgeTests.lean`.
- `stepSem_mono`, `reachableSem_mono` (proved): the semantic machine is
  monotone in `fuel` (`succs` is not, see the tests), so "for every `fuel`"
  on `ReachableSem` is reachability with unbounded certification.
-/
import Kraken.Promising.LiveSem
import Kraken.Promising.ReachableK

namespace Kraken.Promising.Live.Bridge

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem

variable {I : ISA}

/-! ## Reachability on the semantic machine and along `SuccKind` -/

/-- Reachability along semantic steps (`StepSem`) at certification fuel
`fuel`. -/
inductive ReachableSem (A : Arch) (fuel : Nat) : Config I → Config I → Prop
  | refl (c : Config I) : ReachableSem A fuel c c
  | step {c c' c'' : Config I} (tid : Nat) : StepSem A fuel tid c c' → ReachableSem A fuel c' c'' →
      ReachableSem A fuel c c''

-- `ReachableK` and `ReachableK.of_reachable` are in `ReachableK.lean` (moved by the K-world chain).

/-- A semantic instruction step is a `SuccKind` instruction step. -/
theorem succKind_of_instrSem {A : Arch} {fuel tid : Nat} {c c' : Config I}
    (h : InstrSem A fuel tid c c') : SuccKind A c c' := by
  obtain ⟨t, outs, o, ht, hs, ho, -, rfl⟩ := h
  exact .instr ht hs ho

/-- A semantic step keeps the number of threads' bound (re-export of
`Config.Bnd.semStep` for the reductions below). -/
theorem bnd_of_stepSem {A : Arch} {fuel tid : Nat} {c c' : Config I} (hb : c.Bnd)
    (h : StepSem A fuel tid c c') : c'.Bnd :=
  hb.semStep h

/-! ## Q3: the projection direction of Lemma 1 (proved in `PromProjection.lean`) -/

/-- **A write of a certifying run within `fuel`**: thread `tid`, run alone
from `(t, mem)`, performs `p` (message and constraining view) as "promise
now" at its `k + 1`-st instruction (`k < fuel`), and the run can then empty
its promise set within the remaining `fuel - k - 1` instructions. (A run
that certified before the write keeps an empty promise set, so this covers
both of `certify.go`'s recording points.) The fuel-bounded refinement of
`CertWrite`. -/
def CertWriteN (A : Arch) (tid : Nat) (t : Thread I) (mem : Memory) (fuel : Nat) (p : Msg × View) : Prop :=
  ∃ (k : Nat) (t1 : Thread I) (mem1 : Memory) (outs : List (Except String (Outcome I))) (o : Outcome I),
    k < fuel ∧ ThreadNPn A tid k (t, mem) (t1, mem1) ∧ stepOne A t1 tid mem1 = some outs ∧ .ok o ∈ outs ∧
      p ∈ o.promisedNow ∧ CertOkN A tid o.thread o.mem (fuel - k - 1)

/-- `CertWriteN` forgets to the existing `CertWrite`. -/
theorem CertWriteN.certWrite {A : Arch} {tid : Nat} {t : Thread I} {mem : Memory} {fuel : Nat}
    {p : Msg × View} (h : CertWriteN A tid t mem fuel p) : CertWrite A tid t mem p := by
  obtain ⟨k, t1, mem1, outs, o, -, hrun, hs, ho, hp, -⟩ := h
  refine ⟨t1, mem1, outs, o, ?_, hs, ho, hp⟩
  clear hs ho hp
  generalize ht : (t, mem) = a at hrun
  generalize ht1 : (t1, mem1) = b at hrun
  induction hrun generalizing t mem with
  | refl => subst ht; cases ht1; exact .refl _
  | step h₁ _ ih => subst ht; exact .step h₁ (ih rfl ht1)

/-- **Lemma 1 for the paper's promise rule, projection direction (Q3;
proved as `Proj.promProjection` in `PromProjection.lean`).** If the thread,
after promising `w` at `|M| + 1`, can empty its
promise set within `fuel` instructions against `mem ++ w`, then `w` is
written, with a constraining view `ν ≤ |M|`, by a certifying run of the
pre-promise thread within `fuel` instructions.

Proof plan: map the post-run step by step to a pre-run
on `mem`; the fulfilment of `|M| + 1` becomes the "promise now" of `w`;
fresh writes before it sit one timestamp lower; views are related by the
monotone relabelling `v ↦ if v ≤ |M| then v else v + 1` up to the
fulfilment, and by a provenance relation after it. The post-run never reads
`|M| + 1` while it is outstanding (`readSuccs` skips own promises), and the
fulfilment check `bound < |M| + 1` gives `ν ≤ |M|`. Needs `t.Bnd mem.last`. -/
def PromProjection (A : Arch) (I : ISA) : Prop :=
  ∀ (fuel tid : Nat) (t : Thread I) (mem : Memory) (w : Msg), t.Bnd mem.last → w.tid = tid →
    CertOkN A tid (promThread t mem w) (mem.append w).1 fuel →
      ∃ ν, ν ≤ mem.last ∧ CertWriteN A tid t mem fuel (w, ν)

/-- The message of a semantic promise needs no `tid` rewrite. -/
theorem msg_with_tid {w : Msg} {tid : Nat} (h : w.tid = tid) : { w with tid } = w := by
  cases w; cases h; rfl

/-- **A semantic promise step is a `SuccKind` promise step**, given Q3. -/
theorem succKind_of_promSem {A : Arch} (hP : PromProjection A I) {fuel tid : Nat} {c c' : Config I}
    (hb : c.Bnd) (h : PromSem A fuel tid c c') : SuccKind A c c' := by
  obtain ⟨t, w, ht, hw, hc, rfl⟩ := h
  obtain ⟨ν, -, hwn⟩ := hP fuel tid t c.mem w (hb tid t ht) hw hc
  have hk := SuccKind.promise (p := (w, ν)) ht hwn.certWrite
  simp only [msg_with_tid hw] at hk
  exact hk

/-- **A semantic step is a `SuccKind` step**, given Q3. -/
theorem succKind_of_stepSem {A : Arch} (hP : PromProjection A I) {fuel tid : Nat} {c c' : Config I}
    (hb : c.Bnd) (h : StepSem A fuel tid c c') : SuccKind A c c' :=
  h.elim succKind_of_instrSem (succKind_of_promSem hP hb)

/-- **The semantic machine is inside `ReachableK`**, given Q3. -/
theorem ReachableK.of_reachableSem {A : Arch} (hP : PromProjection A I) {fuel : Nat} {c c' : Config I}
    (hb : c.Bnd) (h : ReachableSem A fuel c c') : ReachableK A c c' := by
  induction h with
  | refl c => exact .refl c
  | step _ hs _ ih => exact .step (succKind_of_stepSem hP hb hs) (ih (hb.semStep hs))

/-! ## Monotonicity in fuel (semantic machine) -/

theorem certOkN_mono {A : Arch} {tid n m : Nat} {t : Thread I} {mem : Memory}
    (h : CertOkN A tid t mem n) (hm : n ≤ m) : CertOkN A tid t mem m := by
  obtain ⟨t', mem', hr, hp⟩ := h
  exact ⟨t', mem', hr.mono hm, hp⟩

theorem stepSem_mono {A : Arch} {fuel fuel' tid : Nat} {c c' : Config I} (hf : fuel ≤ fuel')
    (h : StepSem A fuel tid c c') : StepSem A fuel' tid c c' := by
  rcases h with ⟨t, outs, o, ht, hs, ho, hc, rfl⟩ | ⟨t, w, ht, hw, hc, rfl⟩
  · exact .inl ⟨t, outs, o, ht, hs, ho, certOkN_mono hc hf, rfl⟩
  · exact .inr ⟨t, w, ht, hw, certOkN_mono hc hf, rfl⟩

/-- **`ReachableSem` is monotone in `fuel`**: a finite semantic run with
certifications of any lengths is a run at their maximum. -/
theorem reachableSem_mono {A : Arch} {fuel fuel' : Nat} {c c' : Config I} (hf : fuel ≤ fuel')
    (h : ReachableSem A fuel c c') : ReachableSem A fuel' c c' := by
  induction h with
  | refl c => exact .refl c
  | step tid hs _ ih => exact .step tid (stepSem_mono hf hs) ih

/-! ## Q2: the replay direction of Lemma 1 (proved in `PromReplay.lean`) -/

/-- **Lemma 1, replay direction (Q2; proved as `Proj.promReplay` in
`PromReplay.lean`).** A write `(w, ν)` of a
certifying run within `fuel` whose constraining view is `≤ |M|` can be
promised: the thread with `w` promised at `|M| + 1` certifies against
`mem ++ w` within the same `fuel` (the replay of an `n`-step run is an
`n`-step run). Proof plan: the same relabelling
simulation as Q3, in the other direction; before the write, a read of
`w.loc` with a bound above `|M|` would raise `coh w.loc` above `|M|` and
contradict `ν ≤ |M|`. -/
def PromReplay (A : Arch) (I : ISA) : Prop :=
  ∀ (fuel tid : Nat) (t : Thread I) (mem : Memory) (w : Msg) (ν : View), t.Bnd mem.last →
    CertWriteN A tid t mem fuel (w, ν) → ν ≤ mem.last →
      CertOkN A tid (promThread t mem w) (mem.append w).1 fuel

/-! ## Q1: `certify` soundness at the fuel (proved in `CertifySoundN2.lean`) and completeness (false today) -/

/-- **Fuel-bounded soundness of `certify` (Q1; proved as
`certifySoundN'` in `CertifySoundN2.lean` the `certify` bridge; the cache-threaded
form is `certify_soundN2`).** On a fresh
cache: `certified` implies `CertOkN fuel`, and every recorded write is a
`CertWriteN` (the existing `certify_soundN` gives only `writes ≠ [] →
CertOkN`). Same induction as `certify_go_soundN`, with each entry's `ws`
tracked as writes of its path. (The cache-threaded form is as in
`certify_soundN`.) -/
def CertifySoundN' (A : Arch) (I : ISA) : Prop :=
  ∀ (fuel tid : Nat) (t : Thread I) (mem : Memory),
    ((certify A {} t tid mem fuel).1.certified = true → CertOkN A tid t mem fuel) ∧
    ∀ p ∈ (certify A {} t tid mem fuel).1.writes, CertWriteN A tid t mem fuel p

/-- **Completeness of `certify` (Q1).** **False for today's `certify`**
(`LiveBridgeTests.lean`, `cex1`: a thread whose ld step is certifiable
within 3 instructions but `certify` answers `false` at fuels 4 and 5).
Provable for a breadth-first `go` (variant β) with exact `hasDeadPromise`
pruning (`deadPromise_exact`). -/
def CertifyCompleteN (A : Arch) (I : ISA) : Prop :=
  ∀ (fuel tid : Nat) (t : Thread I) (mem : Memory),
    CertOkN A tid t mem fuel → (certify A {} t tid mem fuel).1.certified = true

/-- **`hasDeadPromise` pruning is exact** (needed by any completeness proof;
open, ~60 lines: `coh_lt_of_certOkN` plus monotonicity of `vwNew`, `vCAP`,
which are part of every write's pre-view). -/
def DeadPromiseExact (A : Arch) (I : ISA) : Prop :=
  ∀ (n tid : Nat) (t : Thread I) (mem : Memory), t.hasDeadPromise mem = true → ¬ CertOkN A tid t mem n

/-! ## Q4: the bridge (executable ⊆ semantic proved in `StepSemOfSuccs.lean`; the converse false today) -/

/-- **Executable ⊆ semantic** (one step; proved for `[I.LawfulState]` as
`stepSemOfSuccs` in `StepSemOfSuccs.lean`, with
`reachableSem_of_reachable'` and the binder-free AArch64/x64 forms in
`StepSemOfSuccs{A64,X64}.lean`). Holds for today's `certify` by
`CertifySoundN'` (instruction steps) and `PromReplay` (promise steps), in
the cache-threaded form: `succs` shares one cache across the steps and
promises of all threads, so the reduction uses `CertifySoundN'` stated
over a cache invariant (`CacheSoundOnN'`, the `CacheSoundOnN` pattern of
`certify_soundN` extended with each entry's writes), not only on a fresh
cache. **`I.LawfulState` is needed**: the cache is a hash map keyed on
threads, so the reduction needs `BEq` on states to be equality on the keys
`succs` asks about (`KeyLawful`); with an unlawful `BEq` a cached result
answers for a different thread state, and `succs` offers a promise that
the semantic machine allows only at a larger fuel
(`LiveBridgeTestsLawful.lean`, `BadKey`), so the statement is false for
general `I`. -/
def StepSemOfSuccs (A : Arch) (I : ISA) : Prop :=
  ∀ (fuel : Nat) (c c' : Config I), c.Bnd → c' ∈ (succs A c fuel).1 → ∃ tid, StepSem A fuel tid c c'

/-- **Semantic ⊆ executable** (one step). **False for today's `certify`**
(`LiveBridgeTests.lean`: `cex1` drops an `InstrSem` step, `cex4` a `PromSem`
step, at fuels where the semantic step exists). Needs a complete `certify`
(Q1) and complete promises (Q3 plus writes completeness, Q3 (d)). -/
def MemSuccsOfStepSem (A : Arch) (I : ISA) : Prop :=
  ∀ (fuel tid : Nat) (c c' : Config I), c.Bnd → StepSem A fuel tid c c' → c' ∈ (succs A c fuel).1

/-- Enabledness agrees (needs both directions). -/
def EnabledIff (A : Arch) (I : ISA) : Prop :=
  ∀ (fuel tid : Nat) (c : Config I), c.Bnd → (Enabled A fuel tid c ↔ EnabledSem A fuel tid c)

/-- Reachability agrees from a bounded start (needs both directions). -/
def ReachableIff (A : Arch) (I : ISA) : Prop :=
  ∀ (fuel : Nat) (c0 c : Config I), c0.Bnd → (Reachable A fuel c0 c ↔ ReachableSem A fuel c0 c)

/-- Every executable trace from a bounded start is a semantic trace (proved
for `[I.LawfulState]` as `traceToSem` in `StepSemOfSuccs.lean`). -/
def TraceToSem (A : Arch) (I : ISA) : Prop :=
  ∀ (fuel : Nat) (tr : TraceS A fuel I), (tr.cfg 0).Bnd → ∃ tr' : TraceSem A fuel I, tr'.cfg = tr.cfg

/-- On an executable trace, semantic weak fairness gives executable weak
fairness (needs `Enabled → EnabledSem`, i.e. `StepSemOfSuccs`, and the
thread identification of a step). The converse needs `EnabledSem →
Enabled`, i.e. completeness. -/
def WeakFairOfWeakFairSem (A : Arch) (I : ISA) : Prop :=
  ∀ (fuel : Nat) (tr : TraceS A fuel I), (tr.cfg 0).Bnd → WeakFairSem A fuel tr.cfg → WeakFair A fuel tr.cfg

/-- **Executable reachability is semantic reachability**, given
`StepSemOfSuccs` (proved reduction; `Config.Bnd.succ` carries the bound). -/
theorem reachableSem_of_reachable [I.LawfulState] {A : Arch} (hS : StepSemOfSuccs A I) {fuel : Nat}
    {c c' : Config I} (hb : c.Bnd) (h : Reachable A fuel c c') : ReachableSem A fuel c c' := by
  induction h with
  | refl c => exact .refl c
  | step hs _ ih =>
    obtain ⟨tid, hst⟩ := hS fuel _ _ hb hs
    exact .step tid hst (ih (hb.succ hs))

end Kraken.Promising.Live.Bridge
