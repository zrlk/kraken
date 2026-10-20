/-
**Stage 3: fair traces exist, on both machines**
(ISA-neutral, program-independent).

Every liveness theorem has the shape "on every trace from `c0` satisfying a
fairness hypothesis, …" (`LiveFrom`, `LiveFromSem`, `Spin.ProgressFrom`,
`SpinSem.ProgressFromSem`). `TraceS` and `TraceSem` stutter only at final
configurations, so such a theorem would be vacuous at `c0` if no fair trace
started there. This module builds one, generically.

- `ReachPI A c0`: the configurations reachable from `c0` by instruction steps
  whose outcome leaves no promise (fuel-free; no certification involved).
- `MayRead A tid t l`: some successful outcome of `t`'s next instruction, at
  some memory, reads `l`. `CohTop A tid t mem o`: after the outcome `o`, the
  coherence view of every location `t` may read is at or above every message
  of that location in `mem` (the outcome reads the newest message).
- `GoodT`: a successful, promise-free, `CohTop` outcome. `Progressive A c0`:
  at every `ReachPI` configuration every thread that has not halted has a
  `GoodT` outcome.
- `rrTrace A c0`: the round-robin schedule. At index `i` it steps the first
  thread that has not halted, in the cyclic order from `i % N` (`N` threads),
  with a chosen `GoodT` outcome; once every thread has halted it repeats the
  configuration (which is final: no promise is ever made).
- From `Progressive A c0` and promise-free threads at `c0`: `rrTrace` is a
  `TraceS` at every fuel (`rrTrace_traceS`) and a `TraceSem`
  (`rrTrace_traceSem`), with `PromiseFree`, `WeakFair`, `WeakFairInstr`,
  `WeakFairSem`, `WeakFairInstrSem` and `MemFair`, all as existing
  (`LiveTrace.lean`, `LiveSem.lean`), unchanged. `fair_exists` and
  `fairSem_exists` bundle them.

**Why fair.** A thread enabled at index `j` (on either machine) has not
halted; only its own steps change its thread, and at the next index `≡ tid
(mod N)` the cyclic pick returns it, so it is scheduled within `N` steps
(`rr_sched`). **Why memory-fair.** `ReadsAt` at `j`, with any outcome (not
necessarily the one the trace took), makes `l` a `MayRead` location of
`tid`'s thread at `j`; at `tid`'s next scheduled index its thread is the same,
and `CohTop` puts its `coh l` above every message of `l` then in memory, so
above every message of `l` at any earlier index.

`Progressive` is discharged per lock (`LiveSemWitnessA64.lean`,
`LiveSemWitnessX64.lean`, `LiveSemWitnessTicketAl.lean`; runner starts via
`progressive_of_mapC`, `LiveSemWitnessRunner.lean`) by `progressive_of_inv`,
from the lock's invariant, the per-shape lemmas at the end of this file and
the invariant `FwdLeCoh` (a forwarding entry is at most the coherence view),
which every instruction keeps (`stepOne_fwdLeCoh`).

This shows that the fairness hypotheses are satisfiable from the start
configurations; it says nothing about the behaviours of the programs.
-/
import Kraken.Promising.LiveSem
import Kraken.Promising.LiveSpinX64Step
import Kraken.Promising.LiveTsoRmw

namespace Kraken.Promising.Live.Witness

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem

variable {I : ISA}

/-! ## Newest-reading promise-free steps -/

/-- The configurations reachable from `c0` by instruction steps that leave no
promise (on both machines such a step is a step: `Good.mem_succs`,
`Good.instrSem`). -/
inductive ReachPI (A : Arch) (c0 : Config I) : Config I → Prop
  | refl : ReachPI A c0 c0
  | step {c : Config I} {tid : Nat} {t : Thread I} {outs : List (Except String (Outcome I))} {o : Outcome I} :
      ReachPI A c0 c → c.threads[tid]? = some t → stepOne A t tid c.mem = some outs → .ok o ∈ outs →
      o.thread.prom = [] → ReachPI A c0 (c.withThread tid o.thread o.mem)

/-- Thread state `t` can read `l`: some successful outcome of its next
instruction, against some memory, logs a read of `l`. -/
def MayRead (A : Arch) (tid : Nat) (t : Thread I) (l : Loc) : Prop :=
  ∃ (mem : Memory) (outs : List (Except String (Outcome I))) (o : Outcome I), stepOne A t tid mem = some outs ∧
    .ok o ∈ outs ∧ ∃ ts v ν, TraceEv.read l ts v ν ∈ o.log

/-- **The outcome reads the newest message**: after `o`, the coherence view of
every location `t` may read is at or above every message of that location in
`mem`. -/
def CohTop (A : Arch) (tid : Nat) (t : Thread I) (mem : Memory) (o : Outcome I) : Prop :=
  ∀ l, MayRead A tid t l → ∀ ts w, mem.get? ts = some w → w.loc = l → ts ≤ o.thread.views.getCoh l

/-- A successful, promise-free, newest-reading outcome of `t` against `mem`. -/
def GoodT (A : Arch) (tid : Nat) (t : Thread I) (mem : Memory) (o : Outcome I) : Prop :=
  ∃ outs, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = [] ∧ CohTop A tid t mem o

/-- A `GoodT` outcome of thread `tid` of `c`. -/
def Good (A : Arch) (c : Config I) (tid : Nat) (o : Outcome I) : Prop :=
  ∃ t, c.threads[tid]? = some t ∧ GoodT A tid t c.mem o

/-- **Every thread that has not halted can take a newest-reading
promise-free step**, at every configuration reachable from `c0` by such
steps. -/
def Progressive (A : Arch) (c0 : Config I) : Prop :=
  ∀ c, ReachPI A c0 c → ∀ tid t, c.threads[tid]? = some t → t.halted = false → ∃ o, GoodT A tid t c.mem o

/-- Every thread of `c0` has no outstanding promise. -/
def StartPF (c0 : Config I) : Prop := ∀ (tid : Nat) (t : Thread I), c0.threads[tid]? = some t → t.prom = []

namespace ReachPI

variable {A : Arch} {c0 c : Config I}

theorem size (h : ReachPI A c0 c) : c.threads.size = c0.threads.size := by
  induction h with
  | refl => rfl
  | step _ _ _ _ _ ih => rw [Config.withThread_size]; exact ih

theorem prom (hp0 : StartPF c0) (h : ReachPI A c0 c) : StartPF c := by
  induction h with
  | refl => exact hp0
  | step _ ht _ _ hp ih =>
    intro j u hu
    rcases SpinStep.wt_get ht hu with ⟨-, rfl⟩ | ⟨-, hu⟩
    · exact hp
    · exact ih j u hu

end ReachPI

theorem Good.instrBy {A : Arch} {c : Config I} {tid : Nat} {o : Outcome I} (h : Good A c tid o) :
    InstrBy A tid c (c.withThread tid o.thread o.mem) :=
  let ⟨t, ht, outs, hs, ho, _⟩ := h
  ⟨t, outs, o, ht, hs, ho, rfl⟩

theorem Good.instrSem {A : Arch} {fuel : Nat} {c : Config I} {tid : Nat} {o : Outcome I} (h : Good A c tid o) :
    InstrSem A fuel tid c (c.withThread tid o.thread o.mem) :=
  let ⟨t, ht, outs, hs, ho, hp, _⟩ := h
  ⟨t, outs, o, ht, hs, ho, ⟨_, _, .refl _ _, hp⟩, rfl⟩

theorem Good.mem_succs {A : Arch} {c : Config I} {tid : Nat} {o : Outcome I} (h : Good A c tid o) (fuel : Nat) :
    c.withThread tid o.thread o.mem ∈ (succs A c fuel).1 :=
  let ⟨_, ht, _, hs, ho, hp, _⟩ := h
  reach_mem_succs A fuel (by simp [stepThread, ht, hs]) ho (by simp [hp])

/-! ## The round-robin schedule -/

/-- Thread `tid` exists and has not halted. -/
def Running (c : Config I) (tid : Nat) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.halted = false

/-- The cyclic order from `s`: `s, s + 1, …, N - 1, 0, …, s - 1`. -/
def cyc (N s : Nat) : List Nat := List.range' s (N - s) ++ List.range s

open Classical in
/-- The thread scheduled at index `i`: the first running thread in the cyclic
order from `i % N`. -/
noncomputable def pick (N i : Nat) (c : Config I) : Option Nat :=
  (cyc N (i % N)).find? fun tid => decide (Running c tid)

open Classical in
/-- Step the picked thread with a chosen `Good` outcome; repeat `c` if no
thread is picked. -/
noncomputable def rrStep (A : Arch) (c : Config I) : Option Nat → Config I
  | none => c
  | some tid =>
    if h : ∃ o, Good A c tid o then c.withThread tid (Classical.choose h).thread (Classical.choose h).mem else c

/-- **The round-robin newest-reading promise-free run from `c0`.** -/
noncomputable def rrTrace (A : Arch) (c0 : Config I) : Nat → Config I
  | 0 => c0
  | i + 1 => rrStep A (rrTrace A c0 i) (pick c0.threads.size i (rrTrace A c0 i))

theorem pick_running {N i tid : Nat} {c : Config I} (h : pick N i c = some tid) : Running c tid := by
  unfold pick at h
  simpa using List.find?_some h

theorem mem_cyc {N s tid : Nat} (hs : s ≤ N) (ht : tid < N) : tid ∈ cyc N s := by
  unfold cyc
  rw [List.mem_append, List.mem_range'_1, List.mem_range]
  omega

theorem pick_none {N i : Nat} {c : Config I} (h : pick N i c = none) {tid : Nat} (ht : tid < N) :
    ¬ Running c tid := by
  unfold pick at h
  simpa using List.find?_eq_none.mp h tid (mem_cyc (Nat.le_of_lt (Nat.mod_lt _ (by omega))) ht)

theorem pick_self {N i : Nat} {c : Config I} (hN : 0 < N) (hr : Running c (i % N)) :
    pick N i c = some (i % N) := by
  unfold pick cyc
  obtain ⟨n, hn⟩ : ∃ n, N - i % N = n + 1 := ⟨N - i % N - 1, by have := Nat.mod_lt i hN; omega⟩
  rw [hn, List.range'_succ]
  simp [hr]

section RR

variable {A : Arch} {c0 : Config I}

theorem rr_succ (i : Nat) :
    rrTrace A c0 (i + 1) = rrStep A (rrTrace A c0 i) (pick c0.threads.size i (rrTrace A c0 i)) := rfl

theorem rr_reach (i : Nat) : ReachPI A c0 (rrTrace A c0 i) := by
  induction i with
  | zero => exact .refl
  | succ i ih =>
    rw [rr_succ]
    cases pick c0.threads.size i (rrTrace A c0 i) with
    | none => exact ih
    | some tid =>
      simp only [rrStep]
      split
      · rename_i h
        obtain ⟨t, ht, outs, hs, ho, hp, -⟩ := Classical.choose_spec h
        exact .step ih ht hs ho hp
      · exact ih

theorem rr_good (hP : Progressive A c0) {i tid : Nat} (h : pick c0.threads.size i (rrTrace A c0 i) = some tid) :
    ∃ o, Good A (rrTrace A c0 i) tid o ∧
      rrTrace A c0 (i + 1) = (rrTrace A c0 i).withThread tid o.thread o.mem := by
  obtain ⟨t, ht, hh⟩ := pick_running h
  have he : ∃ o, Good A (rrTrace A c0 i) tid o :=
    let ⟨o, ho⟩ := hP _ (rr_reach i) tid t ht hh
    ⟨o, t, ht, ho⟩
  refine ⟨Classical.choose he, Classical.choose_spec he, ?_⟩
  rw [rr_succ, h]
  simp only [rrStep]
  split
  · rfl
  · contradiction

theorem rr_get_ne {i tid : Nat} (h : pick c0.threads.size i (rrTrace A c0 i) ≠ some tid) :
    (rrTrace A c0 (i + 1)).threads[tid]? = (rrTrace A c0 i).threads[tid]? := by
  rw [rr_succ]
  revert h
  cases pick c0.threads.size i (rrTrace A c0 i) with
  | none => intro _; rfl
  | some j =>
    intro h
    have hj : j ≠ tid := fun e => h (e ▸ rfl)
    simp only [rrStep]
    split
    · rename_i hg
      obtain ⟨t, ht, -⟩ := Classical.choose_spec hg
      exact withThread_get_ne ht (Ne.symm hj)
    · rfl

theorem rr_final (hp0 : StartPF c0) {i : Nat}
    (h : pick c0.threads.size i (rrTrace A c0 i) = none) : (rrTrace A c0 i).final = true := by
  have hsz := (rr_reach (A := A) (c0 := c0) i).size
  unfold Config.final
  rw [Array.all_eq_true]
  intro j hj
  have hget : (rrTrace A c0 i).threads[j]? = some (rrTrace A c0 i).threads[j] := Array.getElem?_eq_getElem hj
  have hnr := pick_none h (by omega : j < c0.threads.size)
  have hh : (rrTrace A c0 i).threads[j].halted = true := by
    cases e : (rrTrace A c0 i).threads[j].halted
    · exact absurd ⟨_, hget, e⟩ hnr
    · rfl
  have hp := (rr_reach i).prom hp0 j _ hget
  simp [hh, hp]

/-- Each step of `rrTrace` is a `Good` step of some thread, or repeats a final
configuration. -/
theorem rr_cases (hP : Progressive A c0) (hp0 : StartPF c0) (i : Nat) :
    (∃ tid o, Good A (rrTrace A c0 i) tid o ∧
      rrTrace A c0 (i + 1) = (rrTrace A c0 i).withThread tid o.thread o.mem) ∨
    ((rrTrace A c0 i).final = true ∧ rrTrace A c0 (i + 1) = rrTrace A c0 i) := by
  cases h : pick c0.threads.size i (rrTrace A c0 i) with
  | none => exact .inr ⟨rr_final hp0 h, by rw [rr_succ, h]; rfl⟩
  | some tid =>
    obtain ⟨o, hg, he⟩ := rr_good hP h
    exact .inl ⟨tid, o, hg, he⟩

/-- **A running thread is scheduled within `N` steps**, with its thread
unchanged until then. -/
theorem rr_sched (hP : Progressive A c0) {j tid : Nat} (hr : Running (rrTrace A c0 j) tid) :
    ∃ m, j ≤ m ∧ (rrTrace A c0 m).threads[tid]? = (rrTrace A c0 j).threads[tid]? ∧
      ∃ o, Good A (rrTrace A c0 m) tid o ∧
        rrTrace A c0 (m + 1) = (rrTrace A c0 m).withThread tid o.thread o.mem := by
  have htN : tid < c0.threads.size := by
    obtain ⟨t, ht, -⟩ := hr
    exact (rr_reach j).size ▸ lt_size_of_get? ht
  have hN : 0 < c0.threads.size := by omega
  obtain ⟨k, hk, hjk⟩ : ∃ k, k % c0.threads.size = tid ∧ j ≤ k := by
    refine ⟨c0.threads.size * (j / c0.threads.size + 1) + tid, ?_, ?_⟩
    · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt htN]
    · have h1 := Nat.div_add_mod j c0.threads.size
      have h2 := Nat.mod_lt j hN
      rw [Nat.mul_add, Nat.mul_one]
      omega
  suffices H : ∀ d j', k - j' = d → j' ≤ k → Running (rrTrace A c0 j') tid →
      ∃ m, j' ≤ m ∧ (rrTrace A c0 m).threads[tid]? = (rrTrace A c0 j').threads[tid]? ∧
        ∃ o, Good A (rrTrace A c0 m) tid o ∧
          rrTrace A c0 (m + 1) = (rrTrace A c0 m).withThread tid o.thread o.mem from H _ j rfl hjk hr
  intro d
  induction d with
  | zero =>
    intro j' hd hj' hr'
    obtain rfl : j' = k := by omega
    refine ⟨j', Nat.le_refl _, rfl, rr_good hP ?_⟩
    have := pick_self (c := rrTrace A c0 j') hN (show Running _ (j' % c0.threads.size) by rw [hk]; exact hr')
    rwa [hk] at this
  | succ d ih =>
    intro j' hd hj' hr'
    by_cases hp : pick c0.threads.size j' (rrTrace A c0 j') = some tid
    · exact ⟨j', Nat.le_refl _, rfl, rr_good hP hp⟩
    · have he := rr_get_ne hp
      obtain ⟨u, hu, hh⟩ := hr'
      obtain ⟨m, hm, h1, h2⟩ := ih (j' + 1) (by omega) (by omega) ⟨u, he ▸ hu, hh⟩
      exact ⟨m, by omega, h1.trans he, h2⟩

theorem rr_infOften (hP : Progressive A c0) {tid n : Nat} (hr : ∀ i, n ≤ i → Running (rrTrace A c0 i) tid) :
    InfOften fun m => ∃ o, Good A (rrTrace A c0 m) tid o ∧
      rrTrace A c0 (m + 1) = (rrTrace A c0 m).withThread tid o.thread o.mem := by
  intro m0
  obtain ⟨m, hm, -, h⟩ := rr_sched hP (hr (max m0 n) (by omega))
  exact ⟨m, by omega, h⟩

end RR

/-! ## Enabled threads are running -/

theorem running_of_enabled {A : Arch} {fuel tid : Nat} {c : Config I} (h : Enabled A fuel tid c) :
    Running c tid := by
  cases ht : c.threads[tid]? with
  | none => exact absurd h (not_enabled_of_none ht)
  | some t =>
    cases hh : t.halted
    · exact ⟨t, ht, hh⟩
    · exact absurd h (not_enabled_of_halted ht hh)

theorem halted_false_of_stepOne {A : Arch} {tid : Nat} {t : Thread I} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hs : stepOne A t tid mem = some outs) : t.halted = false := by
  cases hh : t.halted
  · rfl
  · simp only [Thread.halted, Option.isNone_iff_eq_none] at hh
    simp [stepOne, hh] at hs

theorem running_of_enabledSem {A : Arch} {fuel tid : Nat} {c : Config I} (h : EnabledSem A fuel tid c) :
    Running c tid := by
  obtain ⟨c', ⟨t, outs, o, ht, hs, -, -, -⟩ | ⟨t, w, ht, -, hc, -⟩⟩ := h
  · exact ⟨t, ht, halted_false_of_stepOne hs⟩
  · refine ⟨t, ht, ?_⟩
    cases hh : t.halted
    · rfl
    · exact absurd hc (not_certOkN_of_halted (t := promThread t c.mem w) hh (by simp))

/-! ## `rrTrace` is a fair trace of both machines -/

section Fair

variable {A : Arch} {c0 : Config I} (hP : Progressive A c0)
  (hp0 : StartPF c0)

include hP hp0 in
/-- **`rrTrace` is a trace of the executable machine** (`TraceS`, at every
fuel: a promise-free outcome is a successor whatever `certify` computes). -/
noncomputable def rrTrace_traceS (fuel : Nat) : TraceS A fuel I :=
  ⟨rrTrace A c0, fun i => (rr_cases hP hp0 i).imp (fun ⟨_, _, hg, he⟩ => by rw [he]; exact hg.mem_succs fuel) id⟩

include hP hp0 in
/-- **`rrTrace` is a trace of the semantic machine** (`TraceSem`: a
promise-free outcome is certifiable by the empty run). -/
noncomputable def rrTrace_traceSem (fuel : Nat) : TraceSem A fuel I :=
  ⟨rrTrace A c0, fun i => (rr_cases hP hp0 i).imp (fun ⟨tid, _, hg, he⟩ => ⟨tid, by rw [he]; exact .inl hg.instrSem⟩) id⟩

include hp0 in
theorem rrTrace_promiseFree : PromiseFree A (rrTrace A c0) := by
  intro i tid hpb
  obtain ⟨t', ht', hne⟩ := hpb.prom_ne
  exact hne ((rr_reach (i + 1)).prom hp0 tid t' ht')

include hP in
theorem rrTrace_weakFair (fuel : Nat) : WeakFair A fuel (rrTrace A c0) := by
  rintro tid ⟨n, hn⟩ m0
  obtain ⟨m, hm, o, hg, he⟩ := rr_infOften hP (fun i hi => running_of_enabled (hn i hi)) m0
  refine ⟨m, hm, ?_⟩
  show StepBy A fuel tid _ _
  rw [he]
  exact ⟨hg.mem_succs fuel, .inl hg.instrBy⟩

include hP in
theorem rrTrace_weakFairInstr (fuel : Nat) : WeakFairInstr A fuel (rrTrace A c0) := by
  rintro tid ⟨n, hn⟩ m0
  obtain ⟨m, hm, o, hg, he⟩ :=
    rr_infOften hP (fun i hi => let ⟨c', h1, h2⟩ := hn i hi; running_of_enabled ⟨c', h1, .inl h2⟩) m0
  refine ⟨m, hm, ?_⟩
  show _ ∈ _ ∧ InstrBy A tid _ _
  rw [he]
  exact ⟨hg.mem_succs fuel, hg.instrBy⟩

include hP in
theorem rrTrace_weakFairSem (fuel : Nat) : WeakFairSem A fuel (rrTrace A c0) := by
  rintro tid ⟨n, hn⟩ m0
  obtain ⟨m, hm, o, hg, he⟩ := rr_infOften hP (fun i hi => running_of_enabledSem (hn i hi)) m0
  exact ⟨m, hm, show StepSem A fuel tid _ _ by rw [he]; exact .inl hg.instrSem⟩

include hP in
theorem rrTrace_weakFairInstrSem (fuel : Nat) : WeakFairInstrSem A fuel (rrTrace A c0) := by
  rintro tid ⟨n, hn⟩ m0
  obtain ⟨m, hm, o, hg, he⟩ :=
    rr_infOften hP (fun i hi => let ⟨c', h⟩ := hn i hi; running_of_enabledSem ⟨c', .inl h⟩) m0
  exact ⟨m, hm, show InstrSem A fuel tid _ _ by rw [he]; exact hg.instrSem⟩

include hP hp0 in
/-- **`rrTrace` is memory-fair**: a thread reading `l` infinitely often is
scheduled after each such read with its thread unchanged, and its outcome
then puts `coh l` above every message of `l` in memory (`CohTop`). -/
theorem rrTrace_memFair : MemFair A (rrTrace A c0) := by
  intro tid l hinf i ts w hw hl
  obtain ⟨j, hij, ts', t, outs, o, ht, hs, ho, -, v, ν, hrd⟩ := hinf i
  have hmay : MayRead A tid t l := ⟨_, outs, o, hs, ho, ts', v, ν, hrd⟩
  obtain ⟨m, hjm, hsame, o', ⟨t', ht', outs', hs', ho', -, hct⟩, he⟩ :=
    rr_sched hP ⟨t, ht, halted_false_of_stepOne hs⟩
  rw [hsame, ht] at ht'
  cases ht'
  refine ⟨m + 1, by omega, o'.thread, by rw [he]; exact withThread_get_self (hsame.trans ht), ?_⟩
  exact hct l hmay ts w ((rrTrace_traceSem hP hp0 0).get_le (by omega : i ≤ m) hw) hl

include hP hp0 in
/-- **A fair trace of the executable machine exists from `c0`**: weakly fair
(for all steps and for instruction steps), promise-free and memory-fair. -/
theorem fair_exists (fuel : Nat) :
    ∃ tr : TraceS A fuel I, tr.cfg 0 = c0 ∧ WeakFair A fuel tr.cfg ∧ WeakFairInstr A fuel tr.cfg ∧
      PromiseFree A tr.cfg ∧ MemFair A tr.cfg :=
  ⟨rrTrace_traceS hP hp0 fuel, rfl, rrTrace_weakFair hP fuel, rrTrace_weakFairInstr hP fuel,
    rrTrace_promiseFree hp0, rrTrace_memFair hP hp0⟩

include hP hp0 in
/-- **A fair trace of the semantic machine exists from `c0`**: weakly fair
(for all steps and for instruction steps) and memory-fair. -/
theorem fairSem_exists (fuel : Nat) :
    ∃ tr : TraceSem A fuel I, tr.cfg 0 = c0 ∧ WeakFairSem A fuel tr.cfg ∧ WeakFairInstrSem A fuel tr.cfg ∧
      MemFair A tr.cfg :=
  ⟨rrTrace_traceSem hP hp0 fuel, rfl, rrTrace_weakFairSem hP fuel, rrTrace_weakFairInstrSem hP fuel,
    rrTrace_memFair hP hp0⟩

end Fair


/-! ## Forwarding entries stay at or below the coherence view

A read of a thread's own forwarded write takes the forwarding entry's view,
not the message's timestamp (`readView`). So "reading the last write raises
`coh` to its timestamp" (`readNext_coh_ge`) needs the forwarding entry's
timestamp to be at most `coh` already: `FwdLeCoh`. A write sets both
(`afterWrite`), `coh` only grows, and nothing else touches the forwarding
entries, so every instruction keeps `FwdLeCoh` (`stepOne_fwdLeCoh`), and so
does every `ReachPI` configuration whose start has it (`ReachPI.fwd`). The
proof is one induction on the instruction's tree (`runTree_cstep`), which
also bounds the locations an outcome's log reads by the tree's load and RMW
nodes (`ReadsIn`; `MayRead.readsIn`). -/

/-- **Every forwarding entry is at most the coherence view of its location.** -/
def FwdLeCoh (vs : Views) : Prop := ∀ l f, vs.getFwd l = some f → f.time ≤ vs.getCoh l

theorem fwdLeCoh_of_nil {vs : Views} (h : vs.fwdb = []) : FwdLeCoh vs := by
  intro l f hf
  simp [Views.getFwd, h] at hf

/-- The locations a tree may read: those of its load and RMW nodes. -/
inductive ReadsIn {σ : Type} (l : Loc) : EvTree σ → Prop
  | load {k : LoadKind} {xcl : Bool} {ret : Val → EvTree σ} : ReadsIn l (.load k xcl l ret)
  | loadRet {k : LoadKind} {xcl : Bool} {l' : Loc} {ret : Val → EvTree σ} (v : Val) :
      ReadsIn l (ret v) → ReadsIn l (.load k xcl l' ret)
  | rmw {k : RmwKind} {nr : Bool} {op : Val → Option Val} {ret : Val → EvTree σ} : ReadsIn l (.rmw k nr l op ret)
  | rmwRet {k : RmwKind} {nr : Bool} {l' : Loc} {op : Val → Option Val} {ret : Val → EvTree σ} (v : Val) :
      ReadsIn l (ret v) → ReadsIn l (.rmw k nr l' op ret)
  | store {k : StoreKind} {xcl : Bool} {l' : Loc} {v : Val} {ret : Bool → EvTree σ} (b : Bool) :
      ReadsIn l (ret b) → ReadsIn l (.store k xcl l' v ret)
  | fence {k : FenceKind} {ret : Unit → EvTree σ} : ReadsIn l (ret ()) → ReadsIn l (.fence k ret)
  | choose {n : Nat} {k : Fin n → EvTree σ} (i : Fin n) : ReadsIn l (k i) → ReadsIn l (.choose n k)

/-- A context step that keeps `FwdLeCoh`, never lowers a coherence view, and
logs reads of `P`-locations only. -/
structure CStep (P : Loc → Prop) (c c' : Ctx) : Prop where
  fwd : FwdLeCoh c.views → FwdLeCoh c'.views
  coh : ∀ l, c.views.getCoh l ≤ c'.views.getCoh l
  log : ∀ l ts v ν, TraceEv.read l ts v ν ∈ c'.log → TraceEv.read l ts v ν ∈ c.log ∨ P l

namespace CStep

variable {P Q : Loc → Prop} {c c1 c2 : Ctx}

theorem refl (c : Ctx) : CStep P c c := ⟨id, fun _ => Nat.le_refl _, fun _ _ _ _ h => .inl h⟩

theorem trans (h1 : CStep P c c1) (h2 : CStep Q c1 c2) : CStep (fun l => P l ∨ Q l) c c2 :=
  ⟨h2.fwd ∘ h1.fwd, fun l => Nat.le_trans (h1.coh l) (h2.coh l), fun l ts v ν h =>
    (h2.log l ts v ν h).elim (fun h => (h1.log l ts v ν h).imp id .inl) (fun h => .inr (.inr h))⟩

theorem mono (h : CStep P c c1) (hPQ : ∀ l, P l → Q l) : CStep Q c c1 :=
  ⟨h.fwd, h.coh, fun l ts v ν hr => (h.log l ts v ν hr).imp id (hPQ l)⟩

/-- A step that keeps the coherence and forwarding entries and logs no read. -/
theorem keep (hc : c1.views.coh = c.views.coh) (hf : c1.views.fwdb = c.views.fwdb)
    (hl : ∀ l ts v ν, TraceEv.read l ts v ν ∈ c1.log → TraceEv.read l ts v ν ∈ c.log) : CStep P c c1 := by
  have hgc : ∀ l, c1.views.getCoh l = c.views.getCoh l := fun l => by simp only [Views.getCoh, hc]
  have hgf : ∀ l, c1.views.getFwd l = c.views.getFwd l := fun l => by simp only [Views.getFwd, hf]
  refine ⟨fun h l f hl => ?_, fun l => (hgc l).symm ▸ Nat.le_refl _, fun l ts v ν h => .inl (hl l ts v ν h)⟩
  rw [hgc]; exact h l f (by rw [← hgf]; exact hl)

end CStep

section Prims

variable (A : Arch) (tid : Nat) (iv : InstrViews) {P : Loc → Prop}

theorem cstep_fence (c : Ctx) (k : FenceKind) : CStep P c (fenceStep c k) := by
  have hl : (fenceStep c k).log = c.log ++ [.fence k] := by cases k <;> rfl
  exact CStep.keep (by cases k <;> rfl) (by cases k <;> rfl) fun l ts v ν h => by rw [hl] at h; simpa using h

theorem cstep_optFence (b : Bool) (c : Ctx) (k : FenceKind) : CStep P c (if b then fenceStep c k else c) := by
  split
  · exact cstep_fence c k
  · exact .refl c

theorem cstep_readNext (c : Ctx) (k : LoadKind) (xcl : Bool) (l : Loc) (noRet : Bool) (t : Time) (v : Val) :
    CStep (· = l) c (readNext A iv c k xcl l noRet t v) := by
  refine ⟨fun h l' f hf => Nat.le_trans (h l' f hf) (SpinStep.readNext_getCoh A iv c k xcl l noRet t v l'),
    SpinStep.readNext_getCoh A iv c k xcl l noRet t v, fun l' ts v' ν h => ?_⟩
  simp only [readNext, List.mem_append, List.mem_singleton, TraceEv.read.injEq] at h
  rcases h with h | ⟨rfl, -⟩
  · exact .inl h
  · exact .inr rfl

theorem cstep_afterWrite {c c1 : Ctx} (hv : c1.views = c.views) (hl : c1.log = c.log) (k : StoreKind) (xcl : Bool)
    (l : Loc) (v : Val) (t : Time) (νfwd : View) (ful : Bool) (xr : View) :
    CStep P c (afterWrite A iv c1 k xcl l v t νfwd ful xr) := by
  have hc : ∀ l', (afterWrite A iv c1 k xcl l v t νfwd ful xr).views.getCoh l' = (c.views.setCoh l t).getCoh l' := by
    intro l'; rw [← hv]; rfl
  have hf : ∀ l', (afterWrite A iv c1 k xcl l v t νfwd ful xr).views.getFwd l' =
      (c.views.setFwd l { time := t, view := νfwd, xcl, xclRead := xr }).getFwd l' := by
    intro l'; rw [← hv]; rfl
  refine ⟨fun h l' f hl' => ?_, fun l' => ?_, fun l' ts v' ν h => ?_⟩
  · rw [hf, Views.getFwd_setFwd] at hl'
    rw [hc, Views.getCoh_setCoh]
    by_cases e : l' = l
    · simp only [e, ↓reduceIte, Option.some.injEq] at hl' ⊢
      subst hl'
      exact Nat.le_max_right _ _
    · simp only [e, ↓reduceIte] at hl' ⊢
      exact h l' f hl'
  · rw [hc]; exact Views.getCoh_le_setCoh _ _ _ _
  · simp only [afterWrite, hl, List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · exact .inl h
    · cases h

theorem cstep_writeSuccs {xr : View} {c c' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) : CStep P c c' := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, h⟩ | h
  · cases hg : c.mem.get? t with
    | none => simp [hg] at h
    | some w =>
      simp only [hg] at h
      rw [Option.ite_none_right_eq_some] at h
      obtain ⟨-, h⟩ := h
      obtain rfl := Option.some.inj h
      exact cstep_afterWrite A iv rfl rfl _ _ _ _ _ _ _ _
  · generalize c.mem.append { loc := l, val := v, tid } = ap at h
    obtain ⟨mem', t⟩ := ap
    simp only at h
    rw [List.mem_ite_nil_right, List.mem_singleton] at h
    obtain ⟨-, rfl⟩ := h
    exact cstep_afterWrite (c := c) A iv (by rfl) (by rfl) _ _ _ _ _ _ _ _

end Prims

/-- **One instruction's tree, run**: `FwdLeCoh` is kept, no coherence view
drops, and every read logged is of a location of a load or RMW node. -/
theorem runTree_cstep (A : Arch) (tid : Nat) (iv : InstrViews) {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → CStep (ReadsIn · tree) c c' := by
  induction tree with
  | done s0 =>
    intro c s c' h
    obtain ⟨-, rfl⟩ := TicketStep.run_done A tid iv h
    exact .refl _
  | fault msg => intro c s c' h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, hi⟩ := h
    exact (ih i c s c' hi).mono fun l h => .choose i h
  | load k xcl l ret ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨⟨ts, v, c1⟩, hx, h⟩ := h
    obtain ⟨ts', v', hx', -⟩ := (mem_readSuccs A).mp hx
    simp only [Prod.mk.injEq] at hx'
    obtain ⟨rfl, rfl, rfl⟩ := hx'
    exact ((cstep_readNext A iv _ _ _ _ _ _ _).trans (ih _ _ s c' h)).mono fun l' h =>
      h.elim (fun e => e ▸ .load) (.loadRet _)
  | store k xcl l v ret ih =>
    intro c s c' h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c1, hc1, h⟩ := h
      exact ((cstep_writeSuccs (P := fun _ => False) A tid _ hc1).trans (ih true c1 s c' h)).mono fun l' h =>
        h.elim False.elim (ReadsIn.store true)
    · rw [List.mem_ite_nil_right] at h
      obtain ⟨-, h⟩ := h
      exact ((CStep.keep (P := fun _ => False) (c := c) (by rfl) (by rfl) (fun l ts v ν h => by simpa using h)).trans
        (ih false _ s c' h)).mono fun l' h => h.elim False.elim (ReadsIn.store false)
  | fence k ret ih =>
    intro c s c' h
    simp only [runTree] at h
    exact ((cstep_fence (P := fun _ => False) c k).trans (ih () _ s c' h)).mono fun l' h =>
      h.elim False.elim ReadsIn.fence
  | rmw k noRet l op ret ih =>
    intro c s c' h
    simp only [runTree] at h
    have h0 := cstep_optFence (P := fun _ => False) A.rmwFence c .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c0 at h h0
    simp only [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c1⟩, hx, h⟩ := h
    obtain ⟨tr', old', hx', -⟩ := (mem_readSuccs A).mp hx
    simp only [Prod.mk.injEq] at hx'
    obtain ⟨rfl, rfl, rfl⟩ := hx'
    have h1 := h0.trans (cstep_readNext A iv c0 (if noRet = true then LoadKind.plain else (A.rmwKind k).loadKind)
      false l noRet tr old)
    have hP : ∀ l', l' = l ∨ ReadsIn l' (ret old) → ReadsIn l' (.rmw k noRet l op ret) := fun l' h => by
      rcases h with rfl | h
      · exact .rmw
      · exact .rmwRet _ h
    simp only at h
    split at h
    · exact (h1.trans ((cstep_optFence (P := fun _ => False) A.rmwFence _ .sy).trans (ih old _ s c' h))).mono
        fun l' h => hP l' (by simpa only [false_or] using h)
    · simp only [List.mem_flatMap] at h
      obtain ⟨c2, hc2, h⟩ := h
      refine (h1.trans ((cstep_writeSuccs (P := fun _ => False) A tid iv hc2).trans
        ((?_ : CStep (fun _ => False) c2 _).trans ((cstep_optFence (P := fun _ => False) A.rmwFence _ .sy).trans
          (ih old _ s c' h))))).mono fun l' h => hP l' (by simpa only [false_or] using h)
      split <;> exact CStep.keep rfl rfl fun _ _ _ _ h => h

/-- **Every instruction keeps `FwdLeCoh`**, and logs reads only of locations
of its tree's load and RMW nodes. -/
theorem stepOne_cstep {A : Arch} {tid : Nat} {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))}
    {o : Outcome I} (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ tree, I.exec t.st = some tree ∧ (FwdLeCoh t.views → FwdLeCoh o.thread.views) ∧
      ∀ l ts v ν, TraceEv.read l ts v ν ∈ o.log → ReadsIn l tree := by
  obtain ⟨tree, c', hex, hr, -, hv, -, hl⟩ := SLR.stepOne_runK A hs ho
  have hc := runTree_cstep A tid _ tree _ _ _ hr
  refine ⟨tree, hex, fun h l f hf => ?_, fun l ts v ν hr' => ?_⟩
  · rw [Views.getCoh_congr hv]
    exact hc.fwd h l f (by rw [← Views.getFwd_congr hv]; exact hf)
  · rw [hl] at hr'
    rcases hc.log l ts v ν hr' with h | h
    · simp at h
    · exact h

theorem stepOne_fwdLeCoh {A : Arch} {tid : Nat} {t : Thread I} {mem : Memory}
    {outs : List (Except String (Outcome I))} {o : Outcome I} (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) (h : FwdLeCoh t.views) : FwdLeCoh o.thread.views :=
  let ⟨_, _, hf, _⟩ := stepOne_cstep hs ho
  hf h

/-- A location a thread may read is a location of a load or RMW node of its
next instruction's tree. -/
theorem MayRead.readsIn {A : Arch} {tid : Nat} {t : Thread I} {l : Loc} {tree : EvTree I.State}
    (hm : MayRead A tid t l) (hex : I.exec t.st = some tree) : ReadsIn l tree := by
  obtain ⟨mem, outs, o, hs, ho, ts, v, ν, hr⟩ := hm
  obtain ⟨tree', hex', -, hl⟩ := stepOne_cstep hs ho
  rw [hex] at hex'
  cases hex'
  exact hl l ts v ν hr

/-- `FwdLeCoh` holds at every `ReachPI` configuration if it holds at the start. -/
theorem ReachPI.fwd {A : Arch} {c0 c : Config I}
    (h0 : ∀ (tid : Nat) (t : Thread I), c0.threads[tid]? = some t → FwdLeCoh t.views) (h : ReachPI A c0 c) :
    ∀ (tid : Nat) (t : Thread I), c.threads[tid]? = some t → FwdLeCoh t.views := by
  induction h with
  | refl => exact h0
  | step _ ht hs ho _ ih =>
    intro j u hu
    rcases SpinStep.wt_get ht hu with ⟨-, rfl⟩ | ⟨-, hu⟩
    · exact stepOne_fwdLeCoh hs ho (ih _ _ ht)
    · exact ih j u hu

/-! ## Newest-reading outcomes of the tree shapes

For a promise-free thread with bounded views and `FwdLeCoh`, each of the tree
shapes the lock programs use has a `GoodT` outcome: `done`, `choose` (with
`n > 0`) and non-exclusive stores read nothing; a load, an RMW (any
`rmwFence`) and a load-store pair on one location read the location's last
write, after which its coherence view is at or above every message of it. -/

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-- **Reading a timestamp raises the coherence view to it**, given
`FwdLeCoh` (a forwarded read takes the forwarding entry's view, whose
timestamp is then the one read). -/
theorem readNext_coh_ge (A : Arch) (iv : InstrViews) {c : Ctx} (hfc : FwdLeCoh c.views) (k : LoadKind) (xcl : Bool)
    (l : Loc) (noRet : Bool) (t : Time) (v : Val) : t ≤ (readNext A iv c k xcl l noRet t v).views.getCoh l := by
  have h1 : max (readPre A iv c k) (readView A (A.loadKind k) (c.views.getFwd l) t) ≤
      (readNext A iv c k xcl l noRet t v).views.getCoh l := by
    show _ ≤ (c.views.setCoh l _).getCoh l
    simp only [Views.getCoh_setCoh, ↓reduceIte]
    exact Nat.le_max_right _ _
  have h2 := SpinStep.readNext_getCoh A iv c k xcl l noRet t v l
  unfold readView at h1
  cases hf : c.views.getFwd l with
  | none => rw [hf] at h1; omega_t
  | some f =>
    rw [hf] at h1
    simp only at h1
    split at h1
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have := hfc l f hf
      omega_t
    · omega_t

theorem le_lastWrite {mem : Memory} {ts : Time} {w : Msg} (hw : mem.get? ts = some w) : ts ≤ mem.lastWrite w.loc :=
  Nat.le_of_not_lt fun h => mem.not_write_of_lastWrite_lt w.loc h hw rfl

/-- `stepOne_of_run` with the outcome's coherence views. -/
theorem stepOne_of_runV (A : Arch) (tid : Nat) {t : Thread I} {mem : Memory} {tree : EvTree I.State}
    (hex : I.exec t.st = some tree) {st : I.State} {c' : Ctx}
    (hr : .ok (st, c') ∈ runTree A tid (instrViews t (I.deps t.st)) (TicketStep.ctx0 tid t mem) tree) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = c'.prom ∧
      ∀ l, o.thread.views.getCoh l = c'.views.getCoh l := by
  obtain ⟨th, hth⟩ := List.exists_mem_of_ne_nil _
    (TicketStep.finishInstr_ne_nil t (I.deps t.st) (instrViews t (I.deps t.st)) st c')
  refine ⟨_, ⟨th, c'.mem, c'.promisedNow, c'.log⟩, by unfold stepOne; rw [hex]; rfl, ?_,
    (finishInstr_relKey hth).1, Views.getCoh_congr (finishInstr_relKey hth).2⟩
  rw [List.mem_flatMap]
  exact ⟨_, hr, List.mem_map.mpr ⟨th, hth, rfl⟩⟩

section Shapes

variable {A : Arch} {tid : Nat} {t : Thread I} {mem : Memory}

/-- A run of a tree that reads at most `L`, after which `coh L` is at or past
`L`'s last write, gives a `GoodT` outcome. -/
theorem goodT_of_run {tree : EvTree I.State} (hex : I.exec t.st = some tree) {L : Loc}
    (hL : ∀ l, ReadsIn l tree → l = L) {st : I.State} {c' : Ctx}
    (hr : .ok (st, c') ∈ runTree A tid (instrViews t (I.deps t.st)) (TicketStep.ctx0 tid t mem) tree)
    (hp : c'.prom = []) (hc : mem.lastWrite L ≤ c'.views.getCoh L) : ∃ o, GoodT A tid t mem o := by
  obtain ⟨outs, o, hs, ho, hp', hc'⟩ := stepOne_of_runV A tid hex hr
  refine ⟨o, outs, hs, ho, hp'.trans hp, fun l hm ts w hw hl => ?_⟩
  obtain rfl := hL l (hm.readsIn hex)
  rw [hc']
  exact Nat.le_trans (hl ▸ le_lastWrite hw) hc

/-- A successful promise-free outcome of a tree that reads nothing is `GoodT`. -/
theorem goodT_of_noRead {tree : EvTree I.State} (hex : I.exec t.st = some tree) (hn : ∀ l, ¬ ReadsIn l tree)
    {outs : List (Except String (Outcome I))} {o : Outcome I} (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) (hp : o.thread.prom = []) : ∃ o, GoodT A tid t mem o :=
  ⟨o, outs, hs, ho, hp, fun l hm => absurd (hm.readsIn hex) (hn l)⟩

theorem goodT_done {s : I.State} (hp0 : t.prom = []) (hex : I.exec t.st = some (.done s)) :
    ∃ o, GoodT A tid t mem o :=
  let ⟨_, _, h1, h2, h3⟩ := TicketStep.en_done A tid (mem := mem) hex
  goodT_of_noRead hex (fun _ h => nomatch h) h1 h2 (h3.trans hp0)

theorem goodT_choose {n : Nat} {f : Fin n → I.State} (hn : 0 < n) (hp0 : t.prom = [])
    (hex : I.exec t.st = some (.choose n fun i => .done (f i))) : ∃ o, GoodT A tid t mem o :=
  let ⟨_, _, h1, h2, h3⟩ := SpinX64Step.en_choose A tid (mem := mem) hn hex
  goodT_of_noRead hex (fun _ h => by cases h with | choose _ h => cases h) h1 h2 (h3.trans hp0)

theorem goodT_store {k : StoreKind} {l : Loc} {v : Val} {s : I.State} (hp0 : t.prom = []) (hb : t.Bnd mem.last)
    (hex : I.exec t.st = some (.store k false l v fun _ => .done s)) : ∃ o, GoodT A tid t mem o :=
  let ⟨_, _, h1, h2, h3⟩ := TicketStep.en_store A tid hp0 hb hex
  goodT_of_noRead hex (fun _ h => by cases h with | store _ h => cases h) h1 h2 h3

theorem goodT_load {k : LoadKind} {L : Loc} {f : Val → I.State} (hp0 : t.prom = []) (hfc : FwdLeCoh t.views)
    (hex : I.exec t.st = some (.load k false L fun v => .done (f v))) : ∃ o, GoodT A tid t mem o := by
  have hr : .ok (f (mem.finalVal L), readNext A (instrViews t (I.deps t.st)) (TicketStep.ctx0 tid t mem) k false L
      false (mem.lastWrite L) (mem.finalVal L)) ∈
      runTree A tid (instrViews t (I.deps t.st)) (TicketStep.ctx0 tid t mem) (.load k false L fun v => .done (f v)) := by
    simp only [runTree, List.mem_flatMap]
    refine ⟨(mem.lastWrite L, mem.finalVal L, _), ?_, List.mem_singleton.mpr rfl⟩
    rw [mem_readSuccs]
    exact ⟨_, _, rfl, mem.lastWrite_le L, mem.read?_lastWrite L, mem.writeIn_lastWrite L _, by simp [hp0]⟩
  exact goodT_of_run hex (fun l h => by cases h with | load => rfl | loadRet _ h => cases h) hr hp0
    (readNext_coh_ge A _ hfc _ _ _ _ _ _)

theorem goodT_ldst {k : LoadKind} {k' : StoreKind} {L : Loc} {g : Val → Val} {f : Val → I.State}
    (hp0 : t.prom = []) (hb : t.Bnd mem.last) (hfc : FwdLeCoh t.views)
    (hex : I.exec t.st = some (.load k false L fun v => .store k' false L (g v) fun _ => .done (f v))) :
    ∃ o, GoodT A tid t mem o := by
  let iv := instrViews t (I.deps t.st)
  let c := TicketStep.ctx0 tid t mem
  let c1 := readNext A iv c k false L false (mem.lastWrite L) (mem.finalVal L)
  have hx : (mem.lastWrite L, mem.finalVal L, c1) ∈ readSuccs A iv c k false L false := by
    rw [mem_readSuccs]
    exact ⟨_, _, rfl, mem.lastWrite_le L, mem.read?_lastWrite L, mem.writeIn_lastWrite L _, by simp [c, hp0]⟩
  have hiv : iv.Le c.mem.last := instrViews_le hb.regs _
  obtain ⟨hb1, -, hm1⟩ := readSuccs_bnd A iv (c := c) ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
    hiv hx
  have hp1 : c1.prom = [] := hp0
  obtain ⟨c2, h2⟩ := TicketStep.run_store_exists A tid iv hp1 hb1.views.le (hm1 ▸ hiv) k' L (g (mem.finalVal L))
    (f (mem.finalVal L))
  have hr : .ok (f (mem.finalVal L), c2) ∈ runTree A tid iv c
      (.load k false L fun v => .store k' false L (g v) fun _ => .done (f v)) := by
    simp only [runTree, List.mem_flatMap] at h2 ⊢
    exact ⟨_, hx, h2⟩
  refine goodT_of_run hex (fun l h => by cases h with | load => rfl | loadRet _ h => cases h with | store _ h => cases h)
    hr (TicketStep.run_store A tid iv hp1 h2).2.2 ?_
  exact Nat.le_trans (readNext_coh_ge A iv hfc _ _ _ _ _ _) ((runTree_cstep A tid iv _ c1 _ c2 h2).coh L)

/-- **An RMW reading the last write** (any `rmwFence`): its outcome leaves no
promise, and the coherence view of the location at or past the last write. -/
theorem run_rmw_newest (A : Arch) (tid : Nat) (iv : InstrViews) {σ : Type} {c : Ctx} (hp : c.prom = []) (hb : c.Bnd)
    (hiv : iv.Le c.mem.last) (hfc : FwdLeCoh c.views) (k : RmwKind) (l : Loc) (op : Val → Option Val)
    (f : Val → σ) :
    ∃ s c', .ok (s, c') ∈ runTree A tid iv c (.rmw k false l op fun v => .done (f v)) ∧ c'.prom = [] ∧
      c.mem.lastWrite l ≤ c'.views.getCoh l := by
  obtain ⟨c0, hc0⟩ : ∃ c0, (if A.rmwFence then fenceStep c .sy else c) = c0 := ⟨_, rfl⟩
  have hmp0 : c0.mem = c.mem ∧ c0.prom = c.prom := hc0 ▸ SLR.optFence_mem_prom c A.rmwFence .sy
  have hb0 : c0.Bnd := by
    rw [← hc0]; split
    · exact fenceStep_bnd hb .sy
    · exact hb
  have hs0 : CStep (fun _ => False) c c0 := hc0 ▸ cstep_optFence A.rmwFence c .sy
  have hp0 : c0.prom = [] := hmp0.2.trans hp
  have hiv0 : iv.Le c0.mem.last := hmp0.1 ▸ hiv
  let kl := (A.rmwKind k).loadKind
  let c1 := readNext A iv c0 kl false l false (c0.mem.lastWrite l) (c0.mem.finalVal l)
  have hx : (c0.mem.lastWrite l, c0.mem.finalVal l, c1) ∈ readSuccs A iv c0 kl false l false := by
    rw [mem_readSuccs]
    exact ⟨_, _, rfl, c0.mem.lastWrite_le l, c0.mem.read?_lastWrite l, c0.mem.writeIn_lastWrite l _, by rw [hp0]; rfl⟩
  have hc1 : c.mem.lastWrite l ≤ c1.views.getCoh l := hmp0.1 ▸ readNext_coh_ge A iv (hs0.fwd hfc) _ _ _ _ _ _
  have hp1 : c1.prom = [] := hp0
  cases hop : op (c0.mem.finalVal l) with
  | none =>
    refine ⟨f (c0.mem.finalVal l), if A.rmwFence then fenceStep c1 .sy else c1, ?_, ?_,
      Nat.le_trans hc1 ((cstep_optFence (P := fun _ => False) A.rmwFence c1 .sy).coh l)⟩
    · simp only [runTree, hc0, List.mem_flatMap, Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, hx, by simp only [hop]; exact List.mem_singleton.mpr rfl⟩
    · rw [(SLR.optFence_mem_prom c1 A.rmwFence .sy).2]; exact hp1
  | some new =>
    obtain ⟨c2, hw⟩ := SpinStep.readLast_writeSuccs_exists A tid iv hp0 hb0 hiv0 k l new
    have hp2 : c2.prom = [] := (TicketStep.writeSuccs_nil A tid iv hp1 (.inl hw)).2.1
    have hc2 := (cstep_writeSuccs (P := fun _ => False) A tid iv hw).coh l
    have hpost := TsoRmw.rmwPost_keeps (A.rmwKind k == .acqRel && !false) c2 l
    refine ⟨f (c0.mem.finalVal l), ?c3, ?_, ?_, ?_⟩
    case c3 =>
      exact
        let v : Views := { c2.views with vrNew := max c2.views.vrNew (c2.views.getCoh l),
                                         vwNew := max c2.views.vwNew (c2.views.getCoh l) }
        let c3 : Ctx := if (A.rmwKind k == .acqRel && !false) then { c2 with rmwWrote := true, views := v }
          else { c2 with rmwWrote := true }
        if A.rmwFence then fenceStep c3 .sy else c3
    · simp only [runTree, hc0, List.mem_flatMap, Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, hx, by simp only [hop, List.mem_flatMap]; exact ⟨c2, hw, TicketStep.run_done_exists A tid iv _ _⟩⟩
    · rw [(SLR.optFence_mem_prom _ A.rmwFence .sy).2, hpost.2.1]; exact hp2
    · refine Nat.le_trans hc1 (Nat.le_trans hc2 ?_)
      exact Nat.le_trans (Nat.le_of_eq (hpost.2.2.1 l).symm) ((cstep_optFence (P := fun _ => False) A.rmwFence _ .sy).coh l)

theorem goodT_rmw {k : RmwKind} {L : Loc} {op : Val → Option Val} {f : Val → I.State} (hp0 : t.prom = [])
    (hb : t.Bnd mem.last) (hfc : FwdLeCoh t.views)
    (hex : I.exec t.st = some (.rmw k false L op fun v => .done (f v))) : ∃ o, GoodT A tid t mem o := by
  obtain ⟨s, c', hr, hp, hc⟩ := run_rmw_newest A tid (instrViews t (I.deps t.st)) (c := TicketStep.ctx0 tid t mem) hp0
    ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩ (instrViews_le hb.regs _) hfc k L op f
  exact goodT_of_run hex (fun l h => by cases h with | rmw => rfl | rmwRet _ h => cases h) hr hp hc

end Shapes

/-! ## From an invariant to `Progressive`

Each lock's operational invariant (the existing `step_inv`/`inv_init`) is kept
by every instruction step; at each pc of its per-thread invariant, the
instruction has one of the shapes above. `progressive_of_inv` combines
them, with `Config.Bnd` and `FwdLeCoh` carried along. -/

theorem init_thread {states : List I.State} {initMem : List (Loc × Val)} {tid : Nat} {t : Thread I}
    (h : (Config.init states initMem : Config I).threads[tid]? = some t) : ∃ s ∈ states, t = Thread.init s := by
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨s, hs, rfl⟩ := h
  exact ⟨s, List.mem_of_getElem? hs, rfl⟩

theorem startPF_init (states : List I.State) (initMem : List (Loc × Val)) :
    StartPF (Config.init states initMem : Config I) := fun _ _ h => by
  obtain ⟨s, -, rfl⟩ := init_thread h; rfl

theorem fwd_init (states : List I.State) (initMem : List (Loc × Val)) (tid : Nat) (t : Thread I)
    (h : (Config.init states initMem : Config I).threads[tid]? = some t) : FwdLeCoh t.views := by
  obtain ⟨s, -, rfl⟩ := init_thread h; exact fwdLeCoh_of_nil rfl

/-- A thread that has not halted takes a step (to rule out end pcs). -/
theorem stepOne_ne_none {A : Arch} {tid : Nat} {t : Thread I} {mem : Memory} (hh : t.halted = false) :
    stepOne A t tid mem ≠ none := by
  unfold Thread.halted at hh
  cases h : I.exec t.st with
  | none => rw [h] at hh; cases hh
  | some _ => simp [stepOne, h]

/-- **`Progressive` from an invariant `P`** kept by instruction steps, at
whose configurations every thread that has not halted, with `FwdLeCoh` and
bounded views, has a `GoodT` outcome. -/
theorem progressive_of_inv [I.LawfulState] {A : Arch} {c0 : Config I} (P : Config I → Prop) (h0 : P c0)
    (hb0 : c0.Bnd) (hf0 : ∀ (tid : Nat) (t : Thread I), c0.threads[tid]? = some t → FwdLeCoh t.views)
    (hstep : ∀ (c c' : Config I) (tid : Nat), P c → c'.Bnd → InstrBy A tid c c' → P c')
    (hthr : ∀ c, P c → ∀ (tid : Nat) (t : Thread I), c.threads[tid]? = some t → t.halted = false →
      FwdLeCoh t.views → t.Bnd c.mem.last → ∃ o, GoodT A tid t c.mem o) : Progressive A c0 := by
  have hPB : ∀ c, ReachPI A c0 c → P c ∧ c.Bnd := by
    intro c h
    induction h with
    | refl => exact ⟨h0, hb0⟩
    | @step c tid t outs o _ ht hs ho hp ih =>
      have hb := ih.2.succ (reach_mem_succs A 0 (tid := tid) (by simp [stepThread, ht, hs]) ho (by simp [hp]))
      exact ⟨hstep _ _ _ ih.1 hb ⟨_, _, _, ht, hs, ho, rfl⟩, hb⟩
  intro c hr tid t ht hh
  exact hthr c (hPB c hr).1 tid t ht hh (hr.fwd hf0 tid t ht) ((hPB c hr).2 tid t ht)

end Kraken.Promising.Live.Witness
