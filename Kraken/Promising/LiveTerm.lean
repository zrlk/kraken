/-
**Stage 4: termination on the semantic machine, and the
retry rank** (ISA-neutral, program-independent).

Everything here is about the *semantic* machine (`TraceSem`, `StepSem`,
`LiveSem.lean`), the reference semantics: certification is
`CertOkN` (certifiable within `fuel` instructions), not the executable search
`certify`. A `TraceSem` stutters **only at final configurations**
(`LiveSem.lean`, `TraceSem.step`), so "every trace reaches a final
configuration" is meaningful without any fairness hypothesis.

## Statements

- `TermFromSem A fuel c0 Fair`: every semantic trace from `c0` satisfying
  `Fair` reaches a final configuration.
- `TermBoundSem A fuel c0`: one index `K` at which every semantic trace from
  `c0` is final, whatever the schedule (no fairness). For a fixed finite
  client this is wait-freedom (= lock-freedom, the progress classes collapse).
- `TermBoundSem.termFromSem`: no fairness implies any fairness.

## Proof principles

- `termBoundSem_of_measure`: an invariant kept by `StepSem` and a measure that
  every `StepSem` from an invariant configuration lowers give `TermBoundSem`
  with `K` the measure of `c0`.
- `termBoundSem_of_threadRank`: the measure as a sum over threads of a
  per-thread rank `R` (lowered by the thread's own instruction steps,
  independent of its promise set and stable under memory extension) and of
  the thread's promise headroom `fuel * B - |prom|`. A promise step lowers the
  headroom: the promising thread must then certify within `fuel`
  instructions, so it has at most `fuel * B` promises (`prom_le_of_certOkN`,
  under `DropBounded A B`). **This is how outstanding promises are bounded:
  by certification, not by the program text.** A thread cannot keep
  promising: each promise uses up headroom that only its own instruction
  steps (which lower its rank) give back.

## The retry rank

In Kraken a failing `CAS` writes nothing (`runTree` `.rmw`, `op old = none`).
A CAS retry loop re-reads `l` and retries when the CAS reads a value other
than the one read at the top of the iteration. The rank is
`Memory.cntBelow mem l (coh l)`: the number of writes to `l` at or below the
thread's coherence view of `l`. It never drops (`coh` only grows), and is
stable under memory extension (`cntBelow_prefix`, given `coh l ≤ |M|`).

- `read_window` (one read of `l`, given `FwdLeCoh`, `LiveSemWitness.lean`):
  the timestamp read lies between the last write to `l` at or below the
  coherence view before the read and the one at or below the coherence view
  after it.
- `rank_of_window`: hence the rank does not drop, and **it strictly grows if
  the value read differs from the current value** (`Memory.curBelow`, the
  value of the last write at or below `coh l`) before the read, or from the
  current value after it.
- `cnt_or_cur`: a step that does not raise the rank does not change the
  current value.

So, as long as the value read at the top of an iteration is the current
value (a per-thread invariant), a failing CAS strictly raises the rank. The
rank is at most the number of `l`-messages, which successful CASes (executed
or promised) bound; that bound is per program (e.g. `LiveTermTreiber2.lean`).
-/
import Kraken.Promising.LiveSemWitness
import Kraken.Promising.LiveSemShape

namespace Kraken.Promising.Live.Term

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Termination statements (semantic machine) -/

/-- **Termination under `Fair` (semantic machine)**: every semantic trace
from `c0` satisfying `Fair` reaches a final configuration. -/
def TermFromSem (A : Arch) (fuel : Nat) (c0 : Config I) (Fair : (Nat → Config I) → Prop) : Prop :=
  ∀ tr : TraceSem A fuel I, tr.cfg 0 = c0 → Fair tr.cfg → ∃ j, (tr.cfg j).final = true

/-- **Bounded termination under every schedule (semantic machine)**: one
index bound `K` for all semantic traces from `c0`, with no fairness
hypothesis. A `TraceSem` stutters only at final configurations, so this says
that at most `K` machine steps (instruction or promise) can be taken from
`c0`, whatever the scheduler does. For a fixed finite client this is
wait-freedom (each thread finishes within a bounded number of steps). -/
def TermBoundSem (A : Arch) (fuel : Nat) (c0 : Config I) : Prop :=
  ∃ K, ∀ tr : TraceSem A fuel I, tr.cfg 0 = c0 → (tr.cfg K).final = true

/-- No fairness needed implies any fairness. -/
theorem TermBoundSem.termFromSem {A : Arch} {fuel : Nat} {c0 : Config I}
    (h : TermBoundSem A fuel c0) (Fair : (Nat → Config I) → Prop) : TermFromSem A fuel c0 Fair := by
  obtain ⟨K, hK⟩ := h
  exact fun tr h0 _ => ⟨K, hK tr h0⟩

/-- A final configuration stays final along a semantic trace (nothing is
enabled there, so the trace stutters). -/
theorem _root_.Kraken.Promising.Live.Sem.TraceSem.final_succ {A : Arch} {fuel : Nat} (tr : TraceSem A fuel I)
    {i : Nat} (h : (tr.cfg i).final = true) : (tr.cfg (i + 1)).final = true := by
  rcases tr.step i with ⟨tid, hs⟩ | ⟨-, he⟩
  · exact absurd ⟨_, hs⟩ (not_enabledSem_of_final h)
  · rw [he]; exact h

/-- **Termination from a measure**: an invariant kept by every semantic step
and a measure lowered by every semantic step from an invariant configuration
bound every semantic trace from `c0` by the measure of `c0`. -/
theorem termBoundSem_of_measure {A : Arch} {fuel : Nat} {c0 : Config I} (Inv : Config I → Prop)
    (μ : Config I → Nat) (h0 : Inv c0)
    (hinv : ∀ c c' tid, Inv c → StepSem A fuel tid c c' → Inv c')
    (hdec : ∀ c c' tid, Inv c → StepSem A fuel tid c c' → μ c' < μ c) :
    TermBoundSem A fuel c0 := by
  refine ⟨μ c0, fun tr h0' => ?_⟩
  have key : ∀ i, (tr.cfg i).final = true ∨ (Inv (tr.cfg i) ∧ μ (tr.cfg i) + i ≤ μ c0) := by
    intro i
    induction i with
    | zero => exact .inr ⟨h0' ▸ h0, by rw [h0']; omega⟩
    | succ i ih =>
      rcases ih with hf | ⟨hI, hle⟩
      · exact .inl (tr.final_succ hf)
      · rcases tr.step i with ⟨tid, hs⟩ | ⟨hf, he⟩
        · exact .inr ⟨hinv _ _ _ hI hs, by have := hdec _ _ _ hI hs; omega⟩
        · exact .inl (he ▸ hf)
  rcases key (μ c0) with hf | ⟨hI, hle⟩
  · exact hf
  · rcases tr.step (μ c0) with ⟨tid, hs⟩ | ⟨hf, -⟩
    · have := hdec _ _ _ hI hs; omega
    · exact hf

/-! ## Sums over threads -/

/-- The sum of `F i t` over the threads `t` of `c` (index `i`). -/
def tsum (c : Config I) (F : Nat → Thread I → Nat) : Nat :=
  ((List.range c.threads.size).map fun i => (c.threads[i]?.map (F i)).getD 0).sum

private theorem sum_range_le (n : Nat) (f g : Nat → Nat) (hle : ∀ i, i < n → g i ≤ f i) :
    ((List.range n).map g).sum ≤ ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil]
    have := ih fun i hi => hle i (by omega)
    have := hle n (by omega)
    omega

private theorem sum_range_lt (n : Nat) (f g : Nat → Nat) (j : Nat) (hj : j < n) (hjl : g j < f j)
    (hle : ∀ i, i < n → i ≠ j → g i ≤ f i) :
    ((List.range n).map g).sum < ((List.range n).map f).sum := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil]
    by_cases e : j = n
    · subst e
      have := sum_range_le j f g fun i hi => hle i (by omega) (by omega)
      omega
    · have := ih (by omega) fun i hi hij => hle i (by omega) hij
      have := hle n (by omega) (Ne.symm e)
      omega

private theorem sum_range_add (n : Nat) (f g : Nat → Nat) (j : Nat) (hj : j < n)
    (heq : ∀ i, i < n → i ≠ j → g i = f i) :
    ((List.range n).map g).sum + f j = ((List.range n).map f).sum + g j := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil]
    by_cases e : j = n
    · subst e
      have : ((List.range j).map g).sum = ((List.range j).map f).sum := by
        have h1 := sum_range_le j f g fun i hi => Nat.le_of_eq (heq i (by omega) (by omega))
        have h2 := sum_range_le j g f fun i hi => Nat.le_of_eq (heq i (by omega) (by omega)).symm
        omega
      omega
    · have := ih (by omega) fun i hi hij => heq i (by omega) hij
      have := heq n (by omega) (Ne.symm e)
      omega

/-- The value at index `i`, `0` if absent. -/
private abbrev tval (c : Config I) (F : Nat → Thread I → Nat) (i : Nat) : Nat := (c.threads[i]?.map (F i)).getD 0

theorem withThread_size (c : Config I) (tid : Nat) (t : Thread I) (mem : Memory) :
    (c.withThread tid t mem).threads.size = c.threads.size := by
  simp [Config.withThread]

/-- **A step of thread `tid` that lowers its term and no other lowers the
sum.** -/
theorem tsum_withThread_lt {c : Config I} {tid : Nat} {t t' : Thread I} {mem' : Memory}
    {F F' : Nat → Thread I → Nat} (ht : c.threads[tid]? = some t) (hlt : F' tid t' < F tid t)
    (hle : ∀ i u, i ≠ tid → c.threads[i]? = some u → F' i u ≤ F i u) :
    tsum (c.withThread tid t' mem') F' < tsum c F := by
  unfold tsum
  rw [withThread_size]
  refine sum_range_lt _ _ _ tid (lt_size_of_get? ht) ?_ fun i _ hi => ?_
  · simp only [SpinStep.wt_tid ht, ht, Option.map_some, Option.getD_some]; exact hlt
  · simp only [SpinStep.wt_ne ht hi]
    cases hu : c.threads[i]? with
    | none => simp
    | some u => simp only [Option.map_some, Option.getD_some]; exact hle i u hi hu

/-- **The sum after a step of thread `tid` that changes no other term.** -/
theorem tsum_withThread_add {c : Config I} {tid : Nat} {t t' : Thread I} {mem' : Memory}
    {F F' : Nat → Thread I → Nat} (ht : c.threads[tid]? = some t)
    (heq : ∀ i u, i ≠ tid → c.threads[i]? = some u → F' i u = F i u) :
    tsum (c.withThread tid t' mem') F' + F tid t = tsum c F + F' tid t' := by
  unfold tsum
  rw [withThread_size]
  have := sum_range_add c.threads.size (fun i => (c.threads[i]?.map (F i)).getD 0)
    (fun i => ((c.withThread tid t' mem').threads[i]?.map (F' i)).getD 0) tid (lt_size_of_get? ht)
    fun i _ hi => by
      simp only [SpinStep.wt_ne ht hi]
      cases hu : c.threads[i]? with
      | none => simp
      | some u => simp only [Option.map_some, Option.getD_some]; exact heq i u hi hu
  simpa only [SpinStep.wt_tid ht, ht, Option.map_some, Option.getD_some] using this

/-- A term bounded at every thread bounds the sum by the number of threads. -/
theorem tsum_le {c : Config I} {F : Nat → Thread I → Nat} {M : Nat}
    (h : ∀ i u, c.threads[i]? = some u → F i u ≤ M) : tsum c F ≤ c.threads.size * M := by
  unfold tsum
  have := sum_range_le c.threads.size (fun _ => M) (fun i => (c.threads[i]?.map (F i)).getD 0) fun i _ => by
    cases hu : c.threads[i]? with
    | none => simp
    | some u => simp only [Option.map_some, Option.getD_some]; exact h i u hu
  have hc : ∀ n, ((List.range n).map fun _ => M).sum = n * M := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil, ih, Nat.succ_mul]
      omega
  rw [hc] at this
  exact this

/-! ## Termination from a per-thread rank -/

/-- The measure of `termBoundSem_of_threadRank`: per thread, `B + 1` times
its rank plus its promise headroom `fuel * B - |prom|`. -/
def rankMeasure (fuel B : Nat) (R : Thread I → Memory → Nat) (c : Config I) : Nat :=
  tsum c fun _ (u : Thread I) => (B + 1) * R u c.mem + (fuel * B - u.prom.length)

/-- **Termination from a per-thread rank (semantic machine, no fairness).**
An invariant `Inv` kept by every semantic step, under which

- every thread drops at most `B` promises per instruction (`DropBounded`)
  and has at most `fuel * B` promises (both follow from certification);
- a thread's rank `R` does not depend on its promise set, and is stable
  under extensions of the memory (steps of other threads, and its own
  promises);
- every instruction step of a thread to an `Inv` configuration lowers that
  thread's rank,

bounds every semantic trace from `c0` (`rankMeasure`). A promise step lowers
the promising thread's headroom, since it must then certify (`PromSem`); an
instruction step lowers the rank by at least one and gives back at most `B`
headroom. -/
theorem termBoundSem_of_threadRank {A : Arch} {fuel B : Nat} {c0 : Config I} (Inv : Config I → Prop)
    (R : Thread I → Memory → Nat) (h0 : Inv c0)
    (hinv : ∀ c c' tid, Inv c → StepSem A fuel tid c c' → Inv c')
    (hpb : ∀ c, Inv c → ∀ (i : Nat) (u : Thread I), c.threads[i]? = some u → u.prom.length ≤ fuel * B)
    (hdrop : ∀ c, Inv c → ∀ (i : Nat) (u : Thread I), c.threads[i]? = some u → DropBounded A B i u)
    (hstab : ∀ c, Inv c → ∀ (i : Nat) (u : Thread I), c.threads[i]? = some u → ∀ mem', c.mem.Prefix mem' → R u mem' = R u c.mem)
    (hprom : ∀ (u : Thread I) (p : List Time) (mem : Memory), R { u with prom := p } mem = R u mem)
    (hstep : ∀ c (tid : Nat) (t : Thread I) outs (o : Outcome I), Inv c → c.threads[tid]? = some t → stepOne A t tid c.mem = some outs →
      .ok o ∈ outs → Inv (c.withThread tid o.thread o.mem) → R o.thread o.mem < R t c.mem) :
    TermBoundSem A fuel c0 := by
  refine termBoundSem_of_measure Inv (rankMeasure fuel B R) h0 hinv fun c c' tid hI hs => ?_
  have hI' := hinv _ _ _ hI hs
  rcases hs with ⟨t, outs, o, ht, hso, ho, -, rfl⟩ | ⟨t, w, ht, -, -, rfl⟩
  · have hpre : c.mem.Prefix o.mem := Memory.Prefix.stepOne hso ho
    have hr := hstep c tid t outs o hI ht hso ho hI'
    have hd : t.prom.length ≤ o.thread.prom.length + B :=
      hdrop c hI tid t ht c.mem (t, c.mem) (o.thread, o.mem) (.refl _) ⟨outs, o, hso, ho, rfl⟩
    unfold rankMeasure
    refine tsum_withThread_lt ht ?_ fun i u hi hu => ?_
    · show (B + 1) * R o.thread o.mem + (fuel * B - o.thread.prom.length) <
        (B + 1) * R t c.mem + (fuel * B - t.prom.length)
      have : (B + 1) * (R o.thread o.mem + 1) ≤ (B + 1) * R t c.mem := Nat.mul_le_mul_left _ hr
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    · show (B + 1) * R u o.mem + _ ≤ (B + 1) * R u c.mem + _
      rw [hstab c hI i u hu o.mem hpre]
      exact Nat.le_refl _
  · have hpre : c.mem.Prefix (c.mem.append w).1 := Memory.Prefix.append _ _
    have hp1 := hpb _ hI' tid _ (SpinStep.wt_tid ht)
    unfold rankMeasure
    refine tsum_withThread_lt ht ?_ fun i u hi hu => ?_
    · show (B + 1) * R (promThread t c.mem w) (c.mem.append w).1 + (fuel * B - (promThread t c.mem w).prom.length) <
        (B + 1) * R t c.mem + (fuel * B - t.prom.length)
      rw [hprom, hstab c hI tid t ht _ hpre]
      simp only [List.length_append, List.length_singleton] at hp1 ⊢
      omega
    · show (B + 1) * R u (c.mem.append w).1 + _ ≤ (B + 1) * R u c.mem + _
      rw [hstab c hI i u hu _ hpre]
      exact Nat.le_refl _

/-! ## The retry rank: writes at or below a view -/

/-- The number of writes to `l` with timestamp in `(0, n]`. -/
def _root_.Kraken.Promising.Memory.cntBelow (m : Memory) (l : Loc) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    match m.get? (n + 1) with
    | some w => if w.loc = l then m.cntBelow l n + 1 else m.cntBelow l n
    | none => m.cntBelow l n

/-- The value of the last write to `l` at or below `n` (the initial value if
there is none): what a read of `l` with coherence bound `n` and no newer
choice returns. -/
def _root_.Kraken.Promising.Memory.curBelow (m : Memory) (l : Loc) (n : Nat) : Val :=
  (m.read? l (m.lastWriteBelow l n)).getD 0

section MemRank

variable {m m' : Memory} {l : Loc}

theorem cntBelow_succ_le (m : Memory) (l : Loc) (n : Nat) : m.cntBelow l n ≤ m.cntBelow l (n + 1) := by
  show _ ≤ (match m.get? (n + 1) with
    | some w => if w.loc = l then m.cntBelow l n + 1 else m.cntBelow l n
    | none => m.cntBelow l n)
  split
  · split
    · exact Nat.le_succ _
    · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem cntBelow_mono {a b : Nat} (h : a ≤ b) : m.cntBelow l a ≤ m.cntBelow l b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (cntBelow_succ_le m l _)

theorem cntBelow_succ_of_write {n : Nat} {w : Msg} (hw : m.get? (n + 1) = some w) (hl : w.loc = l) :
    m.cntBelow l (n + 1) = m.cntBelow l n + 1 := by
  simp [Memory.cntBelow, hw, hl]

/-- No write in `(lastWriteBelow n, n]`: the count is the count at the last write. -/
theorem cntBelow_lastWriteBelow (n : Nat) : m.cntBelow l (m.lastWriteBelow l n) = m.cntBelow l n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases hw : m.get? (n + 1) with
    | none => simp only [Memory.lastWriteBelow, Memory.cntBelow, hw]; exact ih
    | some w =>
      by_cases hl : w.loc = l
      · simp only [Memory.lastWriteBelow, hw, hl, ite_true]
      · simp only [Memory.lastWriteBelow, Memory.cntBelow, hw, hl, ite_false]; exact ih

/-- A write to `l` (or the initial write) at or below `b` is at or below the
last one. -/
theorem le_lastWriteBelow {t b : Nat} {v : Val} (hr : m.read? l t = some v) (htb : t ≤ b) :
    t ≤ m.lastWriteBelow l b := by
  refine Nat.le_of_not_lt fun hlt => ?_
  rcases m.read?_eq_some hr with ⟨rfl, -⟩ | ⟨w, hw, hl, -⟩
  · exact Nat.not_lt_zero _ hlt
  · exact Memory.not_write_of_lastWriteBelow_lt m l b t w hlt htb hw hl

theorem read?_lastWriteBelow (m : Memory) (l : Loc) (n : Nat) :
    m.read? l (m.lastWriteBelow l n) = some (m.curBelow l n) := by
  unfold Memory.curBelow
  by_cases h0 : m.lastWriteBelow l n = 0
  · rw [h0]; rfl
  · obtain ⟨w, hw, hl⟩ := m.get?_lastWriteBelow l n h0
    have : m.read? l (m.lastWriteBelow l n) = some w.val := by
      unfold Memory.read?; rw [ite_eq_right_iff.mpr (fun h => absurd h h0), hw]; simp [hl]
    rw [this]; rfl

theorem lastWriteBelow_mono {a b : Nat} (h : a ≤ b) : m.lastWriteBelow l a ≤ m.lastWriteBelow l b :=
  le_lastWriteBelow (read?_lastWriteBelow m l a) (Nat.le_trans (m.lastWriteBelow_le l a) h)

/-- Under a write-free window `(t, hi]`, the last write at or below `b ≤ hi`
is at or below `t`. -/
theorem lastWriteBelow_le_of_writeIn {t hi b : Nat} (hw : m.writeIn l t hi = false) (hb : b ≤ hi) :
    m.lastWriteBelow l b ≤ t := by
  refine Nat.le_of_not_lt fun hlt => ?_
  obtain ⟨w, hw', hl⟩ := m.get?_lastWriteBelow l b (by omega_t)
  rw [(m.writeIn_iff l t hi).mpr ⟨_, w, hlt, Nat.le_trans (m.lastWriteBelow_le l b) hb, hw', hl⟩] at hw
  cases hw

/-- **The count grows strictly with the last write.** -/
theorem cntBelow_lt_of_lastWriteBelow_lt {a b : Nat} (h : m.lastWriteBelow l a < m.lastWriteBelow l b) :
    m.cntBelow l a < m.cntBelow l b := by
  obtain ⟨w, hw, hl⟩ := m.get?_lastWriteBelow l b (by omega_t)
  obtain ⟨k, hk⟩ : ∃ k, m.lastWriteBelow l b = k + 1 := ⟨m.lastWriteBelow l b - 1, by omega_t⟩
  rw [hk] at hw h
  rw [← cntBelow_lastWriteBelow a, ← cntBelow_lastWriteBelow b, hk, cntBelow_succ_of_write hw hl]
  exact Nat.lt_succ_of_le (cntBelow_mono (by omega_t))

/-- **A step that does not raise the count keeps the current value.** -/
theorem cnt_or_cur {a b : Nat} (h : a ≤ b) :
    m.cntBelow l a < m.cntBelow l b ∨ (m.cntBelow l a = m.cntBelow l b ∧ m.curBelow l a = m.curBelow l b) := by
  rcases Nat.lt_or_ge (m.lastWriteBelow l a) (m.lastWriteBelow l b) with hlt | hge
  · exact .inl (cntBelow_lt_of_lastWriteBelow_lt hlt)
  · have he : m.lastWriteBelow l a = m.lastWriteBelow l b := Nat.le_antisymm (lastWriteBelow_mono h) hge
    refine .inr ⟨by rw [← cntBelow_lastWriteBelow a, ← cntBelow_lastWriteBelow b, he], ?_⟩
    unfold Memory.curBelow; rw [he]

/-- **The retry rank of one read** (`read_window`'s conclusion): reading `v`
at a timestamp between the last writes at or below `a` and `b` does not
lower the count from `a` to `b`, and raises it strictly if `v` is not the
current value at `a`, or not the current value at `b`. -/
theorem rank_of_window {t a b : Nat} {v : Val} (hr : m.read? l t = some v) (h1 : m.lastWriteBelow l a ≤ t)
    (h2 : t ≤ m.lastWriteBelow l b) :
    m.cntBelow l a ≤ m.cntBelow l b ∧ (v ≠ m.curBelow l a → m.cntBelow l a < m.cntBelow l b) ∧
      (v ≠ m.curBelow l b → m.cntBelow l a < m.cntBelow l b) := by
  refine ⟨?_, fun hne => cntBelow_lt_of_lastWriteBelow_lt ?_, fun hne => cntBelow_lt_of_lastWriteBelow_lt ?_⟩
  · rw [← cntBelow_lastWriteBelow a, ← cntBelow_lastWriteBelow b]; exact cntBelow_mono (by omega_t)
  · refine Nat.lt_of_lt_of_le (Nat.lt_of_le_of_ne h1 fun e => hne ?_) h2
    have := read?_lastWriteBelow m l a
    rw [e, hr] at this; exact Option.some.inj this
  · refine Nat.lt_of_le_of_lt h1 (Nat.lt_of_le_of_ne h2 fun e => hne ?_)
    have := read?_lastWriteBelow m l b
    rw [← e, hr] at this; exact Option.some.inj this

/-- The last write at or below `b` only grows with the memory. -/
theorem lastWriteBelow_prefix_le (hp : m.Prefix m') (b : Nat) : m.lastWriteBelow l b ≤ m'.lastWriteBelow l b := by
  have hr := read?_lastWriteBelow m l b
  have hle : m.lastWriteBelow l b ≤ m.last := by
    rcases m.read?_eq_some hr with ⟨h0, -⟩ | ⟨w, hw, -⟩
    · omega_t
    · exact m.last_le_of_get?_eq_some hw
  exact le_lastWriteBelow (by rw [hp.read? hle]; exact hr) (m.lastWriteBelow_le l b)

/-- **Below `|M|`, the last write, the count and the current value are
stable under memory extension.** -/
theorem below_prefix (hp : m.Prefix m') : ∀ {b : Nat}, b ≤ m.last →
    m'.lastWriteBelow l b = m.lastWriteBelow l b ∧ m'.cntBelow l b = m.cntBelow l b
  | 0, _ => ⟨rfl, rfl⟩
  | b + 1, hb => by
    obtain ⟨ih1, ih2⟩ := below_prefix hp (b := b) (by omega_t)
    have hg := hp.get? hb
    refine ⟨?_, ?_⟩
    · show (match m'.get? (b + 1) with
        | some w => if w.loc = l then b + 1 else m'.lastWriteBelow l b
        | none => m'.lastWriteBelow l b) = (match m.get? (b + 1) with
        | some w => if w.loc = l then b + 1 else m.lastWriteBelow l b
        | none => m.lastWriteBelow l b)
      rw [hg, ih1]
    · show (match m'.get? (b + 1) with
        | some w => if w.loc = l then m'.cntBelow l b + 1 else m'.cntBelow l b
        | none => m'.cntBelow l b) = (match m.get? (b + 1) with
        | some w => if w.loc = l then m.cntBelow l b + 1 else m.cntBelow l b
        | none => m.cntBelow l b)
      rw [hg, ih2]

theorem cntBelow_prefix (hp : m.Prefix m') {b : Nat} (hb : b ≤ m.last) : m'.cntBelow l b = m.cntBelow l b :=
  (below_prefix hp hb).2

theorem curBelow_prefix (hp : m.Prefix m') {b : Nat} (hb : b ≤ m.last) : m'.curBelow l b = m.curBelow l b := by
  unfold Memory.curBelow
  rw [(below_prefix hp hb).1, hp.read? (Nat.le_trans (m.lastWriteBelow_le l b) hb)]

/-- The count at any view is at most the count of all writes to `l`. -/
theorem cntBelow_le_last (m : Memory) (l : Loc) (b : Nat) : m.cntBelow l b ≤ m.cntBelow l m.last := by
  rcases Nat.le_total b m.last with h | h
  · exact cntBelow_mono h
  · rw [← cntBelow_lastWriteBelow b]
    exact cntBelow_mono (by
      rcases m.read?_eq_some (read?_lastWriteBelow m l b) with ⟨h0, -⟩ | ⟨w, hw, -⟩
      · omega_t
      · exact m.last_le_of_get?_eq_some hw)

end MemRank

/-! ## The retry rank: one read -/

section Window

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **The window of one read of `l`** (given `FwdLeCoh`): the timestamp read
is at or above the last write to `l` at or below the coherence view before
the read (the read's bound is at or above that view, and no write to `l` lies
between the timestamp and the bound), and at or below the last write at or
below the coherence view after it (`readNext_coh_ge`). -/
theorem read_window {c : Ctx} (hfc : Witness.FwdLeCoh c.views) {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) :
    x.2.2.mem = c.mem ∧ x.2.2.prom = c.prom ∧ c.mem.read? l x.1 = some x.2.1 ∧
      c.mem.lastWriteBelow l (c.views.getCoh l) ≤ x.1 ∧ x.1 ≤ c.mem.lastWriteBelow l (x.2.2.views.getCoh l) ∧
      ∀ l', c.views.getCoh l' ≤ x.2.2.views.getCoh l' := by
  obtain ⟨t, v, rfl, -, hr, hw, -⟩ := (mem_readSuccs A).mp hx
  exact ⟨rfl, rfl, hr, lastWriteBelow_le_of_writeIn hw (Nat.le_max_right _ _),
    le_lastWriteBelow hr (Witness.readNext_coh_ge A iv hfc _ _ _ _ _ _),
    SpinStep.readNext_getCoh A iv c k xcl l noRet t v⟩

variable {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))} {o : Outcome I}

theorem coh_of_runK {c' : Ctx} (hv : ({ o.thread.views with vCAP := 0 } : Views) = { c'.views with vCAP := 0 })
    (l : Loc) : o.thread.views.getCoh l = c'.views.getCoh l :=
  SpinSwpStep.getCoh_congr (by have := congrArg Views.coh hv; exact this) l

/-- **The window of a load instruction** (`read_window` for the whole
instruction): memory and promises unchanged. -/
theorem load_window (hfc : Witness.FwdLeCoh t.views) {k : LoadKind} {l : Loc} {f : Val → I.State}
    (hex : I.exec t.st = some (.load k false l fun v => .done (f v))) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) :
    ∃ ts v, o.thread.st = f v ∧ o.mem = mem ∧ o.thread.prom = t.prom ∧ mem.read? l ts = some v ∧
      mem.lastWriteBelow l (t.views.getCoh l) ≤ ts ∧ ts ≤ mem.lastWriteBelow l (o.thread.views.getCoh l) := by
  obtain ⟨tree, c', hex', hr, hp, hv, hm, -⟩ := SLR.stepOne_runK A hs ho
  obtain rfl : tree = _ := Option.some.inj (hex'.symm.trans hex)
  simp only [runTree, List.mem_flatMap] at hr
  obtain ⟨⟨ts, v, c1⟩, hx, h⟩ := hr
  obtain ⟨hst, rfl⟩ := TicketStep.run_done A tid (instrViews t (I.deps t.st)) h
  obtain ⟨e1, e0, e2, e3, e4, -⟩ := read_window A (instrViews t (I.deps t.st))
    (c := { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] }) hfc hx
  refine ⟨ts, v, hst, hm.trans e1, hp.trans e0, e2, e3, ?_⟩
  rw [coh_of_runK hv l]; exact e4

/-- **The window of an RMW instruction** (`read_window` for its read; the
coherence view after the instruction is at or above the one after the read,
in the memory after the instruction). -/
theorem rmw_window (hA : A.rmwFence = false) (hfc : Witness.FwdLeCoh t.views) {k : RmwKind} {l : Loc}
    {op : Val → Option Val} {f : Val → I.State}
    (hex : I.exec t.st = some (.rmw k false l op fun v => .done (f v))) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) :
    ∃ ts v, o.thread.st = f v ∧ mem.read? l ts = some v ∧
      mem.lastWriteBelow l (t.views.getCoh l) ≤ ts ∧ ts ≤ o.mem.lastWriteBelow l (o.thread.views.getCoh l) := by
  obtain ⟨tree, c', hex', hr, -, hv, hm, -⟩ := SLR.stepOne_runK A hs ho
  obtain rfl : tree = _ := Option.some.inj (hex'.symm.trans hex)
  simp only [runTree, hA, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap] at hr
  obtain ⟨⟨ts, old, c1⟩, hx, h⟩ := hr
  obtain ⟨e1, -, e2, e3, e4, -⟩ := read_window A (instrViews t (I.deps t.st))
    (c := { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] }) hfc hx
  simp only at e1 e2 e3 e4
  rw [coh_of_runK hv l, hm]
  cases hop : op old with
  | none =>
    simp only [hop] at h
    obtain ⟨hst, rfl⟩ := TicketStep.run_done A tid (instrViews t (I.deps t.st)) h
    exact ⟨ts, old, hst, e2, e3, e1 ▸ e4⟩
  | some new =>
    simp only [hop, List.mem_flatMap] at h
    obtain ⟨c2, h2, h⟩ := h
    obtain ⟨hst, hc⟩ := TicketStep.run_done A tid (instrViews t (I.deps t.st)) h
    obtain ⟨q1, -, q3, -⟩ := TsoRmw.rmwPost_keeps (A.rmwKind k == RmwKind.acqRel && !false) c2 l
    rw [← hc] at q1 q3
    have hc2 := (Witness.cstep_writeSuccs (P := fun _ => False) A tid (instrViews t (I.deps t.st)) h2).coh l
    have hp2 : c1.mem.Prefix c2.mem := (writeSuccs_dord A tid (instrViews t (I.deps t.st)) h2).mem
    refine ⟨ts, old, hst, e2, e3, ?_⟩
    rw [q3 l, q1]
    rw [e1] at hp2
    exact Nat.le_trans e4 (Nat.le_trans (lastWriteBelow_prefix_le hp2 _) (lastWriteBelow_mono hc2))

end Window

/-! ## The retry rank across one step -/

section Across

variable {m m' : Memory} {l : Loc}

/-- **The count across one step of the thread** (memory extended, coherence
view grown from `a ≤ |M|` to `b`): it does not drop, and if it does not grow
the current value stays. -/
theorem step_cnt (hp : m.Prefix m') {a b : Nat} (ha : a ≤ m.last) (hab : a ≤ b) :
    m.cntBelow l a ≤ m'.cntBelow l b ∧
      (m.cntBelow l a < m'.cntBelow l b ∨ (m.cntBelow l a = m'.cntBelow l b ∧ m.curBelow l a = m'.curBelow l b)) := by
  rw [← cntBelow_prefix hp ha, ← curBelow_prefix hp ha]
  have h := cnt_or_cur (m := m') (l := l) hab
  exact ⟨by rcases h with h | h <;> omega, h⟩

/-- **`rank_of_window` across one step**: a read in `m` at a timestamp
between the last write at or below `a ≤ |M|` (in `m`) and the last write at
or below `b` in the extended memory `m'`. -/
theorem window_rank (hp : m.Prefix m') {a b ts : Nat} {v : Val} (ha : a ≤ m.last) (hr : m.read? l ts = some v)
    (h1 : m.lastWriteBelow l a ≤ ts) (h2 : ts ≤ m'.lastWriteBelow l b) :
    (v ≠ m.curBelow l a → m.cntBelow l a < m'.cntBelow l b) ∧
      (v ≠ m'.curBelow l b → m.cntBelow l a < m'.cntBelow l b) := by
  have hr' : m'.read? l ts = some v := by rw [hp.read? (SpinSemSwpSolo.read_le hr)]; exact hr
  obtain ⟨e1, -⟩ := below_prefix hp (l := l) ha
  obtain ⟨-, r2, r3⟩ := rank_of_window hr' (by rw [e1]; exact h1) h2
  rw [← cntBelow_prefix hp ha, ← curBelow_prefix hp ha]
  exact ⟨r2, r3⟩

end Across

/-! ## Bounding the count: writes against successful writes and promises

The count of writes to `l` in memory is bounded per program by an invariant
of the form "writes to `l` ≤ Σ over threads of (writes to `l` the thread has
executed + its outstanding promises to `l`)". `count_weff` is one write's
contribution: an append adds a write, a fulfilment removes a promise. -/

section Count

/-- The number of the promises `p` whose message in `m` is a write to `l`. -/
def _root_.Kraken.Promising.Memory.promAt (m : Memory) (l : Loc) (p : List Time) : Nat :=
  p.countP fun ts => match m.get? ts with
    | some w => w.loc == l
    | none => false

variable {m m' : Memory} {l : Loc} {p p' : List Time}

theorem promAt_le_length : m.promAt l p ≤ p.length := List.countP_le_length

theorem promAt_prefix (hp : m.Prefix m') (h : ∀ ts ∈ p, ts ≤ m.last) : m'.promAt l p = m.promAt l p := by
  unfold Memory.promAt
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [List.countP_cons, List.countP_cons, hp.get? (h a List.mem_cons_self),
      ih fun ts hts => h ts (List.mem_cons_of_mem _ hts)]

theorem promAt_erase {ts : Time} {w : Msg} (hts : ts ∈ p) (hw : m.get? ts = some w) :
    m.promAt l p = m.promAt l (p.erase ts) + (if w.loc = l then 1 else 0) := by
  unfold Memory.promAt
  rw [(List.perm_cons_erase hts).countP_eq, List.countP_cons, hw]
  by_cases e : w.loc = l <;> simp [e]

/-- One more message: the count of writes to `l` grows iff it is one. -/
theorem cntBelow_append (m : Memory) (w : Msg) (l : Loc) :
    (m.append w).1.cntBelow l (m.append w).1.last = m.cntBelow l m.last + (if w.loc = l then 1 else 0) := by
  have hl : (m.append w).1.last = m.last + 1 := by simp [Memory.append, Memory.last]
  rw [hl]
  have hc := cntBelow_prefix (l := l) (Memory.Prefix.append m w) (Nat.le_refl m.last)
  by_cases e : w.loc = l
  · rw [cntBelow_succ_of_write (Memory.get?_append_last m w) e, hc]; simp [e]
  · have : (m.append w).1.cntBelow l (m.last + 1) = (m.append w).1.cntBelow l m.last := by
      simp [Memory.cntBelow, Memory.get?_append_last, e]
    rw [this, hc]; simp [e]

/-- A promise of `w`: one more promise to `l` iff `w` is to `l`. -/
theorem promAt_promise (w : Msg) (hp : ∀ ts ∈ p, ts ≤ m.last) :
    (m.append w).1.promAt l (p ++ [(m.append w).2]) = m.promAt l p + (if w.loc = l then 1 else 0) := by
  have h1 := promAt_prefix (l := l) (Memory.Prefix.append m w) hp
  unfold Memory.promAt at h1 ⊢
  rw [List.countP_append, h1, List.countP_singleton]
  have : (m.append w).2 = m.last + 1 := rfl
  rw [this, Memory.get?_append_last]
  by_cases e : w.loc = l <;> simp [e]

/-- The memory and promise effect of one write (`spec_store_p`,
`SpinSemShape.spec_rmwo_p`): an append of `w`, or the fulfilment of an
outstanding promise of `w`. -/
def WEff (m m' : Memory) (p p' : List Time) (w : Msg) : Prop :=
  (m' = (m.append w).1 ∧ p' = (p ++ [m.last + 1]).erase (m.last + 1)) ∨
    (∃ ts ∈ p, m.get? ts = some w ∧ m' = m ∧ p' = p.erase ts)

theorem WEff.of_store {w : Msg} {P : Prop} {A B C : Time → Prop}
    (h : (m' = (m.append w).1 ∧ p' = (p ++ [m.last + 1]).erase (m.last + 1) ∧ P) ∨
      (∃ ts ∈ p, m.get? ts = some w ∧ A ts ∧ B ts ∧ m' = m ∧ p' = p.erase ts ∧ C ts)) : WEff m m' p p' w := by
  rcases h with ⟨a, b, -⟩ | ⟨ts, hts, a, -, -, b, c, -⟩
  · exact .inl ⟨a, b⟩
  · exact .inr ⟨ts, hts, a, b, c⟩

theorem WEff.of_rmw {w : Msg} {P : Prop} {A C : Time → Prop}
    (h : (m' = (m.append w).1 ∧ p' = (p ++ [m.last + 1]).erase (m.last + 1) ∧ P) ∨
      (∃ ts ∈ p, m.get? ts = some w ∧ A ts ∧ m' = m ∧ p' = p.erase ts ∧ C ts)) : WEff m m' p p' w := by
  rcases h with ⟨a, b, -⟩ | ⟨ts, hts, a, -, b, c, -⟩
  · exact .inl ⟨a, b⟩
  · exact .inr ⟨ts, hts, a, b, c⟩

/-- One write drops at most one promise. -/
theorem WEff.len {w : Msg} (h : WEff m m' p p' w) : p.length ≤ p'.length + 1 := by
  rcases h with ⟨-, rfl⟩ | ⟨ts, hts, -, -, rfl⟩
  · rw [List.length_erase]; split <;> simp <;> omega
  · rw [List.length_erase_of_mem hts]; omega

/-- **One write's contribution to the count invariant**: the count of writes
to `l` plus the promises to `l` grows by one iff the write is to `l`; the
promises stay at most `|M|`. -/
theorem count_weff {w : Msg} (hp : ∀ ts ∈ p, ts ≤ m.last) (h : WEff m m' p p' w) :
    m'.cntBelow l m'.last + m.promAt l p = m.cntBelow l m.last + m'.promAt l p' + (if w.loc = l then 1 else 0) ∧
      ∀ ts ∈ p', ts ≤ m'.last := by
  rcases h with ⟨rfl, rfl⟩ | ⟨ts, hts, hw, rfl, rfl⟩
  · rw [SemShape.erase_fresh hp, cntBelow_append, promAt_prefix (Memory.Prefix.append m w) hp]
    refine ⟨by omega, fun ts hts => Nat.le_trans (hp ts hts) (Memory.Prefix.append m w).last_le⟩
  · rw [promAt_erase (l := l) hts hw]
    exact ⟨by omega, fun ts' hts' => hp ts' (List.mem_of_mem_erase hts')⟩

end Count

end Kraken.Promising.Live.Term
