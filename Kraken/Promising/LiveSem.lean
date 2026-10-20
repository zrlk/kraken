/-
**Stage 3: the machine with *semantic*
certification** (ISA-neutral, program-independent).

The existing machine (`succs`, `Machine.lean`) keeps an instruction step of a
thread with outstanding promises, and offers a promise step, only when the
executable search `certify` reports a certification within `fuel`
instructions. `certify.go`'s visited set ignores the remaining fuel, so the
search is incomplete (`succs` is not monotone in fuel, KNOWN_GAPS); the existing
`Ticket.TicketLive fuel` is therefore a statement about that search and may be
false. The intended (paper) notion is *certifiable within fuel*: `CertOkN`
(`LiveWfInstr.lean`). This module restates the machine, traces and fairness
with `CertOkN` in place of `certify`; nothing existing is changed.

- `InstrSem`: an instruction step whose resulting thread is certifiable
  within `fuel` instructions against the resulting memory.
- `PromSem`: the paper's promise rule: append any message of the thread and
  add its timestamp to the thread's promises; the resulting thread must be
  certifiable within `fuel`.
- `TraceSem` (stuttering at final configurations, as `TraceS`),
  `EnabledSem`, `WeakFairSem`, `WeakFairInstrSem`, `LiveFromSem`. Memory
  fairness is `MemFair` (`LiveTrace.lean`), which does not mention `succs`.
- `Config.Bnd.semStep`: bounded configurations stay bounded.
- `not_enabledSem_of_final`: nothing is enabled at a final configuration.
- `weakFairInstrSem_of_weakFairSem`: under `DropBounded`, weak fairness gives
  weak fairness for instruction steps (a promise step's resulting thread is
  certifiable, so it has at most `fuel * B` promises).
- `coh_lt_of_certOkN`: a certifiable thread has no dead promise: every
  outstanding promise lies above the thread's `coh` of its location.
-/
import Kraken.Promising.LiveWfInstr
import Kraken.Promising.LiveWfProm
import Kraken.Promising.LiveSpinStep

namespace Kraken.Promising.Live.Sem

open Kraken.Promising Kraken.Promising.Live

variable {I : ISA}

/-! ## Steps with semantic certification -/

/-- **An instruction step of `tid` with semantic certification**: some
successful outcome of its next instruction, after which the thread can empty
its promise set alone within `fuel` instructions. -/
def InstrSem (A : Arch) (fuel tid : Nat) (c c' : Config I) : Prop :=
  ∃ t outs o, c.threads[tid]? = some t ∧ stepOne A t tid c.mem = some outs ∧ .ok o ∈ outs ∧
    CertOkN A tid o.thread o.mem fuel ∧ c' = c.withThread tid o.thread o.mem

/-- The thread after promising the message appended to `mem`. -/
abbrev promThread (t : Thread I) (mem : Memory) (w : Msg) : Thread I :=
  { t with prom := t.prom ++ [(mem.append w).2] }

/-- **A promise step of `tid` (the paper's rule)**: append any message of
`tid` and promise it; the thread must then be certifiable within `fuel`. -/
def PromSem (A : Arch) (fuel tid : Nat) (c c' : Config I) : Prop :=
  ∃ (t : Thread I) (w : Msg), c.threads[tid]? = some t ∧ w.tid = tid ∧
    CertOkN A tid (promThread t c.mem w) (c.mem.append w).1 fuel ∧
    c' = c.withThread tid (promThread t c.mem w) (c.mem.append w).1

/-- A step of thread `tid`. -/
def StepSem (A : Arch) (fuel tid : Nat) (c c' : Config I) : Prop :=
  InstrSem A fuel tid c c' ∨ PromSem A fuel tid c c'

/-- **A trace of the semantic machine**, stuttering only at a final
configuration (as `TraceS`). -/
structure TraceSem (A : Arch) (fuel : Nat) (I : ISA) where
  cfg : Nat → Config I
  step : ∀ i, (∃ tid, StepSem A fuel tid (cfg i) (cfg (i + 1))) ∨ ((cfg i).final = true ∧ cfg (i + 1) = cfg i)

/-- Thread `tid` can take a step. -/
def EnabledSem (A : Arch) (fuel tid : Nat) (c : Config I) : Prop :=
  ∃ c', StepSem A fuel tid c c'

/-- Thread `tid` can take an instruction step. -/
def InstrEnabledSem (A : Arch) (fuel tid : Nat) (c : Config I) : Prop :=
  ∃ c', InstrSem A fuel tid c c'

/-- **Weak fairness** (semantic): a thread enabled from some point on takes a
step (instruction or promise) infinitely often. -/
def WeakFairSem (A : Arch) (fuel : Nat) (cfg : Nat → Config I) : Prop :=
  ∀ tid, EvAlways (fun i => EnabledSem A fuel tid (cfg i)) →
    InfOften (fun i => StepSem A fuel tid (cfg i) (cfg (i + 1)))

/-- Weak fairness for instruction steps (semantic). -/
def WeakFairInstrSem (A : Arch) (fuel : Nat) (cfg : Nat → Config I) : Prop :=
  ∀ tid, EvAlways (fun i => InstrEnabledSem A fuel tid (cfg i)) →
    InfOften (fun i => InstrSem A fuel tid (cfg i) (cfg (i + 1)))

/-- **Liveness from `c0`** on the semantic machine (as `LiveFrom`). -/
def LiveFromSem (A : Arch) (fuel : Nat) (c0 : Config I) (Fair : (Nat → Config I) → Prop)
    (Waiting Done : Nat → Config I → Prop) : Prop :=
  ∀ tr : TraceSem A fuel I, tr.cfg 0 = c0 → Fair tr.cfg →
    ∀ tid i, Waiting tid (tr.cfg i) → ∃ j, i ≤ j ∧ Done tid (tr.cfg j)

/-- **Deadlock-freedom from `c0` on the semantic machine** (the
`Spin.ProgressFrom` shape over `TraceSem`; moved here from `LiveSpinSem`, same
full name): on every semantic trace from `c0` satisfying
`Fair`, if a thread is `Waiting` at index `i`, then some thread that is not
`Done` at `i` is `Done` at a later index. -/
def _root_.Kraken.Promising.Live.SpinSem.ProgressFromSem {I : ISA} (A : Arch) (fuel : Nat) (c0 : Config I)
    (Fair : (Nat → Config I) → Prop) (Waiting Done : Nat → Config I → Prop) : Prop :=
  ∀ tr : TraceSem A fuel I, tr.cfg 0 = c0 → Fair tr.cfg →
    ∀ tid i, Waiting tid (tr.cfg i) → ∃ j, i ≤ j ∧ ∃ tid', ¬ Done tid' (tr.cfg i) ∧ Done tid' (tr.cfg j)

/-! ## Basic facts

`withThread_get_self`/`withThread_get_ne` are `SpinStep.wt_tid`/`wt_ne`. -/

theorem withThread_get_self {c : Config I} {tid : Nat} {t t' : Thread I} {mem' : Memory}
    (ht : c.threads[tid]? = some t) : (c.withThread tid t' mem').threads[tid]? = some t' :=
  SpinStep.wt_tid ht

theorem withThread_get_ne {c : Config I} {tid j : Nat} {t t' : Thread I} {mem' : Memory}
    (ht : c.threads[tid]? = some t) (hj : j ≠ tid) :
    (c.withThread tid t' mem').threads[j]? = c.threads[j]? :=
  SpinStep.wt_ne ht hj

/-- **Bounded configurations stay bounded** along semantic steps. -/
theorem _root_.Kraken.Promising.Config.Bnd.semStep {A : Arch} {fuel tid : Nat} {c c' : Config I}
    (hb : c.Bnd) (h : StepSem A fuel tid c c') : c'.Bnd := by
  rcases h with ⟨tj, outs, o, hj, hstep, ho, -, rfl⟩ | ⟨tj, w, hj, -, -, rfl⟩
  · obtain ⟨hb', hl⟩ := stepOne_bnd A hstep ho (hb tid tj hj)
    intro i t' h'
    rw [Config.withThread_get? c _ _ (lt_size_of_get? hj)] at h'
    split at h'
    · cases h'; exact hb'
    · exact (hb i t' h').mono hl
  · have hl : c.mem.last ≤ (c.mem.append w).1.last := by
      rw [Memory.last_append]; exact Nat.le_succ _
    intro i t' h'
    rw [Config.withThread_get? c _ _ (lt_size_of_get? hj)] at h'
    split at h'
    · cases h'; exact ⟨(hb tid tj hj).views.mono hl, (hb tid tj hj).regs.mono hl⟩
    · exact (hb i t' h').mono hl

/-- A halted thread is not certifiable while it has a promise. -/
theorem not_certOkN_of_halted {A : Arch} {tid n : Nat} {t : Thread I} {mem : Memory} (hh : t.halted = true)
    (hp : t.prom ≠ []) : ¬ CertOkN A tid t mem n := by
  rintro ⟨t', mem', h, ht'⟩
  cases h with
  | refl => exact hp ht'
  | step h₁ _ =>
    obtain ⟨outs, o, hs, -, -⟩ := h₁
    simp only [Thread.halted, Option.isNone_iff_eq_none] at hh
    simp [stepOne, hh] at hs

/-- **Nothing is enabled at a final configuration.** -/
theorem not_enabledSem_of_final {A : Arch} {fuel tid : Nat} {c : Config I} (hf : c.final = true) :
    ¬ EnabledSem A fuel tid c := by
  have hh : ∀ t, c.threads[tid]? = some t → t.halted = true := fun t ht => by
    obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp ht
    have := (Array.all_eq_true.mp hf) tid hlt
    simp only [Bool.and_eq_true] at this
    exact this.1
  rintro ⟨c', ⟨t, outs, o, ht, hs, -, -, -⟩ | ⟨t, w, ht, -, hc, -⟩⟩
  · have := hh t ht
    simp only [Thread.halted, Option.isNone_iff_eq_none] at this
    simp [stepOne, this] at hs
  · exact not_certOkN_of_halted (t := promThread t c.mem w) (hh t ht) (by simp) hc

/-! ## Weak fairness for instruction steps -/

/-- A step that is not an instruction step of `tid` leaves `tid` alone or is
a promise of `tid`, whose resulting thread is certifiable. -/
theorem stepSem_cases_tid {A : Arch} {fuel : Nat} {c c' : Config I} {tid j : Nat}
    (h : StepSem A fuel j c c') (hni : ¬ InstrSem A fuel tid c c') :
    c'.threads[tid]? = c.threads[tid]? ∨
      ∃ t, c.threads[tid]? = some t ∧ ∃ t', c'.threads[tid]? = some t' ∧
        t'.prom.length = t.prom.length + 1 ∧ CertOkN A tid t' c'.mem fuel := by
  rcases h with ⟨t, outs, o, ht, hs, ho, hc, rfl⟩ | ⟨t, w, ht, -, hc, rfl⟩
  · by_cases e : j = tid
    · subst e; exact absurd ⟨t, outs, o, ht, hs, ho, hc, rfl⟩ hni
    · exact .inl (withThread_get_ne ht (Ne.symm e))
  · by_cases e : j = tid
    · subst e
      exact .inr ⟨t, ht, _, withThread_get_self ht, by simp, hc⟩
    · exact .inl (withThread_get_ne ht (Ne.symm e))

/-! ## Generic trace facts

ISA- and architecture-generic, instance-free forms of the trace lemmas first
proved in `LiveTicketSem` and `LiveSpinSemCas`, which are now instances. The
trace lemmas live in namespace `TraceSem` (dot notation on a trace), so
opening `Sem` adds no new short name. -/

/-- An infinite pigeonhole (the original of `SpinSemCas.inf_pigeon`):
if at every index from `n` on some `k < M` has `P k`, then some `k < M` has it
infinitely often. -/
theorem infOften_pigeon (P : Nat → Nat → Prop) : ∀ M n, (∀ j, n ≤ j → ∃ k < M, P k j) →
    ∃ k < M, InfOften (P k)
  | 0, n, h => absurd (h n (Nat.le_refl _)) (fun ⟨_, hk, _⟩ => Nat.not_lt_zero _ hk)
  | M + 1, n, h => by
    by_cases hM : InfOften (P M)
    · exact ⟨M, by omega, hM⟩
    obtain ⟨m0, hm0⟩ : ∃ m0, ∀ j, m0 ≤ j → ¬ P M j := Classical.byContradiction fun hc =>
      hM fun m => Classical.byContradiction fun hj => hc ⟨m, fun j h1 h2 => hj ⟨j, h1, h2⟩⟩
    obtain ⟨k, hk, hP⟩ := infOften_pigeon P M (max n m0) fun j hj => by
      obtain ⟨k, hk, hp⟩ := h j (by omega)
      have : k ≠ M := fun e => hm0 j (by omega) (e ▸ hp)
      exact ⟨k, by omega, hp⟩
    exact ⟨k, by omega, hP⟩

/-- A semantic step keeps the number of threads. -/
theorem stepSem_size {A : Arch} {fuel tid : Nat} {c c' : Config I} (h : StepSem A fuel tid c c') :
    c'.threads.size = c.threads.size := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ <;> simp [Config.withThread]

namespace TraceSem

variable {A : Arch} {fuel : Nat} (tr : TraceSem A fuel I)

theorem size_eq : ∀ j, (tr.cfg j).threads.size = (tr.cfg 0).threads.size
  | 0 => rfl
  | j + 1 => by
    rcases tr.step j with ⟨_, hst⟩ | ⟨-, he⟩
    · rw [stepSem_size hst]; exact size_eq j
    · rw [he]; exact size_eq j

theorem step_prefix (i : Nat) : (tr.cfg i).mem.Prefix (tr.cfg (i + 1)).mem := by
  rcases tr.step i with ⟨tid, ⟨t, outs, oc, ht, hs, ho, -, he⟩ | ⟨t, w, ht, -, -, he⟩⟩ | ⟨-, he⟩
  · rw [he]; exact (stepOne_dord _ hs ho).2.2.1
  · rw [he]; exact Memory.Prefix.append _ _
  · rw [he]; exact Memory.Prefix.refl _

theorem prefix_le {i j : Nat} (hij : i ≤ j) : (tr.cfg i).mem.Prefix (tr.cfg j).mem := by
  induction hij with
  | refl => exact Memory.Prefix.refl _
  | @step k _ ih => exact ih.trans (tr.step_prefix k)

theorem get_le {i j : Nat} (hij : i ≤ j) {ts : Time} {w : Msg} (hw : (tr.cfg i).mem.get? ts = some w) :
    (tr.cfg j).mem.get? ts = some w := by
  rw [(tr.prefix_le hij).get? ((tr.cfg i).mem.last_le_of_get?_eq_some hw)]; exact hw

/-- A step leaves thread `T`'s state and views alone and keeps its promises,
or is an instruction step of `T`. -/
theorem same_or_instr (j T : Nat) {u : Thread I} (hu : (tr.cfg j).threads[T]? = some u) :
    (∃ u', (tr.cfg (j + 1)).threads[T]? = some u' ∧ u'.st = u.st ∧ u'.views = u.views ∧
      ∀ ts ∈ u.prom, ts ∈ u'.prom) ∨
    ∃ outs oc, stepOne A u T (tr.cfg j).mem = some outs ∧ .ok oc ∈ outs ∧
      tr.cfg (j + 1) = (tr.cfg j).withThread T oc.thread oc.mem := by
  rcases tr.step j with ⟨tid, ⟨t, outs, oc, ht, hs, ho, -, he⟩ | ⟨t, w, ht, -, -, he⟩⟩ | ⟨-, he⟩
  · by_cases e : tid = T
    · subst e; rw [hu] at ht; cases ht; exact .inr ⟨outs, oc, hs, ho, he⟩
    · exact .inl ⟨u, by rw [he, withThread_get_ne ht (Ne.symm e)]; exact hu, rfl, rfl, fun _ h => h⟩
  · by_cases e : tid = T
    · subst e; rw [hu] at ht; cases ht
      exact .inl ⟨promThread u (tr.cfg j).mem w, by rw [he]; exact withThread_get_self hu, rfl, rfl,
        fun _ h => List.mem_append_left _ h⟩
    · exact .inl ⟨u, by rw [he, withThread_get_ne ht (Ne.symm e)]; exact hu, rfl, rfl, fun _ h => h⟩
  · exact .inl ⟨u, by rw [he]; exact hu, rfl, rfl, fun _ h => h⟩

theorem wt_self {k U : Nat} {t : Thread I} {oc : Outcome I} (ht : (tr.cfg k).threads[U]? = some t)
    (he : tr.cfg (k + 1) = (tr.cfg k).withThread U oc.thread oc.mem) :
    (tr.cfg (k + 1)).threads[U]? = some oc.thread := by
  rw [he]; exact withThread_get_self ht

/-- A thread, once present, stays present. -/
theorem get_persist {U j : Nat} {t : Thread I} (ht : (tr.cfg j).threads[U]? = some t) :
    ∀ k, j ≤ k → ∃ t', (tr.cfg k).threads[U]? = some t' := by
  intro k hk
  induction hk with
  | refl => exact ⟨t, ht⟩
  | @step k _ ih =>
    obtain ⟨t', h'⟩ := ih
    rcases tr.same_or_instr k U h' with ⟨u', hu', -⟩ | ⟨-, oc, -, -, he⟩
    · exact ⟨u', hu'⟩
    · exact ⟨_, tr.wt_self h' he⟩

/-- **`T`'s next instruction step**, when it takes infinitely many: from `j`,
`T`'s state and views are unchanged until some `k` where it takes one. -/
theorem adv {T : Nat} (hinf : InfOften fun k => InstrSem A fuel T (tr.cfg k) (tr.cfg (k + 1))) {j : Nat}
    {u : Thread I} (hu : (tr.cfg j).threads[T]? = some u) :
    ∃ k, j ≤ k ∧ ∃ u', (tr.cfg k).threads[T]? = some u' ∧ u'.st = u.st ∧ u'.views = u.views ∧
      ∃ outs oc, stepOne A u' T (tr.cfg k).mem = some outs ∧ .ok oc ∈ outs ∧
        tr.cfg (k + 1) = (tr.cfg k).withThread T oc.thread oc.mem := by
  obtain ⟨k0, hk0, hs0⟩ := hinf j
  suffices H : ∀ d j (u : Thread I), k0 - j = d → j ≤ k0 → (tr.cfg j).threads[T]? = some u →
      ∃ k, j ≤ k ∧ ∃ u', (tr.cfg k).threads[T]? = some u' ∧ u'.st = u.st ∧ u'.views = u.views ∧
        ∃ outs oc, stepOne A u' T (tr.cfg k).mem = some outs ∧ .ok oc ∈ outs ∧
          tr.cfg (k + 1) = (tr.cfg k).withThread T oc.thread oc.mem from H _ j u rfl hk0 hu
  intro d
  induction d with
  | zero =>
    intro j u hd hj hu
    obtain rfl : j = k0 := by omega
    obtain ⟨t, outs, oc, ht, hs, ho, -, he⟩ := hs0
    rw [hu] at ht; cases ht
    exact ⟨j, Nat.le_refl _, u, hu, rfl, rfl, outs, oc, hs, ho, he⟩
  | succ d ih =>
    intro j u hd hj hu
    rcases tr.same_or_instr j T hu with ⟨u', hu', e1, e2, -⟩ | hi
    · obtain ⟨k, hk, u'', h1, h2, h3, h4⟩ := ih (j + 1) u' (by omega) (by omega) hu'
      exact ⟨k, by omega, u'', h1, h2.trans e1, h3.trans e2, h4⟩
    · exact ⟨j, Nat.le_refl _, u, hu, rfl, rfl, hi⟩

/-- **A thread taking infinitely many steps takes infinitely many instruction
steps**, on a trace that never stutters from `n` on and whose threads drop at
most `B` promises per instruction (a promise step's resulting thread is
certifiable, so it has at most `fuel * B` promises). -/
theorem instr_inf {B S n : Nat} (hd : ∀ i tid t, (tr.cfg i).threads[tid]? = some t → DropBounded A B tid t)
    (hstepj : ∀ j, n ≤ j → ∃ k, StepSem A fuel k (tr.cfg j) (tr.cfg (j + 1)))
    (hinf : InfOften fun j => StepSem A fuel S (tr.cfg j) (tr.cfg (j + 1))) :
    InfOften fun j => InstrSem A fuel S (tr.cfg j) (tr.cfg (j + 1)) := by
  intro m
  apply Classical.byContradiction
  intro hno
  have hno' : ∀ j, max n m ≤ j → ¬ InstrSem A fuel S (tr.cfg j) (tr.cfg (j + 1)) := fun j hj hs =>
    hno ⟨j, by omega, hs⟩
  have hstep : ∀ j, max n m ≤ j →
      promCount tr.cfg S j ≤ promCount tr.cfg S (j + 1) ∧
        (StepSem A fuel S (tr.cfg j) (tr.cfg (j + 1)) → promCount tr.cfg S (j + 1) ≤ fuel * B ∧
          promCount tr.cfg S (j + 1) = promCount tr.cfg S j + 1) := by
    intro j hj
    obtain ⟨k, hk⟩ := hstepj j (by omega)
    rcases stepSem_cases_tid hk (hno' j hj) with heq | ⟨t, ht, t', ht', hlen, hc⟩
    · refine ⟨by rw [promCount, promCount, heq]; exact Nat.le_refl _, fun hs => ?_⟩
      rcases hs with hi | ⟨t, w, ht, -, -, heq'⟩
      · exact absurd hi (hno' j hj)
      · exfalso
        rw [heq', withThread_get_self ht, ht] at heq
        have := congrArg (fun o => Option.map (fun t : Thread I => t.prom.length) o) heq
        simp at this
    · have e1 : promCount tr.cfg S j = t.prom.length := by simp [promCount, ht]
      have e2 : promCount tr.cfg S (j + 1) = t'.prom.length := by simp [promCount, ht']
      rw [e1, e2, hlen]
      exact ⟨Nat.le_succ _, fun _ => ⟨hlen ▸ prom_le_of_certOkN (hd (j + 1) S t' ht') hc, rfl⟩⟩
  have hmono : ∀ j d, max n m ≤ j → promCount tr.cfg S j ≤ promCount tr.cfg S (j + d) := by
    intro j d hj
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ihd => exact Nat.le_trans ihd (hstep (j + d) (by omega)).1
  have hgrow : ∀ k, ∃ j, max n m ≤ j ∧ k ≤ promCount tr.cfg S j := by
    intro k
    induction k with
    | zero => exact ⟨max n m, Nat.le_refl _, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨j, hj, hk⟩ := ih
      obtain ⟨j', hj', hs⟩ := hinf j
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj'
      refine ⟨j + d + 1, by omega, ?_⟩
      have := ((hstep (j + d) (by omega)).2 hs).2
      have := hmono j d hj
      omega
  obtain ⟨j, hj, hk⟩ := hgrow (fuel * B + 1)
  obtain ⟨j', hj', hs⟩ := hinf j
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj'
  have h1 := (hstep (j + d) (by omega)).2 hs
  have := hmono j d hj
  omega

end TraceSem

/-- **Weak fairness gives weak fairness for instruction steps** on a semantic
trace whose threads drop at most `B` promises per instruction (an
instance of `TraceSem.instr_inf`). -/
theorem weakFairInstrSem_of_weakFairSem {A : Arch} {fuel B : Nat} (tr : TraceSem A fuel I)
    (hd : ∀ i tid t, (tr.cfg i).threads[tid]? = some t → DropBounded A B tid t)
    (hf : WeakFairSem A fuel tr.cfg) : WeakFairInstrSem A fuel tr.cfg := by
  intro tid ⟨n, hn⟩
  refine tr.instr_inf hd (n := n) (fun j hj => ?_) (hf tid ⟨n, fun i hi => let ⟨c', h1⟩ := hn i hi; ⟨c', .inl h1⟩⟩)
  rcases tr.step j with h | ⟨hfin, -⟩
  · exact h
  · obtain ⟨c', h1⟩ := hn j hj
    exact absurd ⟨c', .inl h1⟩ (not_enabledSem_of_final hfin)

/-! ## No dead promise -/

/-- **A certifiable thread has no dead promise**: every outstanding promise
lies above the thread's `coh` of its location (`stepOne_dord`: `coh` only
grows, and fulfilment needs the promise above it). -/
theorem coh_lt_of_certOkN {A : Arch} {tid n : Nat} {t : Thread I} {mem : Memory}
    (hc : CertOkN A tid t mem n) {ts : Time} {w : Msg} (hts : ts ∈ t.prom) (hw : mem.get? ts = some w) :
    t.views.getCoh w.loc < ts := by
  obtain ⟨t', mem', h, hp⟩ := hc
  suffices ∀ n p q, ThreadNPn A tid n p q → q.1.prom = [] → ∀ ts w, ts ∈ p.1.prom → p.2.get? ts = some w →
      p.1.views.getCoh w.loc < ts from this n _ _ h hp ts w hts hw
  intro n p q h hq
  induction h with
  | refl n p => intro ts w hts _; rw [hq] at hts; cases hts
  | @step n p q r hs _ ih =>
    intro ts w hts hw
    obtain ⟨outs, o, hstep, ho, rfl⟩ := hs
    obtain ⟨-, hcoh, hpre, hful⟩ := stepOne_dord A hstep ho
    by_cases hin : ts ∈ o.thread.prom
    · have hw' : o.mem.get? ts = some w := by
        rw [hpre.get? (p.2.last_le_of_get?_eq_some hw)]; exact hw
      exact Nat.lt_of_le_of_lt (hcoh _) (ih hq ts w hin hw')
    · exact (hful ts hts hin).2 w hw

/-! ## Generic solo-run facts

Instance-free forms of the solo-run lemmas of `LiveTicketSolo` and
`LiveSpinSemSolo`, which were proved twice only because each file's section
layout instance differs. Those files' `threadNPn_prefix`, `nacert_replay` and
`instrEnabledSem_of` are instances; their `NACert` is `NACertG Arch.armv8`
by unfolding. -/

/-- A solo run only extends memory. -/
theorem _root_.Kraken.Promising.Live.ThreadNPn.mem_prefix {A : Arch} {tid n : Nat} {p q : Thread I × Memory}
    (h : ThreadNPn A tid n p q) : p.2.Prefix q.2 := by
  induction h with
  | refl => exact Memory.Prefix.refl _
  | step hs _ ih =>
    obtain ⟨outs, o, hs, ho, rfl⟩ := hs
    exact (Memory.Prefix.stepOne hs ho).trans ih

/-- A certification without fresh writes, against memory `mem` (the generic
form of `TicketSolo.NACert` / `SpinSemSolo.NACert`). -/
def NACertG (A : Arch) (fuel tid : Nat) (t : Thread I) (mem : Memory) : Prop :=
  ∃ t', ThreadNPn A tid fuel (t, mem) (t', mem) ∧ t'.prom = []

/-- **A certification without fresh writes replays against a larger memory**,
for threads satisfying a step invariant `Inv` under which every
memory-preserving step replays (`hrep`). -/
theorem nacertG_replay {A : Arch} {tid : Nat} (Inv : I.State → Prop)
    (hstep : ∀ {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))} {oc : Outcome I},
      Inv t.st → stepOne A t tid mem = some outs → .ok oc ∈ outs → Inv oc.thread.st)
    (hrep : ∀ {t : Thread I} {mem0 mem : Memory} {outs : List (Except String (Outcome I))} {oc : Outcome I},
      Inv t.st → t.Bnd mem0.last → mem0.Prefix mem → stepOne A t tid mem0 = some outs → .ok oc ∈ outs →
      oc.mem = mem0 →
      ∃ outs' o', stepOne A t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = oc.thread ∧ o'.mem = mem) :
    ∀ {n : Nat} {p q : Thread I × Memory}, ThreadNPn A tid n p q → p.2 = q.2 → Inv p.1.st → p.1.Bnd p.2.last →
      ∀ mem, p.2.Prefix mem → ThreadNPn A tid n (p.1, mem) (q.1, mem) := by
  intro n p q h
  induction h with
  | refl => intro _ _ _ mem _; exact .refl _ _
  | @step n p q r hs h ih =>
    intro he hS hb mem hpm
    obtain ⟨outs, oc, hs', ho, rfl⟩ := hs
    have hm : oc.mem = p.2 := Memory.Prefix.antisymm (he ▸ h.mem_prefix) (Memory.Prefix.stepOne hs' ho)
    obtain ⟨outs', o', hs2, ho2, hth, hmem⟩ := hrep hS hb hpm hs' ho hm
    have hb' := (stepOne_bnd _ hs' ho hb).1
    refine .step ⟨outs', o', hs2, ho2, by rw [hth, hmem]⟩ (ih (hm.trans he) (hstep hS hs' ho) hb' mem ?_)
    show oc.mem.Prefix mem
    rw [hm]; exact hpm

/-- A successful step that leaves no promise is an enabled instruction step. -/
theorem instrEnabledSem_of_step {A : Arch} {fuel tid : Nat} {cfg : Config I} {t : Thread I}
    {outs : List (Except String (Outcome I))} {oc : Outcome I} (ht : cfg.threads[tid]? = some t)
    (h1 : stepOne A t tid cfg.mem = some outs) (h2 : .ok oc ∈ outs) (h3 : oc.thread.prom = []) :
    InstrEnabledSem A fuel tid cfg :=
  ⟨_, t, outs, oc, ht, h1, h2, ⟨_, _, .refl _ _, h3⟩, rfl⟩

/-- **A thread that either has no promise or certifies without fresh writes
can take an instruction step**, if it can when it has no promise (`hnil`). -/
theorem instrEnabledSem_of_nacertG {A : Arch} {fuel tid : Nat} {cfg : Config I} {t : Thread I}
    (ht : cfg.threads[tid]? = some t) (hnil : t.prom = [] → InstrEnabledSem A fuel tid cfg)
    (hn : t.prom = [] ∨ NACertG A fuel tid t cfg.mem) : InstrEnabledSem A fuel tid cfg := by
  rcases hn with hp0 | ⟨t', hr, ht'⟩
  · exact hnil hp0
  · cases hr with
    | refl => exact hnil ht'
    | @step n _ q _ hs h =>
      obtain ⟨outs, oc, hs', ho, rfl⟩ := hs
      exact ⟨_, t, outs, oc, ht, hs', ho, ⟨t', cfg.mem, h.mono (Nat.le_succ n), ht'⟩, rfl⟩

end Kraken.Promising.Live.Sem
