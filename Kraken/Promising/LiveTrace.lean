/-
**Stage 3 liveness: traces, scheduler fairness and
memory fairness** over the existing machine (`succs`, `Machine.lean`).
Nothing here changes the machine; every definition is new.

- `InstrBy`/`PromiseBy`/`StepBy`: a machine step *of thread `tid`*: an
  instruction step or a certified promise of `tid`, and a member of `succs`
  (`stepBy_of_mem_succs`: every successor is a step of some thread).
- `Trace` (every step a member of `succs`) and `TraceS` (also lets a final
  configuration stutter, so that terminating runs are traces too).
- `Enabled`/`ScheduledAt` (any step of the thread, promise steps included)
  and `InstrEnabled`/`InstrScheduledAt` (instruction steps only).
- `WeakFair`: a thread enabled from some point on is scheduled infinitely
  often; `WeakFairInstr`, the same for instruction steps.
- `ReadsAt`, `MemFair`: a thread that reads a location infinitely often
  eventually has every message of that location in its coherence view
  (memory fairness, Lahav et al., OOPSLA 2021).
- Temporal operators on index predicates: `InfOften`, `EvAlways`.

"Scheduled" is existential: step `i` schedules `tid` if `cfg (i+1)` is a
step of `tid` from `cfg i`. A promise step of `tid` schedules `tid`
(`WeakFair`); `WeakFairInstr` asks for instruction steps.
-/
import Kraken.Promising.PromiseSafe

namespace Kraken.Promising.Live

variable {I : ISA}

/-! ## Steps of one thread -/

/-- An instruction step of thread `tid` from `c` to `c'` (some successful
outcome of its next instruction). -/
def InstrBy (A : Arch) (tid : Nat) (c c' : Config I) : Prop :=
  ∃ t outs o, c.threads[tid]? = some t ∧ stepOne A t tid c.mem = some outs ∧ .ok o ∈ outs ∧
    c' = c.withThread tid o.thread o.mem

/-- A promise step of thread `tid` from `c` to `c'`: a write `tid` performs on
some promise-free run alone (`CertWrite`), appended and promised. -/
def PromiseBy (A : Arch) (tid : Nat) (c c' : Config I) : Prop :=
  ∃ t p, c.threads[tid]? = some t ∧ CertWrite A tid t c.mem p ∧
    c' = c.withThread tid { t with prom := t.prom ++ [(c.mem.append { p.1 with tid }).2] }
      (c.mem.append { p.1 with tid }).1

/-- A promise step leaves its thread with an outstanding promise (the
ISA-generic original of `TicketCex.promiseBy_prom` and
`TicketX64Cex.promiseBy_prom`). -/
theorem PromiseBy.prom_ne {A : Arch} {tid : Nat} {c c' : Config I} (h : PromiseBy A tid c c') :
    ∃ t', c'.threads[tid]? = some t' ∧ t'.prom ≠ [] := by
  obtain ⟨t, p, ht, -, rfl⟩ := h
  exact ⟨{ t with prom := t.prom ++ [(c.mem.append { p.1 with tid }).2] },
    by simp [Config.withThread, (Array.getElem?_eq_some_iff.mp ht).1], by simp⟩

/-- **A machine step of thread `tid`**: a member of `succs` that is an
instruction step or a promise step of `tid`. -/
def StepBy (A : Arch) (fuel tid : Nat) (c c' : Config I) : Prop :=
  c' ∈ (succs A c fuel).1 ∧ (InstrBy A tid c c' ∨ PromiseBy A tid c c')

/-- **Every successor is a step of some thread.** -/
theorem stepBy_of_mem_succs {A : Arch} [I.LawfulState] {fuel : Nat} {c c' : Config I}
    (h : c' ∈ (succs A c fuel).1) : ∃ tid, StepBy A fuel tid c c' := by
  cases succs_cases h with
  | instr ht hs ho => exact ⟨_, h, .inl ⟨_, _, _, ht, hs, ho, rfl⟩⟩
  | promise ht hw => exact ⟨_, h, .inr ⟨_, _, ht, hw, rfl⟩⟩

/-- Thread `tid` can take some machine step at `c`. -/
def Enabled (A : Arch) (fuel tid : Nat) (c : Config I) : Prop :=
  ∃ c', StepBy A fuel tid c c'

/-- Thread `tid` can take an instruction step at `c`. -/
def InstrEnabled (A : Arch) (fuel tid : Nat) (c : Config I) : Prop :=
  ∃ c', c' ∈ (succs A c fuel).1 ∧ InstrBy A tid c c'

/-- A halted thread takes no instruction step. -/
theorem not_instrBy_of_halted {A : Arch} {tid : Nat} {c c' : Config I} {t : Thread I}
    (ht : c.threads[tid]? = some t) (hh : t.halted = true) : ¬ InstrBy A tid c c' := by
  rintro ⟨t', outs, o, ht', hs, -, -⟩
  rw [ht] at ht'; cases ht'
  simp only [Thread.halted, Option.isNone_iff_eq_none] at hh
  simp [stepOne, hh] at hs

/-- A halted thread makes no promise. -/
theorem not_promiseBy_of_halted {A : Arch} {tid : Nat} {c c' : Config I} {t : Thread I}
    (ht : c.threads[tid]? = some t) (hh : t.halted = true) : ¬ PromiseBy A tid c c' := by
  rintro ⟨t', p, ht', ⟨t1, mem1, outs, o, hnp, hs, -, -⟩, -⟩
  rw [ht] at ht'; cases ht'
  simp only [Thread.halted, Option.isNone_iff_eq_none] at hh
  cases hnp with
  | refl => simp [stepOne, hh] at hs
  | step h₁ _ =>
    obtain ⟨outs', o', hs', -, -⟩ := h₁
    simp [stepOne, hh] at hs'

/-- **A halted thread is not enabled.** -/
theorem not_enabled_of_halted {A : Arch} {fuel tid : Nat} {c : Config I} {t : Thread I}
    (ht : c.threads[tid]? = some t) (hh : t.halted = true) : ¬ Enabled A fuel tid c := by
  rintro ⟨c', -, h | h⟩
  · exact not_instrBy_of_halted ht hh h
  · exact not_promiseBy_of_halted ht hh h

/-- A thread id out of range is not enabled. -/
theorem not_enabled_of_none {A : Arch} {fuel tid : Nat} {c : Config I}
    (ht : c.threads[tid]? = none) : ¬ Enabled A fuel tid c := by
  rintro ⟨c', -, ⟨t, -, -, h, -⟩ | ⟨t, -, h, -⟩⟩ <;> simp [ht] at h

/-- At a final configuration no thread is enabled. -/
theorem not_enabled_of_final {A : Arch} {fuel tid : Nat} {c : Config I} (hf : c.final = true) :
    ¬ Enabled A fuel tid c := by
  cases ht : c.threads[tid]? with
  | none => exact not_enabled_of_none ht
  | some t =>
    refine not_enabled_of_halted ht ?_
    obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp ht
    have := (Array.all_eq_true.mp hf) tid hlt
    simp only [Bool.and_eq_true] at this
    exact this.1

/-! ## Traces -/

/-- **A trace**: an infinite run of the machine, every step a member of
`succs`. -/
structure Trace (A : Arch) (fuel : Nat) (I : ISA) where
  cfg : Nat → Config I
  step : ∀ i, cfg (i + 1) ∈ (succs A (cfg i) fuel).1

/-- **A trace that may stutter at a final configuration**: every step is a
member of `succs` or repeats a final configuration. A terminating run,
followed by its final configuration forever, is such a trace. -/
structure TraceS (A : Arch) (fuel : Nat) (I : ISA) where
  cfg : Nat → Config I
  step : ∀ i, cfg (i + 1) ∈ (succs A (cfg i) fuel).1 ∨ ((cfg i).final = true ∧ cfg (i + 1) = cfg i)

/-- A trace is a stuttering trace. -/
def Trace.toS {A : Arch} {fuel : Nat} (tr : Trace A fuel I) : TraceS A fuel I :=
  ⟨tr.cfg, fun i => .inl (tr.step i)⟩

/-! ## Temporal operators on index predicates -/

/-- `p` holds at infinitely many indices. -/
def InfOften (p : Nat → Prop) : Prop := ∀ n, ∃ i, n ≤ i ∧ p i

/-- `p` holds at every index from some point on. -/
def EvAlways (p : Nat → Prop) : Prop := ∃ n, ∀ i, n ≤ i → p i

/-! ## Scheduler fairness -/

/-- Step `i` of `cfg` is a step of thread `tid` (any kind). -/
def ScheduledAt (A : Arch) (fuel : Nat) (cfg : Nat → Config I) (tid i : Nat) : Prop :=
  StepBy A fuel tid (cfg i) (cfg (i + 1))

/-- Step `i` of `cfg` is an instruction step of thread `tid`. -/
def InstrScheduledAt (A : Arch) (fuel : Nat) (cfg : Nat → Config I) (tid i : Nat) : Prop :=
  cfg (i + 1) ∈ (succs A (cfg i) fuel).1 ∧ InstrBy A tid (cfg i) (cfg (i + 1))

/-- **Weak (scheduler) fairness**: every thread that is enabled at every
configuration from some point on takes a step infinitely often. A promise
step counts as a step of its thread. -/
def WeakFair (A : Arch) (fuel : Nat) (cfg : Nat → Config I) : Prop :=
  ∀ tid, EvAlways (fun i => Enabled A fuel tid (cfg i)) → InfOften (ScheduledAt A fuel cfg tid)

/-- **Weak fairness for instruction steps**: every thread that can take an
instruction step from some point on takes one infinitely often (promise
steps do not count). -/
def WeakFairInstr (A : Arch) (fuel : Nat) (cfg : Nat → Config I) : Prop :=
  ∀ tid, EvAlways (fun i => InstrEnabled A fuel tid (cfg i)) → InfOften (InstrScheduledAt A fuel cfg tid)

/-- No step of `cfg` is a promise step. -/
def PromiseFree (A : Arch) (cfg : Nat → Config I) : Prop :=
  ∀ i tid, ¬ PromiseBy A tid (cfg i) (cfg (i + 1))

/-! ## Memory fairness -/

/-- Step `i` of `cfg` is an instruction step of thread `tid` that reads
location `l` from the message at `ts`. -/
def ReadsAt (A : Arch) (cfg : Nat → Config I) (tid : Nat) (l : Loc) (ts i : Nat) : Prop :=
  ∃ t outs o, (cfg i).threads[tid]? = some t ∧ stepOne A t tid (cfg i).mem = some outs ∧ .ok o ∈ outs ∧
    cfg (i + 1) = (cfg i).withThread tid o.thread o.mem ∧ ∃ v ν, TraceEv.read l ts v ν ∈ o.log

/-- **Memory fairness**: if thread `tid` reads location `l` infinitely often,
then every message to `l` in memory at some index is eventually in `tid`'s
coherence view of `l` (`ts ≤ coh l`). After that point `tid` cannot read
a message of `l` older than it: on this machine, timestamps are natural
numbers (`mo` is prefix-finite), and this is the per-thread form of the
prefix-finiteness of `fr`. AArch64 hardware basis:
Arm ARM (DDI 0487) B2.7.1 "Normal memory": "A write to a memory location with the Normal attribute completes in finite time" (verbatim in issues C.a and G.a; C.a adds that it "is globally observed for the shareability domain … in finite time", a sentence removed in later issues with the axiomatic memory model). x86: no SDM sentence guarantees eventual visibility (checked: Intel SDM Vol. 3A, order no. 253668-090US, Feb 2026); `MemFair` is a modelling assumption (store buffers drain in finite time, as in x86-TSO). Qualitative support, same revision: §14.10 "Store Buffer" (§11.10 in older revisions): processors "temporarily store each write (store) to memory in a store buffer" and "the existence of the store buffer is transparent to software, even in systems that use multiple processors"; it lists only the events that always drain the buffer (exceptions/interrupts, serializing and I/O instructions, LOCK, BINIT, SFENCE, MFENCE), not a finite-time bound. §11.2.3.5: a store is "temporarily held in a processor's store buffer". -/
def MemFair (A : Arch) (cfg : Nat → Config I) : Prop :=
  ∀ tid l, InfOften (fun i => ∃ ts, ReadsAt A cfg tid l ts i) →
    ∀ i ts w, (cfg i).mem.get? ts = some w → w.loc = l →
      ∃ j, i ≤ j ∧ ∃ t, (cfg j).threads[tid]? = some t ∧ ts ≤ t.views.getCoh l

/-! ## The shape of a liveness statement -/

/-- **Liveness from `c0` under a fairness hypothesis `Fair`**: on every
(stuttering) trace from `c0` satisfying `Fair`, every thread that is
`Waiting` at some index is `Done` at some later index. -/
def LiveFrom (A : Arch) (fuel : Nat) (c0 : Config I) (Fair : (Nat → Config I) → Prop)
    (Waiting Done : Nat → Config I → Prop) : Prop :=
  ∀ tr : TraceS A fuel I, tr.cfg 0 = c0 → Fair tr.cfg →
    ∀ tid i, Waiting tid (tr.cfg i) → ∃ j, i ≤ j ∧ Done tid (tr.cfg j)

/-- **Deadlock-freedom from `c0` under `Fair`**: on every (stuttering) trace
from `c0` satisfying `Fair`, if a thread is `Waiting` at index `i`, then some
thread that is not `Done` at `i` is `Done` at a later index. (Moved here
from `LiveSpin.lean`, an AArch64 file,; same full name.
`SpinX64Step.ProgressFromN` is this definition.) -/
def Spin.ProgressFrom {I : ISA} (A : Arch) (fuel : Nat) (c0 : Config I) (Fair : (Nat → Config I) → Prop)
    (Waiting Done : Nat → Config I → Prop) : Prop :=
  ∀ tr : TraceS A fuel I, tr.cfg 0 = c0 → Fair tr.cfg →
    ∀ tid i, Waiting tid (tr.cfg i) → ∃ j, i ≤ j ∧ ∃ tid', ¬ Done tid' (tr.cfg i) ∧ Done tid' (tr.cfg j)

end Kraken.Promising.Live
