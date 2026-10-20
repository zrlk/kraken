/-
`pf_complete_drf`, sharpened (second prototype): the
statement, the helper lemmas that are already provable, and the proof
outline. The main statement is a `Prop` definition, not proved here.

## What the second round of experiments found

Method: every configuration reachable with promises against every one
reachable promise-free (not only final ones), Toy `#guard_msgs` tests in
`PFCompleteDRFTests.lean`, AArch64 `.kl` runs

1. **The statement survives.** On every program satisfying the hypotheses
   (the AArch64 lock examples as written, Toy lock shapes with acquire-only
   acquisitions, write-only critical sections, publication, write-after-read
   guarded by an acquire or only by a control dependency, a ping-pong, an
   RMW in the critical section) every promise-free configuration reachable with promises is `≈`
   to one reachable promise-free, intermediate ones included. A random search
   over 800 small Toy programs (386 satisfying the hypotheses) found no
   counterexample.
2. **Each hypothesis does work.** Racy variants (`mpRacy`, load buffering
   through a flag, 2+2W) and unordered ones (a plain flag store, the relaxed
   spinlock's plain release) break `≈`.
3. **The write clause is needed**: 2+2W on data locations has no reads, so a
   reads-only hypothesis holds, yet `≈` fails.
4. **Configuration-level, not happens-before, DRF**: a write-after-read
   guarded only by a control dependency (no acquire) is racy in the
   happens-before sense but satisfies the hypothesis and `≈`.
5. **Split by location**, not by access: a test-and-test-and-set spin's plain
   read of the lock is a racy read of a *synchronisation* location and must
   stay allowed; a by-access split would call it a data race.
6. **Outcome form** (`DataRaceFreeSteps`, below) rather than
   `DataRaceFreePF`: it constrains the events an instruction performs (a read
   must be determinate, whatever made its bound large enough), not a
   syntactic over-approximation of the locations it may touch.
7. **`RunOrderedOff` must stay a property of the promising machine**: its
   promise-free reading (constraining view of every synchronisation write
   `≥` frontier, in promise-free runs) holds for a plain flag store whose
   preceding read only ever sees the initial value without promises, and `≈`
   fails there. So it comes from a shape check (`shape_sound` with location
   classes), not from the Stage 2 logic.
8. **`≈` is enough for §5.3, on promise-free configurations only**: final
   values (`Config.Equiv.finalVal`) and thread states (`Config.Equiv.state`)
   transfer (`PFCompleteEquiv.invariant`). Mutual exclusion read off program
   counters is **false** over all `Reachable` configurations, even for
   acquire-release locks and under TSO: the holder's release can be promised
   and read by the next acquirer before the holder executes it. Every such
   configuration has an outstanding promise.
9. **Side condition: no `DSB ST` after a data store.** The argument below
   uses that data timestamps never reach a read bound. `readSuccs` raises
   `vrOld` only (`vrOldNR` for a `noRet` read, herd's `NoRet` atomics; it is
   part of the frontier, folded by `fence .sy` and release writes like
   `vrOld`, and not by `fence .stAll`, so this item is unchanged) and stores
   raise `vwOld` (Pulte et al.; until reads
   raised `vwOld` too, which made `DMB ST` order earlier reads before later
   writes, unlike herd: LB+dmb.st+dmb.st). So a plain data store promised
   below the frontier leaves `vwOld` lower than the promise-free run would,
   where the store takes the newest timestamp, and `fence .stAll` (`DSB ST`:
   `vrNew ⊔= vwOld`) then lets a later read see that difference. Explorer
   (Toy, `T0: LDR z; STR d; DSB ST; LDR y ∥ T1: STLR y; STLR z`, `data =
   {d}`): `RunOrderedOff` and `DataRaceFreeSteps` hold, and the outcome
   `z = 1, y = 0` is reachable with promises only (one promise-free final
   configuration with no `≈` counterpart). herd allows it too
   (`corpus/aarch64-views/DSBST-leak.litmus`), so the model is right and the
   theorem is false without the side condition. With `DMB ST` or `DMB SY` in
   place of `DSB ST` `≈` holds. `pf_complete_drf_steps` below is stated
   without the side condition, and no such hypothesis may be added: the
   development must not restrict source programs (the same principle rules out
   `RunOrderedOff` and DRF as
   foundations). The theorem is therefore false as a foundation for Stage 2
   and is kept as a tool only. `DMB ST` is believed not to need it:
   it raises only `vwNew`, which bounds writes, not reads, and the
   synchronisation writes it could lower are ordered anyway.

## Proof outline for `pf_complete_drf_steps` (on top of `pf_complete_ordered`)

A write is *ordered* if its timestamp exceeds the writer's frontier, else
*delayed* (possible for data writes only, by `RunOrderedOff`). The source run
is the target's instructions sorted by key, as in `pf_complete_ordered`;
delayed writes do not advance the frontier, so they slot in at the writer's
current key and get a fresh timestamp at the end of the source memory.

| Lemma | Statement | Rating |
|---|---|---|
| `frontier_dominates`, `views_le_last`, `run_trace` | as for `pf_complete_ordered` | routine |
| `key_mono_drf` | key = frontier after the instruction; monotone in program order; equal to the timestamp at an ordered write; unchanged at a delayed write | easy |
| `data_read_neutral` | under the read clause a data read raises no view above the frontier (`νpost ≤ max νpre (coh l)`) | routine |
| `delayed_write_neutral` | a delayed write changes only `coh l`, `fwdb l` and `vwOld` (still `≤` frontier) | easy (uses item 9) |
| `sim_step` | invariant `SimDRF`: equal thread states; equal histories of the scheduled writes; per thread, views agree on non-data messages up to a monotone renaming of synchronisation timestamps; then the source takes the same outcome whenever the target's data reads read the source's last write | hard |
| `early_read_race` | if the target reads a data message that the schedule has not produced yet (an unfulfilled promise, a delayed write with a later key) or a stale one, some configuration reachable promise-free violates `DataRaceFreeSteps` | **unknown** |
| `schedule_drf` | the order (key; the ordered write of that key, then delayed writes, then the rest; program order) linearises program order, reads-from and coherence on synchronisation locations | hard (the `schedule` of `pf_complete_ordered` plus delayed writes) |
| assembly | `pf_complete_drf_steps` from the above | routine |

Where the hypotheses are used:
- `RunOrderedOff`: synchronisation writes keep their relative positions, so
  views rename monotonically (`sim_step`); and in `early_read_race` it blocks
  dependency cycles: a reader that passes a value back to the writer through a
  synchronisation write `s` forces `ts w > ts s > ts w`.
- Read clause: `sim_step` (the source read is determinate) and
  `data_read_neutral`.
- Write clause: data histories, `sim_step` (2+2W).
- *Run-level* data-race freedom is not needed, but `early_read_race` needs
  the hypothesis on configurations **off** the simulated run: the witness is
  a promise-free run in which the writer runs ahead to its write (as its
  certification shows it can) before the reader reads. This is why the
  hypothesis quantifies over every promise-free reachable configuration.

Why `early_read_race` is believed true: no counterexample in the explorer;
the dependency-cycle argument above leaves only writers whose path to the
write does not depend on what the reader does next, and certification
gives such a path; Cho et al. (PLDI'21) prove the analogous LDRF-PF for PS2.1
with this race-exhibition shape. What does not carry over: PS has
per-location timestamps, so delaying a promise there moves it within one
location's timeline only; here the renaming of the global order is the new
part (`sim_step`). PS2.0's failure (relaxed RMW–store reordering) has an ARM
analogue, a plain store promised before an acquire-only RMW's write, which
is exactly the lock pattern here; the explorer finds no failure for it.
-/
import Kraken.Promising.PFComplete

namespace Kraken.Promising

variable {I : ISA}

/-! ## Final values are determined by `≈` -/

/-- The final value of a location is the value of the last message of its
history, else the initial value. -/
theorem Memory.finalVal_eq_history (m : Memory) (l : Loc) :
    m.finalVal l = (((m.history l).getLast?).map (·.val)).getD (m.initVal l) := by
  have h : m.msgs.findRev? (·.loc == l) = (m.history l).getLast? := by
    rw [Array.findRev?_eq_find?_reverse, ← Array.find?_toList, Array.toList_reverse, ← List.head?_filter,
      List.filter_reverse, List.head?_reverse]
    rfl
  unfold Memory.finalVal
  rw [h]
  cases (m.history l).getLast? <;> rfl

/-- `≈` configurations have the same final value at every location (the
counter values of §5.3). -/
theorem Config.Equiv.finalVal {c c' : Config I} (h : c.Equiv c') (l : Loc) :
    c.mem.finalVal l = c'.mem.finalVal l := by
  rw [Memory.finalVal_eq_history, Memory.finalVal_eq_history, h.history l]
  unfold Memory.initVal
  rw [h.init]

/-- `≈` configurations have the same thread states, position by position
(mutual exclusion, read off the program counters, is a property of these). -/
theorem Config.Equiv.state {c c' : Config I} (h : c.Equiv c') (i : Nat) :
    (c.threads[i]?).map (·.st) = (c'.threads[i]?).map (·.st) := by
  have := congrArg (·[i]?) h.states
  simpa [Array.getElem?_toList] using this

/-! ## The sharpened data-race-freedom hypothesis -/

/-- **Data-race freedom on the `data` locations, outcome form**: in every
configuration reachable promise-free from `c`, every outcome of every
thread's next instruction

- reads a data location only at its last write (the thread cannot read a
  stale value: its read bound covers the last write), and
- writes a data location only if the thread has seen its last write
  (`lastWrite l ≤ max (coh l) vrNew`: by an earlier access to `l`, or made
  visible by an acquire or a barrier).

The read clause is exactly "the read is determinate", whatever made the
bound large enough (`vrNew`, an address dependency, `vRel` for an acquire
after a release); the write clause is the write clause of `DataRaceFreePF`.
Unlike `DataRaceFreePF` it looks at the events the instruction performs,
not at a syntactic over-approximation of the locations it may touch, so a
racy read of a *synchronisation* location (a test-and-test-and-set spin) is
never mistaken for a data access. -/
def DataRaceFreeSteps (A : Arch) (fuel : Nat) (data : Loc → Prop) (c : Config I) : Prop :=
  ∀ c', ReachablePF A fuel c c' →
  ∀ (tid : Nat) (t : Thread I) (outs : List (Except String (Outcome I))) (o : Outcome I),
    c'.threads[tid]? = some t → stepThread A c' tid = some outs → .ok o ∈ outs →
      (∀ l ts v ν, TraceEv.read l ts v ν ∈ o.log → data l → ts = c'.mem.lastWrite l) ∧
      (∀ l ts v f, TraceEv.write l ts v f ∈ o.log → data l →
        c'.mem.lastWrite l ≤ max (t.views.getCoh l) t.views.vrNew)

/-- **The sharpened target** for the AArch64 lock examples as written: writes
to synchronisation locations (outside `data`) ordered, data accesses
race-free in the outcome sense over promise-free runs; conclusion: every
promise-free configuration reachable with promises is `≈` to one reachable
without. Rated *go with risk* (outline in the header). -/
def pf_complete_drf_steps (A : Arch) (fuel : Nat) : Prop :=
  ∀ (data : Loc → Prop), PFCompleteEquiv (I := I) A fuel fun c =>
    c.Initial ∧ RunOrderedOff A fuel data c ∧ DataRaceFreeSteps A fuel data c

/-! ## Monotonicity and the degenerate cases -/

theorem PFCompleteEquiv.mono {A : Arch} {fuel : Nat} {P Q : Config I → Prop}
    (h : PFCompleteEquiv A fuel P) (hQP : ∀ c, Q c → P c) : PFCompleteEquiv A fuel Q :=
  fun c c' hQ hr hpf => h c c' (hQP c hQ) hr hpf

/-- More data locations: fewer writes must be ordered. -/
theorem RunOrderedOff.mono {A : Arch} {fuel : Nat} {data data' : Loc → Prop} {c : Config I}
    (h : RunOrderedOff A fuel data c) (hd : ∀ l, data l → data' l) : RunOrderedOff A fuel data' c :=
  fun c' hr tid t outs o ht hs ho l ts v f hw hnd => h c' hr tid t outs o ht hs ho l ts v f hw (fun hl => hnd (hd l hl))

/-- Write-ordered runs are ordered off any set of data locations. -/
theorem RunOrdered.runOrderedOff {A : Arch} {fuel : Nat} {c : Config I} (h : RunOrdered A fuel c)
    (data : Loc → Prop) : RunOrderedOff A fuel data c :=
  fun c' hr tid t outs o ht hs ho l ts v f hw _ => (h c' hr tid t outs o ht hs ho).2 l ts v f hw

/-- Fewer data locations: fewer accesses must be race-free. -/
theorem DataRaceFreeSteps.anti {A : Arch} {fuel : Nat} {data data' : Loc → Prop} {c : Config I}
    (h : DataRaceFreeSteps A fuel data c) (hd : ∀ l, data' l → data l) : DataRaceFreeSteps A fuel data' c :=
  fun c' hr tid t outs o ht hs ho =>
    let h := h c' hr tid t outs o ht hs ho
    ⟨fun l ts v ν hr' hl => h.1 l ts v ν hr' (hd l hl), fun l ts v f hw hl => h.2 l ts v f hw (hd l hl)⟩

theorem DataRaceFreePF.anti {A : Arch} {fuel : Nat} {data data' : Loc → Prop} {c : Config I}
    (h : DataRaceFreePF A fuel data c) (hd : ∀ l, data' l → data l) : DataRaceFreePF A fuel data' c :=
  fun c' hr t ht tree l hex hl hacc => h c' hr t ht tree l hex (hd l hl) hacc

/-- With no data locations the hypothesis is vacuous. -/
theorem DataRaceFreeSteps.none (A : Arch) (fuel : Nat) (c : Config I) :
    DataRaceFreeSteps A fuel (fun _ => False) c :=
  fun _ _ _ _ _ _ _ _ _ => ⟨fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim⟩

/-- `pf_complete_drf_steps` at `data := ∅`: the `≈` form for runs whose writes
are all above the frontier (no bound on writes per instruction, unlike
`RunOrdered`). -/
theorem pf_complete_drf_steps.ordered {A : Arch} {fuel : Nat} (h : pf_complete_drf_steps (I := I) A fuel) :
    PFCompleteEquiv (I := I) A fuel fun c => c.Initial ∧ RunOrderedOff A fuel (fun _ => False) c :=
  (h fun _ => False).mono fun c ⟨hi, ho⟩ => ⟨hi, ho, DataRaceFreeSteps.none A fuel c⟩

/-! ## Using the conclusion: invariants of promise-free configurations -/

/-- How §5.3 consumes a `≈` normal form: a property preserved by `≈`
(mutual exclusion read off thread states; final counter values, by
`Config.Equiv.finalVal`) that holds on every configuration reachable
promise-free holds on every *promise-free* configuration reachable with
promises. It does **not** extend to configurations with outstanding
promises: there, two threads can both be past their acquisition (the
holder's release `STLR` promised and read by the next acquirer before the
holder executes it; `PFCompleteDRFTests.lean`), so mutual exclusion must be
stated on promise-free configurations. -/
theorem PFCompleteEquiv.invariant {A : Arch} {fuel : Nat} {P : Config I → Prop} {Q : Config I → Prop}
    (h : PFCompleteEquiv A fuel P) (hQ : ∀ c c', c.Equiv c' → Q c → Q c') {c : Config I} (hP : P c)
    (hinv : ∀ c', ReachablePF A fuel c c' → Q c') :
    ∀ c', Reachable A fuel c c' → c'.PromFree → Q c' := by
  intro c' hr hpf
  obtain ⟨c'', hr'', heq⟩ := h c c' hP hr hpf
  exact hQ c'' c' heq (hinv c'' hr'')

end Kraken.Promising
