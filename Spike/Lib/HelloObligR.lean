/-
**wake.w's skeleton with the run invariant at the worker's steps** (C4,
option (B)). A twin of `Spike.Lib.WakeA64`'s obligations and
main theorem, verbatim apart from one premise: `WakeObligationsR.post_step1`
also takes the run invariant `WakeRunInv.RunInv Λ E t` at the step's source
configuration (the worker's private keys, `DmemPriv`, for its `write`'s
byte reads). `wake_stepSim` carries `RunInv` in its relation (`Rx`) already;
`wake_stepPostR` passes it on. `WakeA64` itself is untouched (frozen).

- `WakeObligationsR`: `WakeObligations` with the extra `post_step1` premise.
- `WakeObligations.toR`: every `WakeObligations` gives a `WakeObligationsR`
  (drop the premise).
- `wake_stepPreR`, `wake_stepPostR`, `wake_stepSimR`, `wake_tiRunR`: copies
  of `wake_stepPre` … `wake_tiRun` (`Rx`, `Rx.rw` are `WakeA64`'s).
- `hello_correct_atR`: `Correct` at one entry state `E` from `WakeObligationsR … Q E Ti p`.
- `hello_correctE_R`: `wake_correctE` from `WakeObligationsR` (`hello_correct_atR` at
  each admissible `E`); its conclusion is `wake_correctE`'s, token for token.
-/
import Spike.Lib.WakeA64

namespace Spike.Lib.WakeA64

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.TwoSlot Spike.Lib.Handover Spike.Lib.Inv2Core Spike.Lib.HelloProt Spike.Lib.Inv2Read
open Spike.Lib.Inv2Start Spike.Lib.A64TwoSlot Spike.Lib.WakeT1

/-- **The obligations of 1.6** at entry state `E`; each field names its owner.
`μ` is the loaded program's marks (`(target (kernel 2) E).marks asm Λ`, the
same at one slot, `marks_two`). The source machine is `srcS p arch`; `p`
defaults to wake.w's `wakeSrc` (so `srcS p arch` is `wakeS arch`). -/
structure WakeObligationsR (arch : WeakMem.Arch) (Λ : Scc.Sem.Layout) (B : Budget) (asm : String) (Q : WakeRel)
    (E : Entry) (Ti : Cfg → List Ev → Prop) (p : CoreTerm.Prog := wakeSrc) : Prop where
  /-- The layout is well formed. -/
  hwf : Λ.WF
  /-- (hello1's one-thread consumer) The program loads at one slot. -/
  hstart : ∃ d, (target (kernel 1) E).load asm Λ = some d
  /-- (hello1's one-thread consumer) The one-slot load is related by `R1`
  to the source start (`wake_start`: `tidStartT 2`). -/
  pre_init : ∀ d, (target (kernel 1) E).load asm Λ = some d → ∃ s0, (srcS p arch).init s0 ∧ Q.R1 d s0
  /-- (main's rows before the spawn) A step of the one-slot
  configuration keeps `R1` and the slot count, with a matching source run. -/
  pre_step : ∀ tid d es d' s, Q.R1 d s → d.1.threads.size = d.2.slots.size →
    (machine (kernel 1)).Step ((target (kernel 2) E).marks asm Λ) tid d es d' →
    ∃ s', (srcS p arch).Run s (obs es) s' ∧ Q.R1 d' s' ∧ d'.1.threads.size = d'.2.slots.size
  /-- (the spawn/stub rows + the `own` split / `PhRec2` / `TakePath2`; `post_start`
  assembles `Inv2` from the parts) The `clone` into slot 1 is the source
  `spawn`: a source run with no observable event to `Post` after `afterClone`. -/
  spawn : ∀ tid d s th stack tls r, Q.R1 d s → d.1.threads.size = d.2.slots.size →
    d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
    callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
    CertAfter abi Arch.armv8 ((target (kernel 2) E).marks asm Λ) tid (afterClone abi d tid th stack tls r) →
    ∃ s', (srcS p arch).Run s [] s' ∧ Q.Post Λ (afterClone abi d tid th stack tls r) s'
  /-- (main's target/source rows after the spawn, using `wake_ldSt`;
  park as a stutter; the rely of thread 0 under the worker's writes) A step of
  main keeps `Post`. -/
  post_step0 : ∀ t es t' s, Q.Post Λ t s → (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) 0 t es t' →
    ∃ s', (srcS p arch).Run s (obs es) s' ∧ Q.Post Λ t' s'
  /-- (the worker's target rows and source steps; the rely of
  thread 1) A step of the worker other than its unpark and exit rows keeps
  `Post`. -/
  post_step1 : ∀ t es t' s, Q.Post Λ t s → WakeRunInv.RunInv Λ E t → ¬ Q.atUnpk t s → ¬ Q.atTexit t s →
    (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) 1 t es t' →
    ∃ s', (srcS p arch).Run s (obs es) s' ∧ Q.Post Λ t' s'
  /-- (with) **The source unpark**: the worker's `swpal(1)` on
  main's permit word `⟨B + 16, 8⟩` commits the source worker's
  `ext unpark` (and it is committed nowhere else: main's park is never a
  commit point), keeping `Post`. -/
  unpark_src : ∀ t es t' s, Q.Post Λ t s → Q.atUnpk t s →
    (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) 1 t es t' →
    ∃ s', (srcS p arch).Run s (obs es) s' ∧ Q.Post Λ t' s'
  /-- (with) **The worker's exit**: `thr_worker`'s exit `svc`
  (the `texit` row) leaves the source worker at `ret`, keeping `Post`. -/
  worker_done : ∀ t es t' s, Q.Post Λ t s → Q.atTexit t s →
    (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) 1 t es t' →
    ∃ s', (srcS p arch).Run s (obs es) s' ∧ Q.Post Λ t' s'
  /-- Progress and layout before the spawn, of the lifted
  configuration: at main's `clone` the one-slot configuration faults (no
  dormant slot, `faultAt`) while the lifted one steps, so this is not a
  one-slot statement (`Spike.Lib.WakePre.Pre1.pre_progress` reduces it to
  one slot off the `clone`, `progress_up`). -/
  pre_progress : ∀ d u s, Q.R1 d s → Inert u → (∀ a, privLoad u.st a = none) →
    d.1.threads.size = d.2.slots.size →
    (machine (kernel 2)).Progress ((target (kernel 2) E).marks asm Λ) (up d u) ∧
      InLayout (M := machine (kernel 2)) Λ (up d u)
  /-- (`WakeProgress.post_progress_of`) Progress and layout after the
  spawn, under the run invariant (`WakeRunInv.RunInv`) and the certification
  invariant (`CertAll`). -/
  post_progress : ∀ t s, Q.Post Λ t s → WakeRunInv.RunInv Λ E t → CertAll ((target (kernel 2) E).marks asm Λ) t →
    (machine (kernel 2)).Progress ((target (kernel 2) E).marks asm Λ) t ∧ InLayout (M := machine (kernel 2)) Λ t
  /-- The program's instructions are in the wide fragment
  (`WakeRunInv.runInv_load`: the run invariant at the load). -/
  hwide : ∀ prog, (textProgram asm).toOption = some prog → Scc.Cert.WideA64.wideIn prog = true
  /-- (transports for the thread that does not step) A step
  from `Post` to `Post` keeps `CertAll`. -/
  cert_step : ∀ tid t es t' s s', Q.Post Λ t s → CertAll ((target (kernel 2) E).marks asm Λ) t →
    (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' → Q.Post Λ t' s' →
    CertAll ((target (kernel 2) E).marks asm Λ) t'
  /-- (main's wrapper, from `relW0`; the worker's fact) At `Post` a running
  thread's certification is append-free (`CertReplay.certOkCNA_of_certOkC`):
  the parent's after the `clone`. -/
  hconv : ∀ t s, Q.Post Λ t s → CertConv ((target (kernel 2) E).marks asm Λ) t
  /-- `Ti` (the structure's parameter; before the spawn: `TIC` on
  thread 0 of `up d u`) is a **trace invariant** of reachable
  two-slot configurations, handed to `pre_abort`/`post_abort` (whose
  `writeErr`/`threads` cases need the trace, not just the relation): it
  holds at the load with the empty trace. -/
  ti_load : ∀ t0, (target (kernel 2) E).load asm Λ = some t0 → Ti t0 []
  /-- A step of a related configuration extends `Ti` by its events. -/
  ti_step : ∀ tid t es t' s pre, Q.Rw Λ t s →
    (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' → Ti t pre → Ti t' (pre ++ es)
  /-- An abort step of the one-slot configuration before the spawn is
  justified (a `clone` emits no event, so every abort is such a step). -/
  pre_abort : ∀ tr d u s tid es d' k, (srcS p arch).Reach (obs tr) s → Q.R1 d s → Inert u →
    (∀ a, privLoad u.st a = none) → d.1.threads.size = d.2.slots.size → Ti (up d u) tr →
    (machine (kernel 1)).Step ((target (kernel 2) E).marks asm Λ) tid d es d' → Ev.abort k ∈ es →
    ∃ w i, Components (machine (kernel 2)) Λ w (up d u) s ∧ w.thr i = some tid ∧ AbortJustified B (srcS p arch) tr s i k
  /-- (the stub rows /) An abort step after the spawn is justified. -/
  post_abort : ∀ tr t s tid es t' k, (srcS p arch).Reach (obs tr) s → Q.Post Λ t s → Ti t tr →
    (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' → Ev.abort k ∈ es →
    ∃ w i, Components (machine (kernel 2)) Λ w t s ∧ w.thr i = some tid ∧ AbortJustified B (srcS p arch) tr s i k
  /-- The explicit witness before the spawn. -/
  pre_wit : ∀ d u s, Q.R1 d s → Inert u → (∀ a, privLoad u.st a = none) → d.1.threads.size = d.2.slots.size →
    ∃ w, Components (machine (kernel 2)) Λ w (up d u) s
  /-- (`own`/`PhRec2`) The explicit witness after the spawn. -/
  post_wit : ∀ t s, Q.Post Λ t s → WakeRunInv.RunInv Λ E t → ∃ w, Components (machine (kernel 2)) Λ w t s

/-- **`WakeObligations` give `WakeObligationsR`**: `post_step1` drops the
run invariant. -/
theorem WakeObligations.toR {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String}
    {Q : WakeRel} {E : Entry} {Ti : Cfg → List Ev → Prop} {p : CoreTerm.Prog}
    (O : WakeObligations arch Λ B asm Q E Ti p) : WakeObligationsR arch Λ B asm Q E Ti p where
  hwf := O.hwf
  hstart := O.hstart
  pre_init := O.pre_init
  pre_step := O.pre_step
  spawn := O.spawn
  post_step0 := O.post_step0
  post_step1 := fun t es t' s hP _ hu hx hs => O.post_step1 t es t' s hP hu hx hs
  unpark_src := O.unpark_src
  worker_done := O.worker_done
  pre_progress := O.pre_progress
  post_progress := O.post_progress
  hwide := O.hwide
  cert_step := O.cert_step
  hconv := O.hconv
  ti_load := O.ti_load
  ti_step := O.ti_step
  pre_abort := O.pre_abort
  post_abort := O.post_abort
  pre_wit := O.pre_wit
  post_wit := O.post_wit

section MainR

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {Q : WakeRel} {E : Entry}
  {p : CoreTerm.Prog}

/-- **A step before the spawn**: a matching source run to `Pre`, or (the
`clone`) to `Post` with `CertAll` (`certAll_afterClone`). -/
theorem wake_stepPreR {Ti : Cfg → List Ev → Prop} (O : WakeObligationsR arch Λ B asm Q E Ti p) {tid : Nat}
    {t t' : Cfg} {es : List Ev} {s : TermRun.Cfg} (hR : Q.Pre t s)
    (hs : (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t') :
    ∃ s', (srcS p arch).Run s (obs es) s' ∧
      (Q.Pre t' s' ∨ (Q.Post Λ t' s' ∧ CertAll ((target (kernel 2) E).marks asm Λ) t')) := by
  obtain ⟨d, u, rfl, hu, hpl, hn, hR⟩ := hR
  obtain ⟨-, ⟨d', hd', rfl⟩ | ⟨rfl, th, stack, tls, r, h1, h2, h3, h4, h5, h6, h7, rfl, hc⟩⟩ :=
    step_up_cases hn hs
  · obtain ⟨s', hr, hR', hn'⟩ := O.pre_step tid d es d' s hR hn hd'
    exact ⟨s', hr, .inl ⟨d', u, rfl, hu, hpl, hn', hR'⟩⟩
  · obtain ⟨s', hr, hP⟩ := O.spawn tid d s th stack tls r hR hn h1 h2 h3 h4 h5 h6 h7 hc
    have hsz : d.1.threads.size = 1 := by
      obtain ⟨-, ⟨t0, t1, -, -, -, -, -, hT, -⟩, -⟩ := hP
      have := congrArg Array.size hT
      simp [afterClone] at this
      omega
    exact ⟨s', hr, .inr ⟨hP, certAll_afterClone hsz h1 hc (O.hconv _ _ hP)⟩⟩

/-- **A step after the spawn** keeps `Post`, with a matching source run. -/
theorem wake_stepPostR {Ti : Cfg → List Ev → Prop} (O : WakeObligationsR arch Λ B asm Q E Ti p) {tid : Nat}
    {t t' : Cfg} {es : List Ev} {s : TermRun.Cfg} (hP : Q.Post Λ t s) (hri : WakeRunInv.RunInv Λ E t)
    (hs : (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t') :
    ∃ s', (srcS p arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  rcases tid with _ | _ | tid
  · exact O.post_step0 t es t' s hP hs
  · by_cases hu : Q.atUnpk t s
    · exact O.unpark_src t es t' s hP hu hs
    by_cases hx : Q.atTexit t s
    · exact O.worker_done t es t' s hP hx hs
    exact O.post_step1 t es t' s hP hri hu hx hs
  · exfalso
    obtain ⟨⟨th, hth⟩, -, -⟩ := hs.runs
    obtain ⟨-, ⟨t0, t1, -, -, -, -, -, h1, -⟩, -⟩ := hP
    rw [h1] at hth
    simp at hth

/-- **The step-wise simulation.** -/
theorem wake_stepSimR {Ti : Cfg → List Ev → Prop} (O : WakeObligationsR arch Λ B asm Q E Ti p) :
    StepSim (target (kernel 2) E) (srcS p arch) Λ asm (Rx Q Λ E ((target (kernel 2) E).marks asm Λ)) where
  init := by
    intro t0 h0
    have hri := WakeRunInv.runInv_load O.hwide h0
    obtain ⟨d, u, hd, rfl, hu, hpl, hn⟩ := load_two h0
    obtain ⟨s0, hi, hR⟩ := O.pre_init d hd
    exact ⟨s0, hi, hri, .inl ⟨d, u, rfl, hu, hpl, hn, hR⟩⟩
  step := by
    intro tid t es t' s hR hs
    change (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' at hs
    rcases hR with ⟨hri, hpre | ⟨hP, hca⟩⟩
    · obtain ⟨s', hr, h'⟩ := wake_stepPreR O hpre hs
      exact ⟨s', hr, WakeRunInv.runInv_step hri hs, h'⟩
    · obtain ⟨s', hr, hP'⟩ := wake_stepPostR O hP hri hs
      exact ⟨s', hr, WakeRunInv.runInv_step hri hs, .inr ⟨hP', O.cert_step tid t es t' s s' hP hca hs hP'⟩⟩

/-- **The trace invariant along a run**: from a related configuration
satisfying `Ti` with trace `pre`, a run keeps `Ti` with the run's events
appended (by `ti_step`, the relation carried by `wake_stepSim`). -/
theorem wake_tiRunR {Ti : Cfg → List Ev → Prop} (O : WakeObligationsR arch Λ B asm Q E Ti p) {t t' : Cfg} {tr : List Ev}
    (hr : (machine (kernel 2)).Run ((target (kernel 2) E).marks asm Λ) t tr t') {s : TermRun.Cfg}
    (hR : Rx Q Λ E ((target (kernel 2) E).marks asm Λ) t s) {pre : List Ev} (hT : Ti t pre) :
    Ti t' (pre ++ tr) := by
  induction hr generalizing s pre with
  | refl => simpa using hT
  | step hs _ ih =>
    obtain ⟨tid, hs⟩ := hs
    obtain ⟨s1, -, hR1⟩ := (wake_stepSimR O).step _ _ _ _ _ hR hs
    simpa [List.append_assoc] using ih hR1 (O.ti_step tid _ _ _ s pre hR.rw hs hT)

/-- **Correct at one entry state** (`hello_correctE_R` is it at each admissible `E`). -/
theorem hello_correct_atR {Q : WakeRel} {E : Entry} {Ti : Cfg → List Ev → Prop}
    (O : WakeObligationsR arch Λ B asm Q E Ti p) : Correct (target (kernel 2) E) (srcS p arch) Λ B asm := by
  have hsim := wake_stepSimR O
  refine correct_of_stepSim hsim O.hwf ?_ ?_ ?_ ?_
  · obtain ⟨d, hd⟩ := O.hstart
    obtain ⟨u, hu, -⟩ := load_one hd
    exact ⟨_, hu⟩
  · intro t0 tr t h0 hr
    obtain ⟨s, -, hri, hR⟩ := hsim.reach h0 hr
    rcases hR with ⟨d, u, rfl, hu, hpl, hn, hR⟩ | ⟨hP, hca⟩
    · exact O.pre_progress d u s hR hu hpl hn
    · exact O.post_progress t s hP hri hca
  · intro t0 tr t tid es t' k s h0 hr hreach hR hs hk
    change (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' at hs
    have hTi : Ti t tr := by
      obtain ⟨s0, -, hR0⟩ := hsim.init t0 h0
      simpa using wake_tiRunR O hr hR0 (O.ti_load t0 h0)
    rcases hR.2 with ⟨d, u, rfl, hu, hpl, hn, hR⟩ | ⟨hP, -⟩
    · obtain ⟨-, ⟨d', hd', rfl⟩ | ⟨rfl, -⟩⟩ := step_up_cases hn hs
      · exact O.pre_abort tr d u s tid es d' k hreach hR hu hpl hn hTi hd' hk
      · cases hk
    · exact O.post_abort tr t s tid es t' k hreach hP hTi hs hk
  · intro t s hR
    rcases hR with ⟨hri, ⟨d, u, rfl, hu, hpl, hn, hR⟩ | ⟨hP, -⟩⟩
    · exact O.pre_wit d u s hR hu hpl hn
    · exact O.post_wit t s hP hri

/-- **wake.w is correct on AArch64 with two slots**, given the obligations
at every admissible entry state. -/
theorem hello_correctE_R (Ti : Entry → Cfg → List Ev → Prop)
    (O : ∀ E : Entry, E.Ok Λ → WakeObligationsR arch Λ B asm Q E (Ti E) p) :
    CorrectE 2 (srcS p arch) Λ B asm :=
  fun E hE => hello_correct_atR (O E hE)

end MainR

/-- info: 'Spike.Lib.WakeA64.hello_correct_atR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeA64.hello_correct_atR

/-- info: 'Spike.Lib.WakeA64.hello_correctE_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hello_correctE_R

/-- `hello_correctE_R`'s conclusion is `wake_correctE`'s. -/
example (Ti : Entry → Cfg → List Ev → Prop) {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget}
    {asm : String} {Q : WakeRel} {p : CoreTerm.Prog}
    (O : ∀ E : Entry, E.Ok Λ → WakeObligations arch Λ B asm Q E (Ti E) p) :
    CorrectE 2 (srcS p arch) Λ B asm :=
  hello_correctE_R Ti fun E hE => (O E hE).toR

end Spike.Lib.WakeA64
