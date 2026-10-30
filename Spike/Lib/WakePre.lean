/-
**wake.w on AArch64, the pre-spawn obligations from one-slot ones**: `WakeObligations`' `pre_init`, `pre_step`,
`pre_progress`, `pre_abort` and `pre_wit` (`Spike/Lib/WakeA64.lean`) from a
relation `R1` on the one-slot configuration, stated at one slot only
(`Pre1`).

`pre_init` and `pre_step` are already one-slot statements (the two-slot
lift is `WakeA64.wake_stepSim`'s); `pre_progress` is one-slot progress off
main's `clone` (`progress_up`), and the lifted configuration's at it (where
the one-slot configuration faults: no dormant slot); the
witnesses of `pre_abort` and `pre_wit` are one-slot `Components`
transferred to the lift (`Spike.Lib.TwoSlot.components_up`), which needs
the extra thread to own no stack: no range held for its index (`held`).

So the pre-spawn half of 1.6 is a one-thread consumer for `R1` in the
style of hello1's (`Spike/Lib/A64ConsumerACorrect.lean`: `stepSimA` gives
`init`/`step`, `pre_progressA`/`r_progressA` and `r_memInA` give
`progress`, `r_abortA` gives `abort`, `r_componentsA` gives `wit`), for
main's code up to its `clone`, plus `held`. In a `WakeObligations`
instance: `pre_init := O.init`, `pre_step := O.step`,
`pre_progress := O.pre_progress`, `pre_abort := O.pre_abort`,
`pre_wit := O.pre_wit` (`O : Pre1 … Q.R1`).
-/
import Spike.Lib.WakeA64
import Spike.Lib.TwoSlotComp
import Spike.Lib.CloneOne

namespace Spike.Lib.WakePre

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.TwoSlot Spike.Lib.A64TwoSlot Spike.Lib.WakeT1 Spike.Lib.WakeA64

/-- **A thread of `d` at a `clone` call** (running, at the system-call
instruction). At one slot this faults (no dormant slot), so progress there
is the lifted configuration's. -/
def AtClone (d : Cfg) : Prop :=
  ∃ tid th stack tls, d.1.threads[tid]? = some th ∧ abi.atSys th.st = true ∧ d.2.runs tid = true ∧
    callOf abi th = some (.clone stack tls)

/-- **The pre-spawn obligations at one slot**, for the relation `R1` (with
`μ` the loaded program's marks). -/
structure Pre1 (arch : WeakMem.Arch) (Λ : Scc.Sem.Layout) (B : Budget) (asm : String) (E : Entry)
    (R1 : Cfg → TermRun.Cfg → Prop) : Prop where
  /-- The one-slot load is related to a source start. -/
  init : ∀ d, (target (kernel 1) E).load asm Λ = some d → ∃ s0, (wakeS arch).init s0 ∧ R1 d s0
  /-- A one-slot step keeps `R1` and the slot count, with a matching source run. -/
  step : ∀ tid d es d' s, R1 d s → d.1.threads.size = d.2.slots.size →
    (machine (kernel 1)).Step ((target (kernel 2) E).marks asm Λ) tid d es d' →
    ∃ s', (wakeS arch).Run s (obs es) s' ∧ R1 d' s' ∧ d'.1.threads.size = d'.2.slots.size
  /-- Progress and layout at one slot, off a `clone`. -/
  progress : ∀ d s, R1 d s → d.1.threads.size = d.2.slots.size → ¬ AtClone d →
    (machine (kernel 1)).Progress ((target (kernel 2) E).marks asm Λ) d ∧ InLayout (M := machine (kernel 1)) Λ d
  /-- Progress and layout at a `clone`, of the lifted configuration (the
  `clone` into the extra slot steps: `Spike.Lib.Handover.clone_step`). -/
  progressClone : ∀ d u s, R1 d s → Inert u → (∀ a, privLoad u.st a = none) →
    d.1.threads.size = d.2.slots.size → AtClone d →
    (machine (kernel 2)).Progress ((target (kernel 2) E).marks asm Λ) (up d u) ∧
      InLayout (M := machine (kernel 2)) Λ (up d u)
  /-- A one-slot abort step is justified, with one-slot components. -/
  abort : ∀ tr d s tid es d' k, (wakeS arch).Reach (obs tr) s → R1 d s → d.1.threads.size = d.2.slots.size →
    (machine (kernel 1)).Step ((target (kernel 2) E).marks asm Λ) tid d es d' → Ev.abort k ∈ es →
    ∃ w i, Components (machine (kernel 1)) Λ w d s ∧ w.thr i = some tid ∧ AbortJustified B (wakeS arch) tr s i k
  /-- The explicit witness at one slot. -/
  wit : ∀ d s, R1 d s → d.1.threads.size = d.2.slots.size → ∃ w, Components (machine (kernel 1)) Λ w d s
  /-- No stack range is held for the extra slot's index. -/
  held : ∀ d s, R1 d s → d.1.threads.size = d.2.slots.size → ∀ h ∈ d.2.held, h.1 ≠ d.1.threads.size

namespace Pre1

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {E : Entry}
  {R1 : Cfg → TermRun.Cfg → Prop}

/-- `WakeObligations.pre_progress`. -/
theorem pre_progress (O : Pre1 arch Λ B asm E R1) :
    ∀ d u s, R1 d s → Inert u → (∀ a, privLoad u.st a = none) → d.1.threads.size = d.2.slots.size →
      (machine (kernel 2)).Progress ((target (kernel 2) E).marks asm Λ) (up d u) ∧
        InLayout (M := machine (kernel 2)) Λ (up d u) := by
  intro d u s hR hu hpl hn
  by_cases hc : AtClone d
  · exact O.progressClone d u s hR hu hpl hn hc
  · obtain ⟨hp, hl⟩ := O.progress d s hR hn hc
    exact ⟨progress_up hn hu hp, hl⟩

/-- `WakeObligations.pre_abort`. -/
theorem pre_abort (O : Pre1 arch Λ B asm E R1) :
    ∀ tr d u s tid es d' k, (wakeS arch).Reach (obs tr) s → R1 d s → Inert u →
      (∀ a, privLoad u.st a = none) → d.1.threads.size = d.2.slots.size →
      (machine (kernel 1)).Step ((target (kernel 2) E).marks asm Λ) tid d es d' → Ev.abort k ∈ es →
      ∃ w i, Components (machine (kernel 2)) Λ w (up d u) s ∧ w.thr i = some tid ∧
        AbortJustified B (wakeS arch) tr s i k := by
  intro tr d u s tid es d' k hr hR _ hpl hn hs hk
  obtain ⟨w, i, hc, hw, hj⟩ := O.abort tr d s tid es d' k hr hR hn hs hk
  exact ⟨w, i, components_up hn hpl (O.held d s hR hn) hc, hw, hj⟩

/-- `WakeObligations.pre_wit`. -/
theorem pre_wit (O : Pre1 arch Λ B asm E R1) :
    ∀ d u s, R1 d s → Inert u → (∀ a, privLoad u.st a = none) → d.1.threads.size = d.2.slots.size →
      ∃ w, Components (machine (kernel 2)) Λ w (up d u) s := by
  intro d u s hR _ hpl hn
  obtain ⟨w, hc⟩ := O.wit d s hR hn
  exact ⟨w, components_up hn hpl (O.held d s hR hn) hc⟩

/-- **`progressClone` from one-thread facts** at the `clone`: `d`'s one
thread runs, is not halted and has no promise (at a `clone` a certified
thread has none: `Spike.Lib.Handover.prom_nil_of_clone`), and `d` is in the
layout; the lifted configuration's refusal steps
(`Spike.Lib.CloneOne.clone_progress_up`). -/
theorem progressClone_of {μ : Marks} {R1 : Cfg → TermRun.Cfg → Prop}
    (h : ∀ d s, R1 d s → d.1.threads.size = d.2.slots.size → AtClone d →
      ∃ th, d.1.threads = #[th] ∧ d.2.runs 0 = true ∧ d.2.exited = none ∧ th.halted = false ∧ th.prom = [] ∧
        InLayout (M := machine (kernel 1)) Λ d) :
    ∀ d u s, R1 d s → Inert u → (∀ a, privLoad u.st a = none) →
      d.1.threads.size = d.2.slots.size → AtClone d →
      (machine (kernel 2)).Progress μ (up d u) ∧ InLayout (M := machine (kernel 2)) Λ (up d u) := by
  intro d u s hR _ _ hn hc
  obtain ⟨th, hth, hr, hx, hnh, hp, hl⟩ := h d s hR hn hc
  obtain ⟨tid, t, stack, tls, ht, ha, -, hcall⟩ := hc
  have h0 : tid = 0 := by
    have hlt : tid < d.1.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
    rw [hth] at hlt
    exact Nat.lt_one_iff.mp hlt
  subst h0
  obtain rfl : th = t := by rw [hth] at ht; exact Option.some.inj ht
  exact ⟨Spike.Lib.CloneOne.clone_progress_up hn hth hr hx ha hcall hnh hp, hl⟩

/-- **`held` from one thread**: with one thread, every held range of index
0 (the main thread's stacks) is not the extra slot's. -/
theorem held_of {R1 : Cfg → TermRun.Cfg → Prop}
    (h : ∀ d s, R1 d s → d.1.threads.size = d.2.slots.size → d.1.threads.size = 1 ∧ ∀ h ∈ d.2.held, h.1 = 0) :
    ∀ d s, R1 d s → d.1.threads.size = d.2.slots.size → ∀ h ∈ d.2.held, h.1 ≠ d.1.threads.size := by
  intro d s hR hn hh hm
  obtain ⟨h1, h0⟩ := h d s hR hn
  rw [h0 hh hm, h1]
  exact Nat.zero_ne_one

end Pre1

/-- info: 'Spike.Lib.WakePre.Pre1.pre_abort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pre1.pre_abort

end Spike.Lib.WakePre
