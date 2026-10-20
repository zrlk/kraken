/-
**Stage 3: ISA-neutral pieces for the x64
spinlocks' liveness.** Candidates to hoist into the existing `Live*` files.

- `ProgressFromN`: deadlock-freedom from `c0` under `Fair`, defined as
  `Live.Spin.ProgressFrom` (which lived in `LiveSpin.lean`, a file that
  imports the AArch64 syntax via `CasSmoke`; it is now in the ISA-neutral
  `LiveTrace.lean`). The `choose` lemmas below have no other copy.
- A choice of register-only outcomes, `choose n (fun i => done (f i))` (x64:
  an instruction that leaves a flag undefined, e.g. `xorl`/`testl` leave `AF`
  undefined and the adapter turns it into `.choose 2`): every outcome
  (`spec_choose`) and the existence of one (`en_choose`).
-/
import Kraken.Promising.LiveTicketStep

namespace Kraken.Promising.Live.SpinX64Step

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.TicketStep

variable {I : ISA}

/-- **Deadlock-freedom from `c0` under `Fair`**: on every (stuttering) trace
from `c0` satisfying `Fair`, if a thread is `Waiting` at index `i`, then some
thread that is not `Done` at `i` is `Done` at a later index. Formerly an
ISA-neutral copy of `Live.Spin.ProgressFrom`; that definition
is ISA-neutral (`LiveTrace.lean`) and this is it. -/
def ProgressFromN (A : Arch) (fuel : Nat) (c0 : Config I) (Fair : (Nat → Config I) → Prop)
    (Waiting Done : Nat → Config I → Prop) : Prop :=
  Spin.ProgressFrom A fuel c0 Fair Waiting Done

section Shapes

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem run_choose {σ : Type} {c c' : Ctx} {n : Nat} {f : Fin n → σ} {st : σ}
    (h : .ok (st, c') ∈ runTree A tid iv c (.choose n fun i => .done (f i))) : (∃ i, st = f i) ∧ c' = c := by
  simp only [runTree, List.mem_flatMap, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨i, -, rfl, rfl⟩ := h
  exact ⟨⟨i, rfl⟩, rfl⟩

theorem run_choose_exists {σ : Type} (c : Ctx) {n : Nat} (f : Fin n → σ) (i : Fin n) :
    .ok (f i, c) ∈ runTree A tid iv c (.choose n fun i => .done (f i)) := by
  simp only [runTree, List.mem_flatMap, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq]
  exact ⟨i, List.mem_finRange i, rfl, trivial⟩

end Shapes

section Spec

variable (A : Arch) (tid : Nat) {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))}
  {o : Outcome I}

/-- A choice of register-only outcomes: memory, promises and coherence views
unchanged; the state is one of the choices. -/
theorem spec_choose {n : Nat} {f : Fin n → I.State} (hex : I.exec t.st = some (.choose n fun i => .done (f i)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    o.mem = mem ∧ (∃ i, o.thread.st = f i) ∧ o.thread.prom = t.prom ∧ o.thread.views.coh = t.views.coh := by
  obtain ⟨st, c', hr, hm, hst, hp, hc, -⟩ := stepOne_out A tid hex hs ho
  obtain ⟨⟨i, rfl⟩, rfl⟩ := run_choose A tid _ hr
  exact ⟨hm, ⟨i, hst⟩, hp, hc⟩

theorem en_choose {n : Nat} {f : Fin n → I.State} (hn : 0 < n)
    (hex : I.exec t.st = some (.choose n fun i => .done (f i))) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = t.prom := by
  obtain ⟨outs, o, h1, h2, -, -, h3⟩ :=
    stepOne_of_run A tid hex (run_choose_exists A tid _ (ctx0 tid t mem) f ⟨0, hn⟩)
  exact ⟨outs, o, h1, h2, h3⟩

end Spec

end Kraken.Promising.Live.SpinX64Step
