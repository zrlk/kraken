/-
**A fence step at the thread level** (the `Out.fence` row's machine side):
an instruction whose event tree is one fence then a `done` leaf
(`.fence k fun _ => .done s'`, AArch64 `dmb`) runs to that leaf in the
fenced context `fenceStep c k`, which moves only the context's views and
log (`fenceStep_mem`, `fenceStep_prom`).

- `run_fence`: the tree's one run.
- `stepOne_fence_ok`: every successful `stepOne` outcome is `finishInstr`
  at `s'` from the fenced context, memory unchanged, promises unchanged
  (`stepOne_silent_ok`'s counterpart; only the views differ).
- `stepOne_fence_exists`: every thread `finishInstr` gives there is an
  outcome (`stepOne_silent_exists`'s counterpart).
- `stepOne_fence_no_error`: no error outcome.
- `stepOne_fence_progress`: some outcome, with the thread's promises kept.
-/
import Kraken.Promising.Lower.Silent
import Spike.Bridge.Progress

namespace Spike.Lib.FenceStep

open Kraken.Promising Kraken.Promising.Lower
open Kraken.Promising.Live.TicketStep (ctx0)

/-- A fence moves no memory. -/
@[simp] theorem fenceStep_mem (c : Ctx) (k : Kraken.FenceKind) : (fenceStep c k).mem = c.mem := by
  cases k <;> rfl

/-- A fence moves no promise. -/
@[simp] theorem fenceStep_prom (c : Ctx) (k : Kraken.FenceKind) : (fenceStep c k).prom = c.prom := by
  cases k <;> rfl

variable {I : ISA} (A : Arch) (tid : Nat) {t : Thread I} {mem : Memory} {k : Kraken.FenceKind} {s' : I.State}

/-- **The one run of a fence-then-leaf tree**: the leaf in the fenced
context. -/
theorem run_fence {σ : Type} (iv : InstrViews) (c : Ctx) (s : σ) :
    runTree A tid iv c (.fence k fun _ => .done s) = [.ok (s, fenceStep c k)] := rfl

/-- **Every successful `stepOne` outcome at a fence** is `finishInstr` at
the leaf from the fenced context, with memory and promises unchanged. -/
theorem stepOne_fence_ok (hex : I.exec t.st = some (.fence k fun _ => .done s')) {th : Thread I}
    {mem' : Memory} (h : ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread = th ∧ o.mem = mem') :
    th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s' (fenceStep (ctx0 tid t mem) k) ∧
      mem' = mem ∧ th.prom = t.prom := by
  obtain ⟨st, c', hr, hth, rfl⟩ := (stepOne_ok_iff A tid hex).mp h
  rw [run_fence, List.mem_singleton] at hr
  simp only [Except.ok.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  refine ⟨hth, by simp [ctx0], ?_⟩
  rw [(finishInstr_relKey hth).1]
  simp [ctx0]

/-- **Every thread `finishInstr` gives at a fence's leaf is a `stepOne`
outcome**, with the memory unchanged. -/
theorem stepOne_fence_exists (hex : I.exec t.st = some (.fence k fun _ => .done s')) {th : Thread I}
    (hth : th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s' (fenceStep (ctx0 tid t mem) k)) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread = th ∧ o.mem = mem := by
  refine (stepOne_ok_iff A tid hex).mpr ⟨s', _, ?_, hth, by simp [ctx0]⟩
  rw [run_fence]; exact List.mem_singleton.mpr rfl

/-- **No error outcome** at a fence. -/
theorem stepOne_fence_no_error (hex : I.exec t.st = some (.fence k fun _ => .done s'))
    {outs : List (Except String (Outcome I))} (hso : stepOne A t tid mem = some outs) (m : String) :
    (.error m : Except String (Outcome I)) ∉ outs := by
  unfold stepOne at hso
  rw [hex] at hso
  have hs' : _ = outs := Option.some.inj hso
  subst hs'
  simp [run_fence]

/-- **A fence has an outcome**, with the thread's promises kept. -/
theorem stepOne_fence_progress (hex : I.exec t.st = some (.fence k fun _ => .done s')) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = t.prom := by
  obtain ⟨th, hth⟩ := Spike.Bridge.finishInstr_nonempty t (I.deps t.st) (instrViews t (I.deps t.st)) s'
    (fenceStep (ctx0 tid t mem) k)
  obtain ⟨outs, o, hs, ho, rfl, -⟩ := stepOne_fence_exists A tid hex hth
  exact ⟨outs, o, hs, ho, (stepOne_fence_ok A tid hex ⟨outs, o, hs, ho, rfl, rfl⟩).2.2⟩

end Spike.Lib.FenceStep
