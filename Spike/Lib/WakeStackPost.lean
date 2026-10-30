/-
**wake.w on AArch64: the stack map's clauses of `Components` after the
spawn** (`WakeAssembly`'s `post_wit`, the `stack_*` fields): at a
configuration related by `WakeRel.Post` (any relation data, in particular
`WakeQ.wakeQ`), the shared messages are in the layout (`Inv2Core.memIn`), so
`WakeStack.stackOk` gives the six clauses from the domain invariant
`Kernel.OwnDom` and the pool, which `Post` does not carry (they hold along
every run of the kernel model: `DmemPriv.PrivInv.run`).

- `memIn_post`: `Post`'s messages are in the layout.
- `stackOk_post`: `StackOk` at `Post` from `OwnDom` and the pool, for a
  witness without marked places.
- `stackOk_run`: `stackOk_post` with the domain invariant and the pool from
  the run invariant `WakeRunInv.RunInv` (the form `post_wit` takes).
- `mapped_held`: under `KR`, a location whose bytes lie in main's or the
  worker's stack range is mapped, for a read or a write (the held ranges
  are mapped regions, `Kernel.mappedRegions`).
-/
import Spike.Lib.WakeStackFields
import Spike.Lib.WakeKR
import Spike.Lib.WakeRunInv

namespace Spike.Lib.WakeStack

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.Consumer1 (MemIn)

/-- **`Post`'s messages are in the layout** (`Inv2Core.memIn`). -/
theorem memIn_post {Q : WakeRel} {Λ : Scc.Sem.Layout} {t : Cfg} {s : TermRun.Cfg} (h : Q.Post Λ t s) :
    MemIn Λ t.1.mem := by
  obtain ⟨_, ⟨_, _, _, _, _, _, _, _, _, hc, _⟩, _⟩ := h
  exact hc.memIn

/-- **The stack map's clauses after the spawn**: at `Post`, given the
domain invariant `OwnDom` and the pool the layout's (both along every run,
`DmemPriv.PrivInv.run`), for a witness without marked places. -/
theorem stackOk_post {Q : WakeRel} {Λ : Scc.Sem.Layout} (hwf : Λ.WF) {t : Cfg} {s : TermRun.Cfg}
    (h : Q.Post Λ t s) {E : Nat → BitVec 64 → Prop} {P : State → Prop} (hD : OwnDom abi E P t)
    (hpool : t.2.pool = Λ.stackPool) {w : Witness (machine (kernel 2))} (hw : ∀ j pl, ¬ w.marked j pl) :
    StackOk (machine (kernel 2)) Λ w t :=
  stackOk (n := 2) hwf hD hpool (memIn_post h) hw

/-- **The stack map's clauses after the spawn, from the run invariant**
(`post_wit`'s premise `RunInv Λ E t`), for a witness without marked
places. -/
theorem stackOk_run {Q : WakeRel} {Λ : Scc.Sem.Layout} (hwf : Λ.WF) {E : Entry} {t : Cfg} {s : TermRun.Cfg}
    (h : Q.Post Λ t s) (hr : WakeRunInv.RunInv Λ E t) {w : Witness (machine (kernel 2))}
    (hw : ∀ j pl, ¬ w.marked j pl) : StackOk (machine (kernel 2)) Λ w t :=
  stackOk_post hwf h hr.ownDom hr.pool hw

/-- **The stack ranges are mapped** under `KR`: a location each of whose
bytes lies in main's range `r0 w` or the worker's `r1 w` is mapped, for a
read or a write. -/
theorem mapped_held {ι : Type} {r0 r1 : ι → Range} {w : ι} {t : Cfg} {s : TermRun.Cfg}
    (h : WakeKR.KR r0 r1 w t s) (wr : Bool) {l : Loc}
    (hl : ∀ i < l.bytes, (r0 w).contains (l.addr.toNat + i) ∨ (r1 w).contains (l.addr.toNat + i)) :
    mapped t.2 wr l = true := by
  have hh := h.2.2.2.1
  unfold mapped
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  rw [List.any_eq_true]
  rcases hl i hi with h0 | h1
  · exact ⟨r0 w, by simp [mappedRegions, hh], decide_eq_true h0⟩
  · exact ⟨r1 w, by simp [mappedRegions, hh], decide_eq_true h1⟩

/-- info: 'Spike.Lib.WakeStack.stackOk_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeStack.stackOk_post

/-- info: 'Spike.Lib.WakeStack.stackOk_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeStack.stackOk_run

/-- info: 'Spike.Lib.WakeStack.mapped_held' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeStack.mapped_held

end Spike.Lib.WakeStack
