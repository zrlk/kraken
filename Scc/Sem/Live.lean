/-
Live labels across source steps (`Scc/DESIGN.md` §2.5, *Live labels*).

`Live s l` (`Scc/Sem/Correct.lean`) is reachability from the root labels
(the references in the words of every variable a frame still reads) through
the references stored in memory. The memory clauses of `Components` cover
live labels only, which is sound for a compiler proof if a dead label never
becomes live again (`dead_stays_dead`): every new reference a step stores
or binds is to a live or a fresh label.

Here: the promise step (`TermRun.promise`) changes no root and adds one
message, so a dead label becomes live across it only through the promised
value (`live_promise`); the obligation that the promised value is no
reference to a dead label is what certification has to provide (the thread
stores that value in its certifying solo run). The thread steps
(`TermRun.tstep`) are not covered here.
-/
import Scc.Sem.Correct

namespace Scc.Sem

/-- A promise changes only the promising thread's promise list, so the
frames, and the root labels, are the same. -/
theorem rootLabel_promise {c : TermRun.Cfg} {i : Nat} {a : WeakMem.Address} {v : WeakMem.Val} {w : Nat}
    {l : WeakMem.AllocLabel} (h : RootLabel (TermRun.promise c i a v w) l) : RootLabel c l := by
  obtain ⟨j, th, d, e, xs, x, ty, ws, wd, b, g, hth, he, hxs, hx, hl, hwd, hv, rfl⟩ := h
  unfold TermRun.promise at hth
  split at hth
  · exact ⟨j, th, d, e, xs, x, ty, ws, wd, b, g, hth, he, hxs, hx, hl, hwd, hv, rfl⟩
  · rename_i thi hi
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hth
    split at hth
    · rename_i hji
      split at hth
      · cases hth
        subst hji
        exact ⟨_, thi, d, e, xs, x, ty, ws, wd, b, g, hi, he, hxs, hx, hl, hwd, hv, rfl⟩
      · cases hth
    · exact ⟨j, th, d, e, xs, x, ty, ws, wd, b, g, hth, he, hxs, hx, hl, hwd, hv, rfl⟩

/-- The messages after a promise: the earlier ones and the promised one. -/
theorem mem_promise {c : TermRun.Cfg} {i : Nat} {a : WeakMem.Address} {v : WeakMem.Val} {w : Nat}
    {m : WeakMem.Msg} (h : m ∈ (TermRun.promise c i a v w).mem.toList) :
    m ∈ c.mem.toList ∨ m = ⟨a, v, w⟩ := by
  unfold TermRun.promise at h
  split at h
  · exact .inl h
  · simpa using h

/-- **A dead label becomes live across a promise only through the promised
value**: if the promised value is no reference to a dead, allocated label,
every label live after the promise was live before or is fresh. -/
theorem live_promise {c : TermRun.Cfg} {i : Nat} {a : WeakMem.Address} {v : WeakMem.Val} {w : Nat}
    (hv : ∀ b g, v = .loc b g → Live c b.label ∨ Fresh c b.label) {l : WeakMem.AllocLabel}
    (h : Live (TermRun.promise c i a v w) l) : Live c l ∨ Fresh c l :=
  Reach.step
    (fun m hm => (mem_promise hm).imp id fun he b g hb => by subst he; exact hv b g hb)
    (fun _ hr => .inl (.root (rootLabel_promise hr))) h

/-- **Dead stays dead across a promise** of a value that is no reference to
a dead, allocated label. -/
theorem dead_promise {c : TermRun.Cfg} {i : Nat} {a : WeakMem.Address} {v : WeakMem.Val} {w : Nat}
    (hv : ∀ b g, v = .loc b g → Live c b.label ∨ Fresh c b.label) {l : WeakMem.AllocLabel}
    (hd : ¬ Live c l) (hf : ¬ Fresh c l) : ¬ Live (TermRun.promise c i a v w) l :=
  fun h => (live_promise hv h).elim hd hf

end Scc.Sem
