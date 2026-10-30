/-
**The thread-id boxes along source runs** (`Scc.Sem.boxCount`): every box
was counted by an allocation, `boxCount s ≤ allocCount s`, at every
configuration `SrcSem.source P p` reaches from a start where it holds, with
no hook or WeakCore's (`UsesWc`). This is the run fact `heapUse`'s
subtraction of the boxes (`Scc/Sem/Correct.lean`) relies on when an
allocation's units are added (`HeapPres.heapUse_alloc`,
`abortJustified_heap_source`); no trusted statement takes it.

- `boxCount_set`: a thread replaced by one with the same `tidLbl` keeps
  `boxCount`;
- `allocCount_succ`, `heapUse_add`: the heap use grows with the words plus
  allocations, the allocations not decreasing, the boxes kept and counted;
- `threadSteps_tidLbl`: a thread step keeps the thread's box label;
- `boxLe_set`: a thread replaced by one whose allocation count grows by at
  least its box indicator's growth keeps `boxCount ≤ allocCount`;
- the steps: a thread step (`tstep_tidLbl`, `tstep_nalloc`), a promise, a
  spawn (the parent's count grows by the child's box and, the first time, its
  own), an extern step (`current`'s first use allocates the box) and a wake
  (permits only);
- `reach_boxLe`: along every run;
- `progInit_boxLe`, `setupStart_boxLe`, `mainStart_boxLe`: at the starts.
-/
import Scc.Sem.SrcOutProto
import Scc.Sem.Budget
import WeakCore.TermExtStep
import WeakCore.TermTidLbl
import WeakCore.TermPtrKey
import WeakCore.TermSpawnStep

namespace Spike.Lib.BoxCount

open CoreLang CoreTerm TermRun
open Scc.Sem (SrcSem Ev boxCount allocCount)

/-- The box indicator of a thread. -/
abbrev bx (th : TTh) : Nat := if th.tidLbl.isSome = true then 1 else 0

/-- `boxCount` is a count over the thread list. -/
theorem boxCount_eq (s : Cfg) : boxCount s = s.ths.toList.countP (·.tidLbl.isSome) := rfl

/-- **A thread replaced by one with the same box label keeps the box
count.** -/
theorem boxCount_set {s s' : Cfg} {i : Nat} {th th' : TTh} (hi : s.ths[i]? = some th)
    (hths : s'.ths = s.ths.set! i th') (ht : th'.tidLbl = th.tidLbl) : boxCount s' = boxCount s := by
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  rw [boxCount_eq, boxCount_eq, hths]
  simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt, dite_true, Array.toList_set]
  rw [List.countP_set (by simpa using hlt)]
  have := List.boole_getElem_le_countP (p := fun t : TTh => t.tidLbl.isSome) (l := s.ths.toList)
    (i := i) (by simpa using hlt)
  simp only [Array.getElem_toList] at this ⊢
  rw [ht]
  omega

/-- **A thread replaced by one whose allocation count grows by at least its
box indicator's growth** keeps `boxCount ≤ allocCount`. -/
theorem boxLe_set {s s' : Cfg} {i : Nat} {th th' : TTh} (hi : s.ths[i]? = some th)
    (hths : s'.ths = s.ths.set! i th') (h : bx th' + th.nalloc ≤ bx th + th'.nalloc)
    (hb : boxCount s ≤ allocCount s) : boxCount s' ≤ allocCount s' := by
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  rw [boxCount_eq, Scc.Sem.allocCount_eq] at hb ⊢
  unfold Scc.Sem.nallocSum at hb ⊢
  rw [hths]
  simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt, dite_true, Array.toList_set]
  rw [List.countP_set (by simpa using hlt)]
  have h1 := List.boole_getElem_le_countP (p := fun t : TTh => t.tidLbl.isSome) (l := s.ths.toList)
    (i := i) (by simpa using hlt)
  have h2 := Scc.Sem.list_sum_set (l := s.ths.toList) (by simpa using hlt) th'
  simp only [Array.getElem_toList, bx] at h1 h2 h ⊢
  omega

/-- **A thread step keeps the thread's box label and does not lower its
allocation count**, read off the configuration it reaches. -/
theorem threadSteps_th {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {c c' : Cfg} {i : Nat}
    {th th' : TTh} (h : c' ∈ threadSteps p k arch c i) (hi : c.ths[i]? = some th) (hi' : c'.ths[i]? = some th') :
    th'.tidLbl = th.tidLbl ∧ th.nalloc ≤ th'.nalloc := by
  unfold threadSteps at h
  rw [hi] at h
  simp only [List.mem_map] at h
  obtain ⟨⟨mem', pairs', th''⟩, hr, rfl⟩ := h
  have hlt := (Array.getElem?_eq_some_iff.mp hi).1
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hlt, ite_true,
    Option.some.injEq] at hi'
  subst hi'
  exact ⟨TermTidLbl.tstep_tidLbl hr, TermPtrKey.tstep_nalloc hr⟩

/-- `threadSteps_th` at a configuration whose thread `i` is replaced by
`th'`. -/
theorem threadSteps_tidLbl {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {c c' : Cfg} {i : Nat}
    {th th' : TTh} (h : c' ∈ threadSteps p k arch c i) (hi : c.ths[i]? = some th)
    (hths : c'.ths = c.ths.set! i th') : th'.tidLbl = th.tidLbl :=
  (threadSteps_th h hi (by
    rw [hths, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp [(Array.getElem?_eq_some_iff.mp hi).1])).1

/-- **A thread's allocation count bumped** adds one to `allocCount`. -/
theorem allocCount_succ {s s' : Cfg} {i : Nat} {th th' : TTh} (hi : s.ths[i]? = some th)
    (hths : s'.ths = s.ths.set! i th') (hn : th'.nalloc = th.nalloc + 1) : allocCount s' = allocCount s + 1 := by
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  rw [Scc.Sem.allocCount_eq, Scc.Sem.allocCount_eq, hths]
  simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt, dite_true]
  exact Scc.Sem.nallocSum_set hlt hn

/-- **The heap use grows by `u`** when the words plus allocations do, the
allocations not decreasing and the box count kept, the boxes counted by the
allocations before. -/
theorem heapUse_add {c c' : Cfg} {u : Nat}
    (hca : Scc.Sem.cellCount c' + allocCount c' = Scc.Sem.cellCount c + allocCount c + u)
    (hmono : allocCount c ≤ allocCount c') (hb : boxCount c' = boxCount c) (hle : boxCount c ≤ allocCount c) :
    Scc.Sem.heapUse c' = Scc.Sem.heapUse c + u := by
  unfold Scc.Sem.heapUse
  rw [hb]
  omega

/-! ## The steps -/

/-- **A thread step** keeps `boxCount ≤ allocCount`: the box label kept
(`tstep_tidLbl`), the allocation count not decreasing (`tstep_nalloc`). -/
theorem boxLe_thread {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {c c' : Cfg} {i : Nat}
    (h : c' ∈ threadSteps p k arch c i) (hb : boxCount c ≤ allocCount c) : boxCount c' ≤ allocCount c' := by
  unfold threadSteps at h
  cases hth : c.ths[i]? with
  | none => rw [hth] at h; cases h
  | some th =>
    rw [hth] at h
    simp only [List.mem_map] at h
    obtain ⟨⟨mem', pairs', th'⟩, hr, rfl⟩ := h
    have ht := TermTidLbl.tstep_tidLbl hr
    have hn := TermPtrKey.tstep_nalloc hr
    simp only at ht hn
    exact boxLe_set hth rfl (by simp only [bx, ht]; omega) hb

/-- **A promise** keeps `boxCount ≤ allocCount` (it changes only the
thread's promises). -/
theorem boxLe_prom {c : Cfg} {i : Nat} {a : WeakMem.Address} {v : WeakMem.Val} {w : WeakMem.Ts}
    (hb : boxCount c ≤ allocCount c) : boxCount (promise c i a v w) ≤ allocCount (promise c i a v w) := by
  unfold promise
  cases hth : c.ths[i]? with
  | none => exact hb
  | some th => exact boxLe_set hth rfl (by simp [bx]) hb

/-- **A spawn** keeps `boxCount ≤ allocCount`: the child's box is counted by
the parent's allocation count, as is the parent's own when the spawn
allocates it. -/
theorem boxLe_spawn {cap i : Nat} {c c' : Cfg} (h : Scc.Sem.SrcSem.SpawnBy cap i c c')
    (hb : boxCount c ≤ allocCount c) : boxCount c' ≤ allocCount c' := by
  obtain ⟨x, f, a, T, ts, e, th, rt, ws, h1, -, -, -, -, rfl⟩ := h
  obtain ⟨hlt, hth⟩ := Array.getElem?_eq_some_iff.mp h1
  have hpn : (TermSpawnStep.spawnPar c i th x e).nalloc = th.nalloc + if th.tidLbl = none then 2 else 1 := rfl
  have hpt : (TermSpawnStep.spawnPar c i th x e).tidLbl.isSome = true := by
    cases hl : th.tidLbl <;> simp [TermSpawnStep.spawnPar, hl, Option.orElse]
  have hpar : boxCount { c with ths := c.ths.set! i (TermSpawnStep.spawnPar c i th x e) } + 1 ≤
      allocCount { c with ths := c.ths.set! i (TermSpawnStep.spawnPar c i th x e) } := by
    rw [boxCount_eq, Scc.Sem.allocCount_eq] at hb ⊢
    unfold Scc.Sem.nallocSum at hb ⊢
    simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt, dite_true, Array.toList_set]
    rw [List.countP_set (by simpa using hlt)]
    have h1' := List.boole_getElem_le_countP (p := fun t : TTh => t.tidLbl.isSome) (l := c.ths.toList)
      (i := i) (by simpa using hlt)
    have h2 := Scc.Sem.list_sum_set (l := c.ths.toList) (by simpa using hlt)
      (TermSpawnStep.spawnPar c i th x e)
    simp only [Array.getElem_toList, hth] at h1' h2 ⊢
    rw [hpt]
    rw [hpn] at h2
    cases hl : th.tidLbl <;> simp only [hl, Option.isSome_some, Option.isSome_none, ite_true,
      Bool.false_eq_true, ite_false, reduceCtorEq] at h1' h2 ⊢ <;> omega
  simp only [boxCount_eq, Scc.Sem.allocCount_eq, Scc.Sem.nallocSum, TermSpawnStep.spawnCfg,
    TermSpawnStep.spawnT, Array.toList_push, List.countP_append, List.map_append, List.sum_append] at hpar ⊢
  simp [TermSpawnStep.spawnKid] at hpar ⊢
  omega

/-- **An extern step** keeps `boxCount ≤ allocCount`: `current`'s first
use allocates the box and counts it; every other extern step keeps the
thread's box label and allocation count. -/
theorem boxLe_ext {c : Cfg} {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) (x : String) (n : ExtName)
    (e : Expr) (ws rs : List Word) (hb : boxCount c ≤ allocCount c) :
    boxCount (extCfg c i th x n e ws rs) ≤ allocCount (extCfg c i th x n e ws rs) := by
  cases n with
  | current =>
      cases hl : th.tidLbl with
      | some l =>
          simp only [extCfg, curCfg, hl]
          exact boxLe_set hth rfl (by simp [bx, hl]) hb
      | none =>
          simp only [extCfg, curCfg, hl]
          exact boxLe_set hth rfl (by simp [bx, hl]; omega) hb
  | _ => exact boxLe_set hth rfl (by simp [bx]) hb

/-- **A wake** keeps `boxCount ≤ allocCount` (it changes only permits). -/
theorem boxLe_wake {c : Cfg} (i : Nat) (v : WeakMem.Ts) (n : ExtName) (ws : List Word)
    (hb : boxCount c ≤ allocCount c) : boxCount (wake c i v n ws) ≤ allocCount (wake c i v n ws) := by
  rcases TermExtStep.wake_eq c i v n ws with h | ⟨j, th, u, h1, h2⟩
  · rw [h]; exact hb
  · rw [h2]; exact boxLe_set h1 rfl (by simp [bx]) hb

/-! ## Along runs -/

/-- **Every reachable source configuration has `boxCount ≤ allocCount`**,
from starts where it holds, with no hook or WeakCore's (`UsesWc`). -/
theorem reach_boxLe {P : SrcSem.SrcParams} {p : Prog}
    (hH : P.hooks = SrcSem.SrcHooks.none ∨ Scc.Sem.SrcOutProto.UsesWc P p)
    (hinit : ∀ c, P.init c → boxCount c ≤ allocCount c) {tr : List Ev}
    {s : Cfg} (h : (SrcSem.source P p).Reach tr s) : boxCount s ≤ allocCount s := by
  obtain ⟨s0, h0, hr⟩ := h
  have H := hinit s0 h0
  clear h0
  induction hr with
  | refl => exact H
  | step hs _ ih =>
    obtain ⟨i, -, hs, -⟩ := hs
    apply ih
    rcases hs with hs | hs | hs
    · rcases hs with ⟨hs, -⟩ | ⟨a, v, w, -, -, -, rfl⟩
      · exact boxLe_thread hs H
      · exact boxLe_prom H
    · exact boxLe_spawn hs H
    · rcases hH with hH | hH <;> rw [hH] at hs
      · exact hs.elim
      obtain ⟨x, n, a, e, th1, rt, ws, rs, h1, -, -, -, -, -, rfl⟩ := hs
      exact boxLe_wake _ _ _ _ (boxLe_ext h1 x n e ws rs H)

/-! ## The starts -/

/-- **Every start of a program** (`progInit`) has its boxes counted: none
but `tidStartT`'s and `setupStartT`'s, whose box is its one allocation. -/
theorem progInit_boxLe {p : Prog} {cap : Nat} {c : Cfg} (h : SrcSem.progInit p cap c) :
    boxCount c ≤ allocCount c := by
  have key : SrcSem.progInit p cap = SrcSem.mainInit cap ∨ SrcSem.progInit p cap = SrcSem.tidInit cap ∨
      SrcSem.progInit p cap = SrcSem.setupInit cap ∨
      SrcSem.progInit p cap = (· = SrcSem.tidStartT cap) ∨
      SrcSem.progInit p cap = (· = SrcSem.setupStartT cap) ∨ SrcSem.progInit p cap = fun _ => False := by
    unfold SrcSem.progInit
    split
    · split <;> simp
    · simp
  rcases key with e | e | e | e | e | e <;> rw [e] at h
  · subst h; simp [boxCount, allocCount, SrcSem.mainStart]
  · obtain ⟨_, rfl⟩ := h; simp [boxCount, allocCount, SrcSem.tidStart]
  · obtain ⟨_, rfl⟩ := h; simp [boxCount, allocCount, SrcSem.setupStart]
  · subst h; simp [boxCount, allocCount, SrcSem.tidStartT]
  · subst h; simp [boxCount, allocCount, SrcSem.setupStartT]
  · exact h.elim

/-- The start before the setup block (`setupStart`) has no box. -/
theorem setupStart_boxLe (cap : Nat) (meW : Word) :
    boxCount (SrcSem.setupStart cap meW) ≤ allocCount (SrcSem.setupStart cap meW) := by
  simp [boxCount, allocCount, SrcSem.setupStart]

/-- `mainStart` (at any stripe) has no box. -/
theorem mainStart_boxLe (cap : Nat) :
    boxCount { SrcSem.mainStart with cap := cap } ≤ allocCount { SrcSem.mainStart with cap := cap } := by
  simp [boxCount, allocCount, SrcSem.mainStart]

end Spike.Lib.BoxCount
