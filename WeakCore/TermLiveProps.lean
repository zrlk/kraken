/-
# TermLiveProps — the facts `TermLive`'s criterion rests on

`TermLive` reports a *fair livelock* as a strongly connected class of
configurations that no thread step leaves.  Its header argues from some facts
about the machine.  This module proves those facts.  It changes nothing in the
language and touches no existing proof (plan A + B).

* **A1 memory only grows.**  Every thread step, promise step and machine
  `Step` extends memory (`MemExt`: no smaller, same messages below the old
  size).  A thread step never adds a promise (`tstep_ext`, `threadSteps_ext`,
  `Step_ext`).
* **A2 memory is constant on a class.**  Configurations that reach each other
  by machine steps have the same memory (`reach_mem_eq`).  Crash steps
  (`TermLive.crashCfg`) do not touch memory, so this holds on the explorer's
  graph too.
* **A3 a class has no fresh `cas`.**  If thread `i` is at a `cas` whose
  expected value is the word's latest value in memory (`Promises.LatestIs`),
  it has a step that appends a message (`tstep_cas_appends`).  So in a class that thread steps do
  not leave, no thread waits at such a `cas` (`stale_cas`): a spinning `cas`
  in a fair livelock compares against an old value.
* **A4 an inside load reads old.**  A load step that leaves the thread's
  coherence view at the address unchanged read a message at or below that view
  (`stepLoad_stale`).  This is the local half of the header's
  memory-fairness argument.  The other half — views are constant on a class —
  is `class_coh_eq`: under the invariant `CohAt` (each coherence view is `0`
  or sits on a message at its own address; `CfgCoh` for a configuration, true
  of the initial one with all views `0`), every thread and promise step keeps
  the invariant and lowers no view (`tstep_mono`, `Step_coh`, `Reach_coh`).
  The invariant is what rules out fresh allocation and a fulfilling `casp`
  lowering a view.  End to end (`class_load_stale`): a one-word load by a
  thread step the run can come back from returns a word no newer than the
  thread's view at the address before the step.
* **B robust words need no token.**  Under `robust` (with `pwf`) every state
  of the protocol holds (`robust_holds`).  So no `store` on the word types
  (`robust_noStore`: every word store rule leaves a held state), and a typed
  `cas` on the word is `casShare` or `casEpoch` (`robust_cas`): it neither
  mints nor needs a region token.  Read shares may move (`LendCx`).

What is **not** here: a word in a held state whose token holder is done never
changes again.
That needs token uniqueness, which `MemOK` does not track.
-/
import WeakCore.TermArch
import WeakCore.CoreTyping

namespace TermLiveProps
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Promises.Sim (MemExt)

/-! ## A1 Memory only grows -/

/-- `s'` extends `s`: memory only grew, and no promise was added. -/
structure Ext (s s' : St) : Prop where
  mem : MemExt s.mem s'.mem
  prom : ∀ t ∈ s'.promises, t ∈ s.promises

@[simp] theorem Ext.rfl' (s : St) : Ext s s := ⟨Promises.Sim.MemExt.refl _, fun _ h => h⟩

theorem Ext.trans {s1 s2 s3 : St} (a : Ext s1 s2) (b : Ext s2 s3) : Ext s1 s3 :=
  ⟨Promises.Sim.MemExt.trans a.mem b.mem, fun t h => a.prom t (b.prom t h)⟩

@[simp] theorem fenceS_ext (s : St) (f : WeakMem.Fence) : Ext s (fenceS s f) :=
  ⟨Promises.Sim.MemExt.refl _, fun _ h => h⟩

theorem loadUnits_ext {arch : Arch} {pw : Word} {a : Address} {acq : Bool} {us : List Acc} {k : Nat}
    {s s' : St} {ws : List Word} (h : (s', ws) ∈ loadUnits arch pw a acq us k s) : Ext s s' := by
  obtain ⟨h1, -, h3, -⟩ := TermArch.loadUnits_frame arch pw a acq us k s h
  exact ⟨h1 ▸ Promises.Sim.MemExt.refl _, fun t ht => h3 ▸ ht⟩

theorem storeUnits_ext {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {i : Nat} {s s' : St}
    (h : s' ∈ storeUnits k arch pw a rel us ws i s) : Ext s s' :=
  let ⟨h1, h2⟩ := TermArch.storeUnits_ext k arch pw a rel us ws i s h
  ⟨h1, h2⟩

theorem alloc_ext {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s s' : St} {pw : Word} (h : (s', pw) ∈ alloc k arch lbl us ws s) : Ext s s' :=
  let ⟨h1, h2⟩ := TermArch.alloc_ext k arch lbl us ws s h
  ⟨h1, h2⟩

@[simp] theorem allocBuf_ext (lbl : AllocLabel) (n : Nat) (zero : Option (List Val)) (s : St) :
    Ext s (allocBuf lbl n zero s).1 :=
  let ⟨h1, h2⟩ := TermArch.allocBuf_ext lbl n zero s
  ⟨h1, h2⟩

/-- The simp set that turns a membership in a nest of `flatMap`/`map`/`ol` into
one implication per outcome, with the outcome substituted. -/
macro "flat" : tactic => `(tactic|
  simp (config := {contextual := true}) only [ol, Option.mem_toList,
    Option.bind_eq_some_iff, Option.map_eq_some_iff, List.mem_map, List.mem_flatMap,
    List.mem_filterMap, List.mem_singleton, List.not_mem_nil, Prod.exists,
    Prod.mk.injEq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, forall_eq',
    Option.some.injEq, Option.pure_def, Option.bind_some, reduceCtorEq, false_implies,
    implies_true, Ext.rfl', fenceS_ext, allocBuf_ext, Option.toList_none, Option.toList_some,
    Option.bind_none, Option.map_none, Option.map_some, Option.mem_def,
    Option.bind_eq_bind, Option.map_eq_map, Option.ite_none_left_eq_some, Option.ite_none_right_eq_some])

/-- Close `Ext s s'` from the helper lemmas, given the membership hypotheses. -/
macro "close_ext" : tactic => `(tactic| first
    | done
    | exact Ext.rfl' _
    | exact fenceS_ext _ _
    | exact loadUnits_ext (by assumption)
    | exact storeUnits_ext (by assumption)
    | exact alloc_ext (by assumption)
    | exact Ext.trans (loadUnits_ext (by assumption)) (storeUnits_ext (by assumption))
    | exact Ext.trans (alloc_ext (by assumption)) (fenceS_ext _ _)
    | exact Ext.trans (loadUnits_ext (by assumption)) (loadUnits_ext (by assumption)))

/-- One pass: split the goal's matches, flatten, substitute, close. -/
macro "crush1" : tactic => `(tactic| (
  repeat' split
  all_goals (try flat)
  all_goals (try intros)
  all_goals (try subst_vars)
  all_goals (try close_ext)))

/-- `∀ r ∈ L, Ext s r.1`.  A second and third pass open matches that sat
under a `flatMap`'s binder (now the last hypothesis). -/
macro "crush" : tactic => `(tactic| (
  intro r hin
  revert hin
  crush1
  all_goals (try (rename_i hh; revert hh; crush1))
  all_goals (try (rename_i hh; revert hh; crush1))))

theorem projM_ext (g : G) (s : St) (t : Ty) (ws : List Word) :
    ∀ r ∈ projM g s t ws, Ext s r.1 := by
  unfold projM
  crush

theorem injM_ext (g : G) (s : St) (t : Ty) (j : Nat) (p : List Word) :
    ∀ r ∈ injM g s t j p, Ext s r.1 := by
  unfold injM
  crush

theorem rmw_ext {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts} {s : St}
    {r0 r1 r2 : Word} {dst : WeakMem.Reg} {a : Address} {cmp : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs (mth s r0 r1 r2) dst a cmp newv deps acq rel) :
    MemExt mem mem' ∧ ∀ t ∈ th'.promises, t ∈ s.promises :=
  Promises.Sim.stepRmw_ext k arch mem pairs _ dst a cmp newv deps acq rel h

theorem evalOp_ext (g : G) (env : Env) (σs : List Ty) (s : St) (op : Op) :
    ∀ r ∈ evalOp g env σs s op, Ext s r.1 := by
  cases op <;> simp only [evalOp]
  all_goals crush
  all_goals first
    | exact Ext.trans (projM_ext _ _ _ _ _ (by assumption)) (injM_ext _ _ _ _ _ _ (by assumption))
    | exact ⟨(rmw_ext (by assumption)).1, (rmw_ext (by assumption)).2⟩

/-! ### Thread steps, promise steps, machine steps -/

theorem enter_promises {g : G} {th th' : TTh} {f : String} {ts : List Ty} {a : At}
    (h : enter g th f ts a = some th') : th'.promises = th.promises := by
  unfold enter at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.exists] at h
  obtain ⟨_, _, _, _, _, rfl⟩ := h
  rfl

theorem enter_ext {g : G} {mem : Memory} {pairs : List Ts} {th th0 th' : TTh} {f : String}
    {ts : List Ty} {a : At} (h : enter g th0 f ts a = some th') (hp : th0.promises = th.promises) :
    Ext (stOf mem pairs th) (stOf mem pairs th') :=
  ⟨Promises.Sim.MemExt.refl _, fun t ht => by
    have := enter_promises h
    simp only [stOf] at ht ⊢
    rw [this, hp] at ht
    exact ht⟩

theorem rmwPair_ext {arch : Arch} {mem : Memory} {pairs : List Ts} {s : St}
    {r0 r1 r2 : Word} {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : Val} {n0 n1 : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs (mth s r0 r1 r2) d0 d1 a c0 c1 n0 n1 deps acq rel) :
    MemExt mem mem' ∧ ∀ t ∈ th'.promises, t ∈ s.promises :=
  Promises.Sim.stepRmwPair_ext arch mem pairs _ d0 d1 a c0 c1 n0 n1 deps acq rel h

/-- (D1) `region` fences: its outcome's state is the old one behind the fence. -/
theorem fenceS_withS_ext (mem : Memory) (pairs : List Ts) (th X : TTh) (f : WeakMem.Fence) :
    Ext (stOf mem pairs th) (stOf (fenceS (stOf mem pairs th) f).mem (fenceS (stOf mem pairs th) f).pairs
      (withS X (fenceS (stOf mem pairs th) f))) := by
  have e : ∀ s : St, stOf s.mem s.pairs (withS X s) = s := fun s => by cases s; rfl
  rw [e]; exact fenceS_ext _ _

/-- **A1.**  A thread step only extends memory and only discharges promises. -/
theorem tstep_ext (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) :
    ∀ r ∈ tstep g mem pairs th, Ext (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := by
  unfold tstep
  crush
  all_goals first
    | exact evalOp_ext _ _ _ _ _ _ (by assumption)
    | exact Ext.trans (projM_ext _ _ _ _ _ (by assumption)) (injM_ext _ _ _ _ _ _ (by assumption))
    | exact enter_ext (by assumption) (by rfl)
    | exact ⟨(rmw_ext (by assumption)).1, (rmw_ext (by assumption)).2⟩
    | exact ⟨(rmwPair_ext (by assumption)).1, (rmwPair_ext (by assumption)).2⟩
    | exact fenceS_withS_ext _ _ _ _ _


theorem threadSteps_ext {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (h : c' ∈ threadSteps p k arch c i) : MemExt c.mem c'.mem := by
  unfold threadSteps at h
  split at h
  · simp at h
  · simp only [List.mem_map] at h
    obtain ⟨⟨mem, pairs, th'⟩, hin, rfl⟩ := h
    exact (tstep_ext _ _ _ _ _ hin).mem

theorem promise_ext (c : Cfg) (i : Nat) (a : Address) (v : Val) (w : Ts) :
    MemExt c.mem (promise c i a v w).mem := by
  unfold promise
  split
  · exact Promises.Sim.MemExt.refl _
  · exact Promises.Sim.MemExt.push _ _

theorem Step_ext {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg}
    (h : Step p k arch c c') : MemExt c.mem c'.mem := by
  cases h with
  | thread i hs _ => exact threadSteps_ext hs
  | prom i a v w _ _ _ => exact promise_ext c i a v w

/-! ## A2 Memory is constant on a class -/

theorem memExt_antisymm {m m' : Memory} (h : MemExt m m') (h' : MemExt m' m) : m = m' := by
  have hs : m.size = m'.size := Nat.le_antisymm h.size h'.size
  apply Array.ext_getElem?
  intro t
  by_cases ht : t < m.size
  · exact (h.get t ht).symm
  · have h1 : m[t]? = none := by simp [Nat.le_of_not_lt ht]
    have h2 : m'[t]? = none := by simp [← hs, Nat.le_of_not_lt ht]
    rw [h1, h2]

/-- Reachability by machine steps. -/
inductive Reach (p : Prog) (k : Promises.Knobs) (arch : Arch) : Cfg → Cfg → Prop
  | refl (c) : Reach p k arch c c
  | step {c c' c''} : Step p k arch c c' → Reach p k arch c' c'' → Reach p k arch c c''

theorem Reach_ext {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg}
    (h : Reach p k arch c c') : MemExt c.mem c'.mem := by
  induction h with
  | refl c => exact Promises.Sim.MemExt.refl _
  | step hs _ ih => exact Promises.Sim.MemExt.trans (Step_ext hs) ih

/-- **A2.**  Two configurations that reach each other have the same memory. -/
theorem reach_mem_eq {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg}
    (h : Reach p k arch c c') (h' : Reach p k arch c' c) : c'.mem = c.mem :=
  (memExt_antisymm (Reach_ext h) (Reach_ext h')).symm

/-- A crash step (`TermLive.crashCfg`'s shape) leaves memory alone. -/
theorem crash_mem (c : Cfg) (i : Nat) (th : TTh) :
    ({ c with ths := c.ths.set! i th } : Cfg).mem = c.mem := rfl

/-! ## A3 A class has no fresh `cas` -/

theorem not_hidden_of_latest {mem : Memory} {a : Address} {t : Ts}
    (hb : WeakMem.betweenAt mem a t mem.size = false) (bound : Ts) :
    WeakMem.hiddenFrom mem a t bound = false := by
  unfold WeakMem.hiddenFrom
  rw [List.any_eq_false]
  intro t' _
  unfold WeakMem.betweenAt at hb
  rw [List.any_eq_false] at hb
  by_cases ht' : t' < mem.size
  · have := hb t' (List.mem_range.2 ht')
    simpa [ht'] using this
  · have : mem[t']? = none := by simp [Nat.le_of_not_lt ht']
    simp [this]

/-- An RMW whose comparand is the coherence-latest value of `a` can append. -/
theorem stepRmw_latest_appends (k : Promises.Knobs) (arch : Arch) (mem : Memory) (pairs : List Ts)
    (th : Promises.Thread) (dst : WeakMem.Reg) (a : Address) (e : Val) (newv : WeakMem.Expr) (deps : List WeakMem.Reg)
    (acq rel : Bool) (hl : Promises.LatestIs mem a e) :
    ∃ mem' th', (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a (.cas e) newv deps acq rel ∧
      mem'.size = mem.size + 1 := by
  obtain ⟨t, m, hm, hloc, hv, hb⟩ := hl
  have ht : t < mem.size := by
    rcases Nat.lt_or_ge t mem.size with h | h
    · exact h
    · simp [Nat.not_lt.2 h] at hm
  have hread : ∀ bound, WeakMem.readable mem a t bound = true := by
    intro bound
    simp [WeakMem.readable, hm, hloc, not_hidden_of_latest hb bound]
  have hm! : mem[t]! = m := by simp [getElem!_def, hm]
  have hadj : WeakMem.rmwAdjacent mem a t mem.size = true := by
    simp [WeakMem.rmwAdjacent, ht, hb]
  have hsucc : WeakMem.rmwSucceeds (.cas e) m.val = true := by simp [WeakMem.rmwSucceeds, WeakMem.RmwKind.succeeds, hv]
  simp only [Promises.stepRmw, Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range]
  exact ⟨_, _, ⟨t, ⟨ht, hread _⟩, by
    simp only [hm!, hsucc, hadj, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
    exact List.mem_append_left _ (List.mem_singleton_self _)⟩, by simp⟩

/-- **A3, one thread.**  A thread at a `cas` whose expected value is the
coherence-latest value of the word has a step that appends a message. -/
theorem tstep_cas_appends (g : G) (mem : Memory) (pairs : List Ts) (th : TTh)
    {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr} {tw te tv : Ty} {pw ew nw : Word}
    {b : Address} (hterm : th.term = .cas acq rel w e v t ok fail)
    (hw : evalAt th.env w = some (tw, [pw])) (he : evalAt th.env e = some (te, [ew]))
    (hv : evalAt th.env v = some (tv, [nw])) (hb : addrOf pw = some b)
    (hl : Promises.LatestIs mem b ew.val) :
    ∃ r ∈ tstep g mem pairs th, r.1.size = mem.size + 1 := by
  obtain ⟨mem', th', hin, hsz⟩ := stepRmw_latest_appends g.k g.arch mem pairs
    (mth (stOf mem pairs th) pw nw nw) 1 b ew.val (dataE 1 nw) [0] acq rel hl
  unfold tstep
  simp only [hterm, hw, he, hv, hb]
  exact ⟨_, List.mem_map.2 ⟨(mem', th'), hin, rfl⟩, hsz⟩

/-- **A3.**  If no step of thread `i` changes memory (as inside a class that
thread steps do not leave, by A2), then a `cas` thread `i` waits at compares
against a value that is not the latest: the class's spin is on a stale value. -/
theorem stale_cas {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {th : TTh}
    {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr} {tw te tv : Ty} {pw ew nw : Word}
    {b : Address} (hth : c.ths[i]? = some th) (hterm : th.term = .cas acq rel w e v t ok fail)
    (hw : evalAt th.env w = some (tw, [pw])) (he : evalAt th.env e = some (te, [ew]))
    (hv : evalAt th.env v = some (tv, [nw])) (hb : addrOf pw = some b)
    (hstay : ∀ c' ∈ threadSteps p k arch c i, c'.mem = c.mem) :
    ¬ Promises.LatestIs c.mem b ew.val := by
  intro hl
  obtain ⟨⟨m', p', t'⟩, hr, hsz⟩ := tstep_cas_appends (gOf p k arch c i) c.mem c.pairs th hterm hw he hv hb hl
  have hin : ({ c with mem := m', pairs := p', ths := c.ths.set! i t' } : Cfg) ∈ threadSteps p k arch c i := by
    simp only [threadSteps, hth]
    exact List.mem_map.2 ⟨(m', p', t'), hr, rfl⟩
  have := hstay _ hin
  simp only at this hsz
  rw [this] at hsz
  omega

/-! ## A4 An inside load reads old -/

/-- A load that leaves the coherence view at its address where it was read a
message at or below that view.  Inside a class, where views do not move, a
load therefore never reads a write newer than what the thread has seen. -/
theorem stepLoad_stale {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool}
    (h : th' ∈ Promises.stepLoad arch mem pairs th dst a deps acq)
    (hcoh : th'.vs.coh a = th.vs.coh a) : (th'.regs dst).rts ≤ th.vs.coh a := by
  simp only [Promises.stepLoad, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨t, _, rfl⟩ := h
  dsimp only at hcoh ⊢
  simp only [eq_self, ite_true] at hcoh ⊢
  rw [← hcoh]
  exact Nat.le_max_right _ _

/-! ## B Robust words need no token -/

open CoreTyping in
theorem enumFrom_mem {α : Type} : ∀ (l : List α) (i n : Nat) (a : α),
    l[n]? = some a → (n + i, a) ∈ enumFrom l i
  | [], _, _, _, h => by simp at h
  | b :: bs, i, 0, a, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [enumFrom]
  | b :: bs, i, n + 1, a, h => by
      simp only [List.getElem?_cons_succ] at h
      have := enumFrom_mem bs (i + 1) n a h
      simp only [enumFrom, List.mem_cons]
      right
      rw [show n + 1 + i = n + (i + 1) by omega]
      exact this

/-- Under `robust` every state of a well-formed protocol holds its region. -/
theorem robust_holds {P : Proto} (hpwf : pwf P = true) (hrob : P.robust = true) {c : Nat}
    {cl : Clause} (hc : P.clauses[c]? = some cl) : cl.holds = true := by
  simp only [pwf, Bool.and_eq_true] at hpwf
  obtain ⟨⟨⟨⟨_, hF⟩, _⟩, _⟩, _⟩ := hpwf
  simp only [hrob, Bool.not_true, Bool.false_or, List.isEmpty_iff] at hF
  cases hh : cl.holds
  · exfalso
    have hmem : c ∈ heldStates P := by
      unfold heldStates
      rw [List.mem_filterMap]
      exact ⟨(c, cl), by simpa using enumFrom_mem P.clauses 0 c cl hc, by simp [hh]⟩
    rw [hF] at hmem
    simp at hmem
  · rfl

theorem holds_contra {P : Proto} (hall : ∀ (c : Nat) (cl : CoreLang.Clause), P.clauses[c]? = some cl → cl.holds = true)
    {c : Nat} {cl : CoreLang.Clause} (hh : cl.holds = false) (hc : P.clauses[c]? = some cl) : False := by
  rw [hall c cl hc] at hh
  cases hh

open CoreTyping in
/-- **B, stores.**  No `store` on a robust word types: every word-store rule
starts from a held state, and a robust protocol has none. -/
theorem robust_noStore {p : Prog} {cx c' : Cx} {x : String} {rel : Bool} {a v : At}
    {tok : Option At} {t : Ty} {r : Idx} {P : Proto} (h : OpT p cx x (.store rel a v tok) c')
    (ht : cx.peek a = .ok t) (hw : wordOf t = some (r, P)) (hpwf : pwf P = true)
    (hrob : P.robust = true) : False := by
  have hall : ∀ (c : Nat) (cl : CoreLang.Clause), P.clauses[c]? = some cl → cl.holds = true :=
    fun _ _ h => robust_holds hpwf hrob h
  revert ht hw
  cases h
  all_goals (
    have hpk := ‹Cx.peek _ _ = _›
    have hwo := ‹wordOf _ = _›
    intro ht hw
    rw [ht] at hpk
    cases hpk
    rw [hw] at hwo
    cases hwo)
  all_goals exact holds_contra hall (by assumption) (by assumption)

open CoreTyping in
/-- **B, `cas`.**  A typed `cas` on a robust word is `casShare` or `casEpoch`:
it moves at most read shares (`LendCx`) or enters an epoch, and never mints or
needs a region token (`casTake`'s target is held, which robust forbids). -/
theorem robust_cas {p : Prog} {cx : Cx} {acq rel : Bool} {w e v : At} {t : String}
    {ok fail : Expr} {tw : Ty} {r : Idx} {P : Proto}
    (h : Typed p cx (.cas acq rel w e v t ok fail))
    (ht : cx.peek w = .ok tw) (hw : wordOf tw = some (r, P)) (hpwf : pwf P = true)
    (hrob : P.robust = true) :
    (∃ c k c' k' c₂, LendCx cx acq rel r t P c k c' k' c₂ ∧ Typed p c₂ ok) ∨
      (∃ j c₂, P.epoch = true ∧ cx.bind t (.tokE r (.word P) j) = .ok c₂ ∧ Typed p c₂ ok) := by
  have hall : ∀ (c : Nat) (cl : CoreLang.Clause), P.clauses[c]? = some cl → cl.holds = true :=
    fun _ _ h => robust_holds hpwf hrob h
  revert ht hw
  cases h
  all_goals (
    have hpk := ‹Cx.peek _ w = _›
    have hwo := ‹wordOf _ = _›
    intro ht hw
    rw [ht] at hpk
    cases hpk
    rw [hw] at hwo
    cases hwo)
  · exact Or.inl ⟨_, _, _, _, _, ‹_›, ‹_›⟩
  · exact (holds_contra hall (by assumption) (by assumption)).elim
  · exact Or.inr ⟨_, _, ‹_›, ‹_›, ‹_›⟩

/-! ## A4, lifted: coherence views only rise

Inside a class, A4's premise — the stepping thread's coherence view did not
move — holds automatically, because coherence views only rise along machine
steps, so two configurations that reach each other have the same ones.  "Only
rise" needs one invariant: each view is `0` or sits on a message at its own
address (`CohAt`).  Without it a fresh allocation could set a view below where
it was, and a `casp` fulfilling a promise could set the second word's view
below an older one; with it, both are ruled out (the old view is at most the
memory size, and a readable message is never below the view). -/

/-- `omega` does not see through `WeakMem.Ts`; unfold it first. -/
macro "tomega" : tactic => `(tactic| ((try simp only [WeakMem.Ts] at *) <;> omega))

/-- Each coherence view is `0` or the timestamp of a message at its address. -/
def CohAt (mem : Memory) (vs : VState) : Prop :=
  ∀ b, vs.coh b = 0 ∨ ∃ m, mem[vs.coh b]? = some m ∧ m.loc = b

theorem lt_of_get {α : Type} {xs : Array α} {i : Nat} {x : α} (h : xs[i]? = some x) : i < xs.size := by
  rcases Nat.lt_or_ge i xs.size with hi | hi
  · exact hi
  · simp [Nat.not_lt.2 hi] at h

theorem CohAt.le_size {mem : Memory} {vs : VState} (h : CohAt mem vs) (b : Address) :
    vs.coh b ≤ mem.size := by
  rcases h b with h0 | ⟨m, hm, _⟩
  · tomega
  · exact Nat.le_of_lt (lt_of_get hm)

theorem get_ext {mem mem' : Memory} (he : MemExt mem mem') {i : Nat} {m : Msg} (h : mem[i]? = some m) :
    mem'[i]? = some m := by
  rw [he.get i (lt_of_get h)]; exact h

theorem CohAt.ext {mem mem' : Memory} {vs : VState} (he : MemExt mem mem') (h : CohAt mem vs) :
    CohAt mem' vs := fun b => (h b).imp id fun ⟨m, hm, hl⟩ => ⟨m, get_ext he hm, hl⟩

/-- One coherence view's move from `x` to `x'`: it stays or lands on a message
at its address, and it does not go down. -/
def Moves (mem' : Memory) (b : Address) (x x' : Ts) : Prop :=
  (x' = x ∨ ∃ m, mem'[x']? = some m ∧ m.loc = b) ∧ x ≤ x'

theorem cohStep {mem mem' : Memory} {vs vs' : VState} (hc : CohAt mem vs) (he : MemExt mem mem')
    (h : ∀ b, Moves mem' b (vs.coh b) (vs'.coh b)) : CohAt mem' vs' ∧ ∀ b, vs.coh b ≤ vs'.coh b := by
  refine ⟨fun b => ?_, fun b => (h b).2⟩
  rcases (h b).1 with e | hm
  · rw [e]; exact CohAt.ext he hc b
  · exact Or.inr hm

theorem Moves.stay {mem' : Memory} {b : Address} {x : Ts} : Moves mem' b x x :=
  ⟨Or.inl rfl, Nat.le_refl _⟩

theorem Moves.max {mem' : Memory} {b : Address} {x t : Ts} {m : Msg} (hm : mem'[t]? = some m)
    (hl : m.loc = b) : Moves mem' b x (max x t) := by
  refine ⟨?_, Nat.le_max_left _ _⟩
  rcases Nat.le_total x t with h | h
  · exact Or.inr ⟨m, by rw [Nat.max_eq_right h]; exact hm, hl⟩
  · exact Or.inl (Nat.max_eq_left h)

theorem Moves.to {mem' : Memory} {b : Address} {x t : Ts} {m : Msg} (hm : mem'[t]? = some m)
    (hl : m.loc = b) (hle : x ≤ t) : Moves mem' b x t := ⟨Or.inr ⟨m, hm, hl⟩, hle⟩

theorem loc_of_readable {mem : Memory} {a : Address} {t bound : Ts}
    (h : WeakMem.readable mem a t bound = true) : ∃ m, mem[t]? = some m ∧ m.loc = a := by
  unfold WeakMem.readable at h
  cases hm : mem[t]? with
  | none => simp [hm] at h
  | some m => simp [hm] at h; exact ⟨m, rfl, h.1⟩

theorem coh_le_rb (arch : Arch) (vs : VState) (dv : Ts) (a : Address) :
    vs.coh a ≤ Promises.readBoundOf arch vs dv a := by
  simp only [Promises.readBoundOf]
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

/-- A readable message is never below the view (given `CohAt`). -/
theorem coh_le_of_readable {mem : Memory} {vs : VState} {a : Address} {t bound : Ts}
    (hc : CohAt mem vs) (hb : vs.coh a ≤ bound) (hr : WeakMem.readable mem a t bound = true) :
    vs.coh a ≤ t := by
  rcases hc a with h0 | ⟨m, hm, hloc⟩
  · tomega
  · apply Nat.le_of_not_lt
    intro hlt
    have hh : WeakMem.hiddenFrom mem a t bound = true := by
      unfold WeakMem.hiddenFrom
      rw [List.any_eq_true]
      exact ⟨vs.coh a, List.mem_range.2 (Nat.lt_succ_of_le hb), by simp [hlt, hm, hloc]⟩
    simp [WeakMem.readable, hh] at hr

theorem stepFence_coh (th : Promises.Thread) (f : WeakMem.Fence) :
    (Promises.stepFence th f).vs.coh = th.vs.coh := by
  cases f <;> rfl

theorem ite_fence_coh {c : Prop} [Decidable c] (th : Promises.Thread) (f : WeakMem.Fence) :
    (if c then Promises.stepFence th f else th).vs.coh = th.vs.coh := by
  split
  · exact stepFence_coh th f
  · rfl

theorem coh_le_storeOb {k : Promises.Knobs} {arch : Arch} {th : Promises.Thread} {a : Address}
    {e : WeakMem.Expr} {deps : List WeakMem.Reg} : th.vs.coh a ≤ Promises.storeOb k arch th a e deps := by
  unfold Promises.storeOb
  dsimp only
  split <;> tomega

theorem push2_fst (mem : Memory) (x y : Msg) : ((mem.push x).push y)[mem.size]? = some x := by
  simp [Array.getElem?_push]

theorem push2_snd (mem : Memory) (x y : Msg) : ((mem.push x).push y)[mem.size + 1]? = some y := by
  simp only [Array.getElem?_push, Array.size_push, eq_self, ↓reduceIte]

/-! ### The machine rules -/

theorem stepLoad_coh {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool}
    (h : th' ∈ Promises.stepLoad arch mem pairs th dst a deps acq) (hc : CohAt mem th.vs) :
    CohAt mem th'.vs ∧ ∀ b, th.vs.coh b ≤ th'.vs.coh b := by
  simp only [Promises.stepLoad, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨t, ⟨_, hr⟩, rfl⟩ := h
  obtain ⟨m, hm, hl⟩ := loc_of_readable hr
  refine cohStep hc (Promises.Sim.MemExt.refl _) fun b => ?_
  by_cases hb : b = a
  · subst hb; simp only [eq_self, ↓reduceIte]; exact Moves.max hm hl
  · simp only [hb, ↓reduceIte]; exact Moves.stay

theorem stepLoadPair_coh {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool}
    (h : th' ∈ Promises.stepLoadPair arch mem pairs th d0 d1 a deps acq) (hc : CohAt mem th.vs) :
    CohAt mem th'.vs ∧ ∀ b, th.vs.coh b ≤ th'.vs.coh b := by
  simp only [Promises.stepLoadPair, List.mem_flatMap, List.mem_filterMap, List.mem_filter,
    List.mem_range] at h
  obtain ⟨t0, ⟨_, hr0⟩, t1, ⟨_, hr1⟩, hs⟩ := h
  split at hs
  · cases hs
  · cases hs
    obtain ⟨m0, hm0, hl0⟩ := loc_of_readable hr0
    obtain ⟨m1, hm1, hl1⟩ := loc_of_readable hr1
    refine cohStep hc (Promises.Sim.MemExt.refl _) fun b => ?_
    by_cases hb : b = a
    · subst hb; simp only [eq_self, ↓reduceIte]; exact Moves.max hm0 hl0
    · by_cases hb1 : b = a.next
      · subst hb1; simp only [hb, eq_self, ↓reduceIte]; exact Moves.max hm1 hl1
      · simp only [hb, hb1, ↓reduceIte]; exact Moves.stay

theorem stepStore_coh {k : Promises.Knobs} {arch : Arch} {mem : Memory} {th : Promises.Thread}
    {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool} {mem' : Memory}
    {th' : Promises.Thread} (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel)
    (hc : CohAt mem th.vs) : CohAt mem' th'.vs ∧ ∀ b, th.vs.coh b ≤ th'.vs.coh b := by
  simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
  rcases h with h | ⟨t, _, hf⟩
  · cases h
    refine cohStep hc (Promises.Sim.MemExt.push _ _) fun b => ?_
    by_cases hb : b = a
    · subst hb; simp only [eq_self, ↓reduceIte]
      exact Moves.to Array.getElem?_push_size rfl (hc.le_size _)
    · simp only [hb, ↓reduceIte]; exact Moves.stay
  · split at hf
    · cases hf
    · rename_i m hm
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hf
      obtain ⟨hcond, hf⟩ := hf
      cases hf
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
      obtain ⟨⟨⟨hl, _⟩, _⟩, hob⟩ := hcond
      refine cohStep hc (Promises.Sim.MemExt.refl _) fun b => ?_
      by_cases hb : b = a
      · subst hb; simp only [eq_self, ↓reduceIte]
        exact Moves.to hm hl (Nat.le_of_lt (Nat.lt_of_le_of_lt coh_le_storeOb hob))
      · simp only [hb, ↓reduceIte]; exact Moves.stay

theorem stepStorePair_coh {mem : Memory} {pairs : List Ts} {th : Promises.Thread} {a : Address}
    {e0 e1 : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool} (hc : CohAt mem th.vs) :
    CohAt (Promises.stepStorePair mem pairs th a e0 e1 deps rel).1
      (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2.vs ∧
    ∀ b, th.vs.coh b ≤ (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2.vs.coh b := by
  refine cohStep hc (Promises.Sim.MemExt.trans (Promises.Sim.MemExt.push _ _)
    (Promises.Sim.MemExt.push _ _)) fun b => ?_
  simp only [Promises.stepStorePair]
  by_cases hb : b = a
  · subst hb; simp only [eq_self, ↓reduceIte]
    exact Moves.to (push2_fst _ _ _) rfl (hc.le_size _)
  · by_cases hb1 : b = a.next
    · subst hb1; simp only [hb, eq_self, ↓reduceIte]
      exact Moves.to (push2_snd _ _ _) rfl (by have := hc.le_size a.next; tomega)
    · simp only [hb, hb1, ↓reduceIte]; exact Moves.stay

theorem stepRmw_coh_at {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {cmp : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a cmp newv deps acq rel)
    (hc : CohAt mem th.vs) : CohAt mem' th'.vs ∧ ∀ b, th.vs.coh b ≤ th'.vs.coh b := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t, ⟨_, hr⟩, hbody⟩ := h
  obtain ⟨m, hm, hl⟩ := loc_of_readable hr
  split at hbody
  · rw [List.mem_singleton] at hbody
    cases hbody
    refine cohStep hc (Promises.Sim.MemExt.refl _) fun b => ?_
    rw [ite_fence_coh]
    by_cases hb : b = a
    · subst hb; simp only [eq_self, ↓reduceIte]; exact Moves.max hm hl
    · simp only [hb, ↓reduceIte]; exact Moves.stay
  · rw [List.mem_append] at hbody
    rcases hbody with happ | hful
    · split at happ
      · rw [List.mem_singleton] at happ
        cases happ
        refine cohStep hc (Promises.Sim.MemExt.push _ _) fun b => ?_
        rw [ite_fence_coh]
        by_cases hb : b = a
        · subst hb; simp only [eq_self, ↓reduceIte]
          exact Moves.to Array.getElem?_push_size rfl (hc.le_size _)
        · simp only [hb, ↓reduceIte]; exact Moves.stay
      · simp at happ
    · obtain ⟨tw, _, hft⟩ := List.mem_filterMap.1 hful
      split at hft
      · cases hft
      · rename_i pm hpm
        simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hft
        obtain ⟨hcond, hft⟩ := hft
        cases hft
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
        obtain ⟨⟨⟨⟨hl', _⟩, _⟩, hob⟩, _⟩ := hcond
        refine cohStep hc (Promises.Sim.MemExt.refl _) fun b => ?_
        rw [ite_fence_coh]
        by_cases hb : b = a
        · subst hb
          simp only [eq_self, ↓reduceIte] at hob ⊢
          refine Moves.to hpm hl' ?_
          revert hob; split <;> intro hob <;> tomega
        · simp only [hb, ↓reduceIte]; exact Moves.stay

theorem stepRmw_coh {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {cmp : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a cmp newv deps acq rel)
    (hc : CohAt mem th.vs) : CohAt mem' th'.vs ∧ ∀ b, th.vs.coh b ≤ th'.vs.coh b :=
  by
  have hx := stepRmw_coh_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (by intro b; rw [ite_fence_coh]; exact hc b)
  rw [ite_fence_coh] at hx
  exact hx

theorem stepRmwPair_coh_at {arch : Arch} {mem : Memory} {pairs : List Ts} {th : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : Val} {n0 n1 : WeakMem.Expr} {deps : List WeakMem.Reg}
    {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPairAt arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel)
    (hc : CohAt mem th.vs) : CohAt mem' th'.vs ∧ ∀ b, th.vs.coh b ≤ th'.vs.coh b := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, ⟨_, hr0⟩, t1, ⟨_, hr1⟩, hbody⟩ := h
  obtain ⟨m0, hm0, hl0⟩ := loc_of_readable hr0
  obtain ⟨m1, hm1, hl1⟩ := loc_of_readable hr1
  have h1 : th.vs.coh a.next ≤ t1 := coh_le_of_readable hc (coh_le_rb _ _ _ _) hr1
  split at hbody
  · simp at hbody
  · split at hbody
    · rw [List.mem_singleton] at hbody
      cases hbody
      refine cohStep hc (Promises.Sim.MemExt.refl _) fun b => ?_
      rw [ite_fence_coh]
      by_cases hb : b = a
      · subst hb; simp only [eq_self, ↓reduceIte]; exact Moves.max hm0 hl0
      · by_cases hb1 : b = a.next
        · subst hb1; simp only [hb, eq_self, ↓reduceIte]; exact Moves.max hm1 hl1
        · simp only [hb, hb1, ↓reduceIte]; exact Moves.stay
    · rw [List.mem_append] at hbody
      rcases hbody with happ | hful
      · split at happ
        · rw [List.mem_singleton] at happ
          cases happ
          refine cohStep hc (Promises.Sim.MemExt.trans (Promises.Sim.MemExt.push _ _)
            (Promises.Sim.MemExt.push _ _)) fun b => ?_
          rw [ite_fence_coh]
          by_cases hb : b = a
          · subst hb; simp only [eq_self, ↓reduceIte]
            exact Moves.to (push2_fst _ _ _) rfl (hc.le_size _)
          · by_cases hb1 : b = a.next
            · subst hb1; simp only [hb, eq_self, ↓reduceIte]
              exact Moves.to (push2_snd _ _ _) rfl (by have := hc.le_size a.next; tomega)
            · simp only [hb, hb1, ↓reduceIte]; exact Moves.stay
        · simp at happ
      · obtain ⟨tw, _, hft⟩ := List.mem_filterMap.1 hful
        split at hft
        · rename_i pm0 pm1 hpm0 hpm1
          simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hft
          obtain ⟨hcond, hft⟩ := hft
          · cases hft
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
            obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hla⟩, _⟩, _⟩, hlb⟩, _⟩, _⟩, hob⟩, _⟩, hadj1⟩ := hcond
            have hlt1 : t1 < tw + 1 := by
              simp [WeakMem.rmwAdjacent] at hadj1; exact hadj1.1
            refine cohStep hc (Promises.Sim.MemExt.refl _) fun b => ?_
            rw [ite_fence_coh]
            by_cases hb : b = a
            · subst hb
              simp only [eq_self, ↓reduceIte] at hob ⊢
              refine Moves.to hpm0 hla ?_
              revert hob; split <;> intro hob <;> tomega
            · by_cases hb1 : b = a.next
              · subst hb1; simp only [hb, eq_self, ↓reduceIte]
                exact Moves.to hpm1 hlb (by tomega)
              · simp only [hb, hb1, ↓reduceIte]; exact Moves.stay
        · cases hft

theorem stepRmwPair_coh {arch : Arch} {mem : Memory} {pairs : List Ts} {th : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : Val} {n0 n1 : WeakMem.Expr} {deps : List WeakMem.Reg}
    {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel)
    (hc : CohAt mem th.vs) : CohAt mem' th'.vs ∧ ∀ b, th.vs.coh b ≤ th'.vs.coh b :=
  by
  have hx := stepRmwPair_coh_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (by intro b; rw [ite_fence_coh]; exact hc b)
  rw [ite_fence_coh] at hx
  exact hx

/-! ### The state helpers -/

/-- `s'` keeps `CohAt` and lowers no coherence view. -/
def Mono (s s' : St) : Prop :=
  CohAt s.mem s.vs → CohAt s'.mem s'.vs ∧ ∀ b, s.vs.coh b ≤ s'.vs.coh b

@[simp] theorem Mono.refl' (s : St) : Mono s s := fun h => ⟨h, fun _ => Nat.le_refl _⟩

theorem Mono.trans {s1 s2 s3 : St} (a : Mono s1 s2) (b : Mono s2 s3) : Mono s1 s3 := fun h =>
  let ⟨h2, l2⟩ := a h
  let ⟨h3, l3⟩ := b h2
  ⟨h3, fun x => Nat.le_trans (l2 x) (l3 x)⟩

@[simp] theorem fenceS_mono (s : St) (f : WeakMem.Fence) : Mono s (fenceS s f) := fun h => by
  have e : (fenceS s f).vs.coh = s.vs.coh := stepFence_coh _ f
  exact ⟨fun b => by rw [e]; exact h b, fun b => by rw [e]; exact Nat.le_refl _⟩

theorem loadUnits_mono (arch : Arch) (pw : Word) (a : Address) (acq : Bool) :
    ∀ (us : List Acc) (k : Nat) (s : St) {s' : St} {ws : List Word},
    (s', ws) ∈ loadUnits arch pw a acq us k s → Mono s s'
  | [], k, s, s', ws, h => by
      simp only [loadUnits, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Mono.refl' _
  | .one :: us, k, s, s', ws, h => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at h
      obtain ⟨th, hth, ⟨s2, ws2⟩, hin, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      refine Mono.trans ?_ (loadUnits_mono arch pw a acq us _ _ hin)
      exact fun hc => stepLoad_coh hth hc
  | .two :: us, k, s, s', ws, h => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at h
      obtain ⟨th, hth, ⟨s2, ws2⟩, hin, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      refine Mono.trans ?_ (loadUnits_mono arch pw a acq us _ _ hin)
      exact fun hc => stepLoadPair_coh hth hc

theorem storeUnits_mono (k : Promises.Knobs) (arch : Arch) (pw : Word) (a : Address) (rel : Bool) :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s : St) {s' : St},
    s' ∈ storeUnits k arch pw a rel us ws i s → Mono s s'
  | [], ws, i, s, s', h => by
      simp only [storeUnits, List.mem_singleton] at h
      subst h; exact Mono.refl' _
  | .one :: us, [], i, s, s', h => by simp [storeUnits] at h
  | .one :: us, w :: ws, i, s, s', h => by
      simp only [storeUnits, List.mem_flatMap] at h
      obtain ⟨⟨mem', th⟩, hst, hin⟩ := h
      refine Mono.trans ?_ (storeUnits_mono k arch pw a rel us ws _ _ hin)
      exact fun hc => stepStore_coh hst hc
  | .two :: us, [], i, s, s', h => by simp [storeUnits] at h
  | .two :: us, [_], i, s, s', h => by simp [storeUnits] at h
  | .two :: us, w0 :: w1 :: ws, i, s, s', h => by
      have hp := stepStorePair_coh (mem := s.mem) (pairs := s.pairs) (th := mth s pw w0 w1) (a := offs a i)
        (e0 := dataE 1 w0) (e1 := dataE 2 w1) (deps := [0]) (rel := rel)
      unfold storeUnits at h
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i)
        (dataE 1 w0) (dataE 2 w1) [0] rel = q at h hp
      obtain ⟨mem', pairs', th⟩ := q
      refine Mono.trans ?_ (storeUnits_mono k arch pw a rel us ws _ _ h)
      exact fun hc => hp hc

theorem fold_get (f : Nat → Msg) : ∀ (l : List Nat) (m : Memory) (i : Nat) (hi : i < l.length),
    (l.foldl (fun m j => m.push (f j)) m)[m.size + i]? = some (f l[i])
  | [], m, i, hi => by simp at hi
  | j :: l, m, 0, _ => by
      simp only [List.foldl_cons, List.getElem_cons_zero, Nat.add_zero]
      exact get_ext (TermArch.fold_push_ext f l _) Array.getElem?_push_size
  | j :: l, m, i + 1, hi => by
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have := fold_get f l (m.push (f j)) i (by simp at hi; omega)
      rw [Array.size_push] at this
      rw [show m.size + (i + 1) = m.size + 1 + i by omega]
      exact this

/-- The views `new`/`newBuf` set: each fresh cell's sits on its first message,
which is above every old view. -/
theorem allocCoh {mem : Memory} {vs : VState} (hc : CohAt mem vs) (lbl : AllocLabel) (n : Nat)
    (g : Nat → Val) :
    CohAt ((List.range n).foldl (fun m j => m.push ⟨offs ⟨lbl, 0⟩ j, g j, 0⟩) mem)
      { vs with coh := fun b => if b.label = lbl ∧ b.offset < n then mem.size + b.offset else vs.coh b } ∧
    ∀ b, vs.coh b ≤ (if b.label = lbl ∧ b.offset < n then mem.size + b.offset else vs.coh b) := by
  refine cohStep hc (TermArch.fold_push_ext _ _ _) fun b => ?_
  show Moves _ b (vs.coh b) (if b.label = lbl ∧ b.offset < n then mem.size + b.offset else vs.coh b)
  split
  · rename_i hb
    obtain ⟨hl, ho⟩ := hb
    refine Moves.to (fold_get _ _ _ _ (by simpa using ho)) ?_
      (Nat.le_trans (hc.le_size b) (Nat.le_add_right _ _))
    simp only [List.getElem_range, offs]
    cases b; simp_all
  · exact Moves.stay

theorem alloc_mono {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s s' : St} {pw : Word} (h : (s', pw) ∈ alloc k arch lbl us ws s) : Mono s s' := by
  simp only [alloc, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨s2, hs2, rfl, rfl⟩ := h
  refine Mono.trans ?_ (storeUnits_mono k arch _ _ false us ws 0 _ hs2)
  exact fun hc => allocCoh hc lbl (nWords us) (fun _ => .undef)

@[simp] theorem allocBuf_mono (lbl : AllocLabel) (n : Nat) (zero : Option (List Val)) (s : St) :
    Mono s (allocBuf lbl n zero s).1 := fun hc => allocCoh hc lbl n _

macro "flatM" : tactic => `(tactic|
  simp (config := {contextual := true}) only [ol, Option.mem_toList,
    Option.bind_eq_some_iff, Option.map_eq_some_iff, List.mem_map, List.mem_flatMap,
    List.mem_filterMap, List.mem_singleton, List.not_mem_nil, Prod.exists,
    Prod.mk.injEq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, forall_eq',
    Option.some.injEq, Option.pure_def, Option.bind_some, reduceCtorEq, false_implies,
    implies_true, Mono.refl', fenceS_mono, allocBuf_mono, Option.toList_none, Option.toList_some,
    Option.bind_none, Option.map_none, Option.map_some, Option.mem_def,
    Option.bind_eq_bind, Option.map_eq_map, Option.ite_none_left_eq_some, Option.ite_none_right_eq_some])

macro "close_mono" : tactic => `(tactic| first
    | done
    | exact Mono.refl' _
    | exact fenceS_mono _ _
    | exact allocBuf_mono _ _ _ _
    | exact loadUnits_mono _ _ _ _ _ _ _ (by assumption)
    | exact storeUnits_mono _ _ _ _ _ _ _ _ _ (by assumption)
    | exact alloc_mono (by assumption)
    | exact Mono.trans (loadUnits_mono _ _ _ _ _ _ _ (by assumption))
        (storeUnits_mono _ _ _ _ _ _ _ _ _ (by assumption))
    | exact Mono.trans (alloc_mono (by assumption)) (fenceS_mono _ _)
    | exact Mono.trans (loadUnits_mono _ _ _ _ _ _ _ (by assumption))
        (loadUnits_mono _ _ _ _ _ _ _ (by assumption)))

macro "crushM1" : tactic => `(tactic| (
  repeat' split
  all_goals (try flatM)
  all_goals (try intros)
  all_goals (try subst_vars)
  all_goals (try close_mono)))

macro "crushM" : tactic => `(tactic| (
  intro r hin
  revert hin
  crushM1
  all_goals (try (rename_i hh; revert hh; crushM1))
  all_goals (try (rename_i hh; revert hh; crushM1))))

theorem projM_mono (g : G) (s : St) (t : Ty) (ws : List Word) :
    ∀ r ∈ projM g s t ws, Mono s r.1 := by
  unfold projM
  crushM

theorem injM_mono (g : G) (s : St) (t : Ty) (j : Nat) (p : List Word) :
    ∀ r ∈ injM g s t j p, Mono s r.1 := by
  unfold injM
  crushM

theorem rmw_mono {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts} {s s' : St}
    {r0 r1 r2 : Word} {dst : WeakMem.Reg} {a : Address} {cmp : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs (mth s r0 r1 r2) dst a cmp newv deps acq rel)
    (hm : s'.mem = mem') (hv : s'.vs = th'.vs) (hs : s.mem = mem) : Mono s s' := fun hc => by
  have := stepRmw_coh h (hs ▸ hc)
  rw [hm, hv]; exact this

theorem evalOp_mono (g : G) (env : Env) (σs : List Ty) (s : St) (op : Op) :
    ∀ r ∈ evalOp g env σs s op, Mono s r.1 := by
  cases op <;> simp only [evalOp]
  all_goals crushM
  all_goals first
    | exact Mono.trans (projM_mono _ _ _ _ _ (by assumption)) (injM_mono _ _ _ _ _ _ (by assumption))
    | exact rmw_mono (by assumption) (by rfl) (by rfl) (by rfl)

theorem enter_vs {g : G} {th th' : TTh} {f : String} {ts : List Ty} {a : At}
    (h : enter g th f ts a = some th') : th'.vs = th.vs := by
  unfold enter at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.exists] at h
  obtain ⟨_, _, _, _, _, rfl⟩ := h
  rfl

theorem enter_mono {g : G} {mem : Memory} {pairs : List Ts} {th th0 th' : TTh} {f : String}
    {ts : List Ty} {a : At} (h : enter g th0 f ts a = some th') (hv : th0.vs = th.vs) :
    Mono (stOf mem pairs th) (stOf mem pairs th') := fun hc => by
  have e : th'.vs = th.vs := (enter_vs h).trans hv
  show CohAt mem th'.vs ∧ ∀ b, th.vs.coh b ≤ th'.vs.coh b
  rw [e]; exact ⟨hc, fun _ => Nat.le_refl _⟩

theorem rmwPair_mono {arch : Arch} {mem : Memory} {pairs : List Ts} {s s' : St}
    {r0 r1 r2 : Word} {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : Val} {n0 n1 : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs (mth s r0 r1 r2) d0 d1 a c0 c1 n0 n1 deps acq rel)
    (hm : s'.mem = mem') (hv : s'.vs = th'.vs) (hs : s.mem = mem) : Mono s s' := fun hc => by
  have := stepRmwPair_coh h (hs ▸ hc)
  rw [hm, hv]; exact this

/-- A thread step keeps `CohAt` and lowers no coherence view. -/
theorem tstep_mono (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) :
    ∀ r ∈ tstep g mem pairs th, Mono (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := by
  unfold tstep
  crushM
  all_goals first
    | exact evalOp_mono _ _ _ _ _ _ (by assumption)
    | exact Mono.trans (projM_mono _ _ _ _ _ (by assumption)) (injM_mono _ _ _ _ _ _ (by assumption))
    | exact enter_mono (by assumption) (by rfl)
    | exact rmw_mono (by assumption) (by rfl) (by rfl) (by rfl)
    | exact rmwPair_mono (by assumption) (by rfl) (by rfl) (by rfl)

/-! ### Configurations -/

/-- Every thread's views satisfy `CohAt` against shared memory.  The initial
configuration does (all views `0`). -/
def CfgCoh (c : Cfg) : Prop := ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → CohAt c.mem th.vs

/-- Same threads, and no thread's coherence view went down. -/
def CohLe (c c' : Cfg) : Prop :=
  c.ths.size = c'.ths.size ∧
  ∀ (i : Nat) (th th' : TTh), c.ths[i]? = some th → c'.ths[i]? = some th' →
    ∀ b, th.vs.coh b ≤ th'.vs.coh b

theorem CohLe.refl (c : Cfg) : CohLe c c :=
  ⟨rfl, fun _ _ _ h h' _ => by rw [h] at h'; cases h'; exact Nat.le_refl _⟩

theorem CohLe.trans {c1 c2 c3 : Cfg} (a : CohLe c1 c2) (b : CohLe c2 c3) : CohLe c1 c3 := by
  refine ⟨a.1.trans b.1, fun j th th3 h1 h3 x => ?_⟩
  have hj : j < c2.ths.size := by rw [← a.1]; exact lt_of_get h1
  have h2 : c2.ths[j]? = some c2.ths[j] := Array.getElem?_eq_getElem hj
  exact Nat.le_trans (a.2 j th _ h1 h2 x) (b.2 j _ th3 h2 h3 x)

theorem getElem?_set! {xs : Array TTh} {i j : Nat} {x : TTh} :
    (xs.set! i x)[j]? = if i = j then (if i < xs.size then some x else none) else xs[j]? := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]

theorem threadSteps_coh {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (h : c' ∈ threadSteps p k arch c i) (hc : CfgCoh c) : CfgCoh c' ∧ CohLe c c' := by
  unfold threadSteps at h
  split at h
  · simp at h
  · rename_i th0 hth
    simp only [List.mem_map] at h
    obtain ⟨⟨mem, pairs, th'⟩, hin, rfl⟩ := h
    have hm := tstep_mono _ _ _ _ _ hin (hc _ _ hth)
    have he := (tstep_ext _ _ _ _ _ hin).mem
    have hi := lt_of_get hth
    refine ⟨fun j th hj => ?_, by simp, fun j th th2 hj hj2 b => ?_⟩
    · simp only [getElem?_set!] at hj
      by_cases e : i = j
      · subst e; simp only [hi, ↓reduceIte, Option.some.injEq] at hj; subst hj; exact hm.1
      · simp only [e, ↓reduceIte] at hj; exact CohAt.ext he (hc _ _ hj)
    · simp only [getElem?_set!] at hj2
      by_cases e : i = j
      · subst e; simp only [hi, ↓reduceIte, Option.some.injEq] at hj2; subst hj2
        rw [hth] at hj; cases hj; exact hm.2 b
      · simp only [e, ↓reduceIte] at hj2; rw [hj] at hj2; cases hj2; exact Nat.le_refl _

theorem promise_coh (c : Cfg) (i : Nat) (a : Address) (v : Val) (w : Ts) (hc : CfgCoh c) :
    CfgCoh (promise c i a v w) ∧ CohLe c (promise c i a v w) := by
  unfold promise
  split
  · exact ⟨hc, CohLe.refl c⟩
  · rename_i th0 hth
    have he := Promises.Sim.MemExt.push c.mem (⟨a, v, w⟩ : Msg)
    have hi := lt_of_get hth
    refine ⟨fun j th hj => ?_, by simp, fun j th th2 hj hj2 b => ?_⟩
    · simp only [getElem?_set!] at hj
      by_cases e : i = j
      · subst e; simp only [hi, ↓reduceIte, Option.some.injEq] at hj; subst hj
        exact CohAt.ext he (hc _ th0 hth)
      · simp only [e, ↓reduceIte] at hj; exact CohAt.ext he (hc _ _ hj)
    · simp only [getElem?_set!] at hj2
      by_cases e : i = j
      · subst e; simp only [hi, ↓reduceIte, Option.some.injEq] at hj2; subst hj2
        rw [hth] at hj; cases hj; exact Nat.le_refl _
      · simp only [e, ↓reduceIte] at hj2; rw [hj] at hj2; cases hj2; exact Nat.le_refl _

theorem Step_coh {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg}
    (h : Step p k arch c c') (hc : CfgCoh c) : CfgCoh c' ∧ CohLe c c' := by
  cases h with
  | thread i hs _ => exact threadSteps_coh hs hc
  | prom i a v w _ _ _ => exact promise_coh c i a v w hc

theorem Reach_coh {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg}
    (h : Reach p k arch c c') (hc : CfgCoh c) : CfgCoh c' ∧ CohLe c c' := by
  induction h with
  | refl c => exact ⟨hc, CohLe.refl c⟩
  | step hs _ ih =>
      obtain ⟨h1, l1⟩ := Step_coh hs hc
      obtain ⟨h2, l2⟩ := ih h1
      exact ⟨h2, l1.trans l2⟩

/-- **Coherence views are constant on a class.**  Two configurations that
reach each other give each thread the same coherence views (given `CfgCoh`,
which the initial configuration has and every step keeps). -/
theorem class_coh_eq {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg}
    (h : Reach p k arch c c') (h' : Reach p k arch c' c) (hc : CfgCoh c)
    {i : Nat} {th th' : TTh} (hi : c.ths[i]? = some th) (hi' : c'.ths[i]? = some th')
    (b : Address) : th'.vs.coh b = th.vs.coh b := by
  obtain ⟨hc', l⟩ := Reach_coh h hc
  obtain ⟨_, l'⟩ := Reach_coh h' hc'
  exact Nat.le_antisymm (l'.2 i th' th hi' hi b) (l.2 i th th' hi hi' b)

/-! ### A4 end to end -/

theorem offs_zero (b : Address) : offs b 0 = b := by cases b; simp [offs]

/-- A one-word load returns one word, and if it left the view at its address
alone, that word is no newer than the view. -/
theorem loadUnits_one_stale {arch : Arch} {pw : Word} {a : Address} {acq : Bool} {k : Nat}
    {s s' : St} {ws : List Word} (h : (s', ws) ∈ loadUnits arch pw a acq [.one] k s) :
    ∃ w, ws = [w] ∧ (s'.vs.coh (offs a k) = s.vs.coh (offs a k) → w.rts ≤ s.vs.coh (offs a k)) := by
  simp only [loadUnits, List.mem_flatMap, List.mem_map] at h
  obtain ⟨th, hth, ⟨s2, ws2⟩, hin, heq⟩ := h
  try simp only [List.mem_singleton, Prod.mk.injEq] at hin
  try simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := hin
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨_, rfl, fun hc => stepLoad_stale hth hc⟩

/-- One thread at a one-word `load`: if the step leaves the view at the
address alone, the loaded word is no newer than it. -/
theorem tstep_load_stale {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {x : String}
    {acq : Bool} {a : At} {e : Expr} {t : Ty} {pw : Word} {μ : Mode} {u : Ty} {b : Address}
    (hterm : th.term = .let_ x (.load acq a) e) (ha : evalAt th.env a = some (t, [pw]))
    (hcell : cellOf t = some (μ, u)) (hb : addrOf pw = some b) (hus : accs u = some [.one])
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th)
    (hcoh : r.2.2.vs.coh b = th.vs.coh b) :
    ∃ t' w, r.2.2.env.head? = some (x, t', [w]) ∧ w.rts ≤ th.vs.coh b := by
  unfold tstep at hr
  simp only [hterm, evalOp, ha, hcell, hb, hus, List.map_map] at hr
  obtain ⟨⟨s', ws⟩, hin, rfl⟩ := List.mem_map.1 hr
  obtain ⟨w, rfl, hw⟩ := loadUnits_one_stale hin
  rw [offs_zero] at hw
  exact ⟨_, w, rfl, hw hcoh⟩

/-- **A4.**  Inside a class a one-word load reads no write newer than what the
loading thread has seen: a step of thread `i` from `c` that the run can come
back from (`hback`) loads a word whose timestamp is at most the thread's
coherence view at the address before the step. -/
theorem class_load_stale {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c1 : Cfg} {i : Nat}
    {th : TTh} {x : String} {acq : Bool} {a : At} {e : Expr} {t : Ty} {pw : Word} {μ : Mode}
    {u : Ty} {b : Address}
    (hc : CfgCoh c) (hs : c1 ∈ threadSteps p k arch c i) (hback : Reach p k arch c1 c)
    (hth : c.ths[i]? = some th) (hterm : th.term = .let_ x (.load acq a) e)
    (ha : evalAt th.env a = some (t, [pw])) (hcell : cellOf t = some (μ, u))
    (hb : addrOf pw = some b) (hus : accs u = some [.one]) :
    ∃ th1 t' w, c1.ths[i]? = some th1 ∧ th1.env.head? = some (x, t', [w]) ∧
      w.rts ≤ th.vs.coh b := by
  obtain ⟨hc1, l1⟩ := threadSteps_coh hs hc
  obtain ⟨_, l2⟩ := Reach_coh hback hc1
  simp only [threadSteps, hth] at hs
  obtain ⟨⟨mem, pairs, th1⟩, hin, rfl⟩ := List.mem_map.1 hs
  have h1 : (c.ths.set! i th1)[i]? = some th1 := by
    rw [getElem?_set!]; simp [lt_of_get hth]
  have hcoh : th1.vs.coh b = th.vs.coh b :=
    Nat.le_antisymm (l2.2 i th1 th h1 hth b) (l1.2 i th th1 hth h1 b)
  obtain ⟨t', w, hw, hle⟩ := tstep_load_stale hterm ha hcell hb hus hin hcoh
  exact ⟨th1, t', w, h1, hw, hle⟩

#print axioms evalOp_ext
#print axioms tstep_ext
#print axioms Step_ext
#print axioms reach_mem_eq
#print axioms tstep_cas_appends
#print axioms stale_cas
#print axioms stepLoad_stale
#print axioms robust_holds
#print axioms robust_noStore
#print axioms robust_cas
#print axioms tstep_mono
#print axioms class_coh_eq
#print axioms class_load_stale

end TermLiveProps
