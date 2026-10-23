import WeakCore.TermSpawnStep

/-! # TermExtStep (E1): the trusted extern configuration step

A thread at `let x = ext n a in e` takes no thread step (`tstep_ext`: `evalOp` has `[]`
for `.ext`); its only move is `Ext`, a configuration step **beside** `Step` and `Spawn`, so no existing
`Step` case split, final or liveness statement changes meaning.

* `extCfg`: the thread continues with `x := n.res i` (`current`: its own index, a `ThreadId`; else `()`),
  and `n.events ws` (`emit`: one byte; `exitEv`: the exit code) is appended to `trace`.  Memory, pairs,
  views, promises, allocations and the thread count are unchanged; no fence; nothing is read from memory.
* `Ext`: enabled iff the argument evaluates and thread `i` is certified afterwards; (IO1) the calls of
  `ExtNeedsNoProm` (`exitEv`, `current()`) also need an empty promise set. The I/O step itself is never
  promised; stores after it may be (a certificate takes the same move, `Solo.ext`/`extSteps`).
* `StepsE`: runs of machine steps, spawns and extern steps (`StepsG` at `Spawn ∨ Ext`).
* `Ext.ofNoProm`: with no promises the certificate is the empty run.
-/

namespace TermExtStep
open CoreLang CoreTerm TermRun TermSpawnStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## The step

(IO1) `curCfg` and `extCfg` live in `TermRun` (before `Solo`, whose `ext` arm uses them). -/

/-- **The extern step** of thread `i`. -/
inductive Ext (p : Prog) (k : Promises.Knobs) (arch : Arch) : Cfg → Cfg → Prop
  | mk {c : Cfg} (i : Nat) (x : String) (n : ExtName) (a : At) (e : Expr) (th : TTh) (rt : Ty)
      (ws : List Word) :
      c.ths[i]? = some th → th.term = .let_ x (.ext n a) e → (ExtNeedsNoProm n th → th.promises = []) →
      evalAt th.env a = some (rt, ws) → Certified p k arch (extCfg c i th x n e ws) i →
      Ext p k arch c (extCfg c i th x n e ws)

/-- Runs of machine steps, spawns (capacity `cap`) and extern steps. -/
abbrev StepsE (p : Prog) (k : Promises.Knobs) (arch : Arch) (cap : Nat) : Cfg → Cfg → Prop :=
  StepsG p k arch (fun c c' => Spawn p k arch cap c c' ∨ Ext p k arch c c')

/-- Elimination form of `Ext`. -/
theorem Ext.elim {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} (h : Ext p k arch c c') :
    ∃ i x n a e th rt ws, c.ths[i]? = some th ∧ th.term = .let_ x (.ext n a) e ∧
      (ExtNeedsNoProm n th → th.promises = []) ∧ evalAt th.env a = some (rt, ws) ∧
      Certified p k arch (extCfg c i th x n e ws) i ∧ c' = extCfg c i th x n e ws := by
  cases h with
  | mk i x n a e th rt ws h1 h2 h3 h4 h5 => exact ⟨i, x, n, a, e, th, rt, ws, h1, h2, h3, h4, h5, rfl⟩

/-- (IO1) Thread `i` keeps its promises across `extCfg`. -/
theorem extCfg_noPromises {c : Cfg} {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) (x : String) (n : ExtName)
    (e : Expr) (ws : List Word) : noPromises (extCfg c i th x n e ws) i = th.promises.isEmpty := by
  have hi : i < c.ths.size := by
    rcases Nat.lt_or_ge i c.ths.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hth
  unfold extCfg curCfg; split <;> (try split) <;> simp [noPromises, Array.set!, hi]

/-- (IO1) **With no promises an extern step needs no certificate beyond the empty run**: every pre-IO1 extern
step is an `Ext` step. -/
theorem Ext.ofNoProm {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {x : String} {n : ExtName}
    {a : At} {e : Expr} {th : TTh} {rt : Ty} {ws : List Word} (hth : c.ths[i]? = some th)
    (hterm : th.term = .let_ x (.ext n a) e) (hnp : th.promises = []) (hev : evalAt th.env a = some (rt, ws)) :
    Ext p k arch c (extCfg c i th x n e ws) :=
  .mk i x n a e th rt ws hth hterm (fun _ => hnp) hev
    ⟨_, .refl _, by rw [extCfg_noPromises hth, hnp]; rfl⟩

/-! ## What the step leaves alone -/

theorem extCfg_mem (c : Cfg) (i : Nat) (th : TTh) (x : String) (n : ExtName) (e : Expr) (ws : List Word) :
    (extCfg c i th x n e ws).mem = c.mem := by unfold extCfg curCfg; split <;> (try split) <;> rfl

theorem extCfg_pairs (c : Cfg) (i : Nat) (th : TTh) (x : String) (n : ExtName) (e : Expr) (ws : List Word) :
    (extCfg c i th x n e ws).pairs = c.pairs := by unfold extCfg curCfg; split <;> (try split) <;> rfl

theorem extCfg_cap (c : Cfg) (i : Nat) (th : TTh) (x : String) (n : ExtName) (e : Expr) (ws : List Word) :
    (extCfg c i th x n e ws).cap = c.cap := by unfold extCfg curCfg; split <;> (try split) <;> rfl

theorem extCfg_lbase (c : Cfg) (i : Nat) (th : TTh) (x : String) (n : ExtName) (e : Expr) (ws : List Word) :
    (extCfg c i th x n e ws).lbase = c.lbase := by unfold extCfg curCfg; split <;> (try split) <;> rfl

theorem extCfg_size (c : Cfg) (i : Nat) (th : TTh) (x : String) (n : ExtName) (e : Expr) (ws : List Word) :
    (extCfg c i th x n e ws).ths.size = c.ths.size := by
  unfold extCfg curCfg; split <;> (try split) <;> simp

theorem extCfg_n (c : Cfg) (i : Nat) (th : TTh) (x : String) (n : ExtName) (e : Expr) (ws : List Word) :
    (extCfg c i th x n e ws).n = c.n := by
  simp [Cfg.n, extCfg_cap, extCfg_size]

/-- The trace only grows: by `n.events ws`. -/
theorem extCfg_trace (c : Cfg) (i : Nat) (th : TTh) (x : String) (n : ExtName) (e : Expr) (ws : List Word) :
    (extCfg c i th x n e ws).trace = c.trace ++ n.events ws := by
  unfold extCfg curCfg; split <;> (try split) <;> simp [ExtName.events]

/-- The stepping thread after a non-`current` step. -/
theorem extCfg_ths_self {c : Cfg} {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) (x : String) (n : ExtName)
    (e : Expr) (ws : List Word) (hn : n ≠ .current) :
    (extCfg c i th x n e ws).ths[i]? = some { th with term := e, env := (x, n.sig.2, n.res i) :: th.env } := by
  have hi : i < c.ths.size := by
    rcases Nat.lt_or_ge i c.ths.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hth
  unfold extCfg; split
  · exact absurd rfl hn
  · simp [Array.set!, hi]

/-- The other threads are untouched. -/
theorem extCfg_ths_ne (c : Cfg) {i j : Nat} (th : TTh) (x : String) (n : ExtName) (e : Expr) (ws : List Word)
    (hj : j ≠ i) : (extCfg c i th x n e ws).ths[j]? = c.ths[j]? := by
  unfold extCfg curCfg; split <;> (try split) <;> simp [Array.set!, Ne.symm hj]

/-- An `Ext` step keeps memory, pairs, `cap`, `lbase` and the thread count, and extends the trace. -/
theorem Ext.frame {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} (h : Ext p k arch c c') :
    c'.mem = c.mem ∧ c'.pairs = c.pairs ∧ c'.cap = c.cap ∧ c'.lbase = c.lbase ∧ c'.ths.size = c.ths.size ∧
      c.trace <+: c'.trace := by
  obtain ⟨i, x, n, a, e, th, rt, ws, -, -, -, -, -, rfl⟩ := h.elim
  exact ⟨extCfg_mem .., extCfg_pairs .., extCfg_cap .., extCfg_lbase .., extCfg_size ..,
    by rw [extCfg_trace]; exact List.prefix_append _ _⟩

/-! ## An extern site has no thread step -/

theorem tstep_ext {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {x : String} {n : ExtName} {a : At}
    {e : Expr} (h : th.term = .let_ x (.ext n a) e) : tstep g mem pairs th = [] := by
  simp [tstep, h, evalOp]

theorem threadSteps_ext {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {th : TTh}
    {x : String} {n : ExtName} {a : At} {e : Expr} (hth : c.ths[i]? = some th)
    (h : th.term = .let_ x (.ext n a) e) : threadSteps p k arch c i = [] := by
  simp [threadSteps, hth, tstep_ext h]

/-- Thread `th` sits at an extern site. -/
def ExtSite (th : TTh) : Prop := ∃ x n a e, th.term = .let_ x (.ext n a) e

/-! ## Runs -/

/-- Every `StepsX` run is a `StepsE` run. -/
theorem StepsE.ofStepsX {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c c' : Cfg}
    (h : StepsX p k arch cap c c') : StepsE p k arch cap c c' :=
  StepsG.mono (fun _ _ h => .inl h) h

end TermExtStep

#print axioms TermExtStep.Ext.elim
#print axioms TermExtStep.extCfg_noPromises
#print axioms TermExtStep.Ext.ofNoProm
#print axioms TermExtStep.extCfg_mem
#print axioms TermExtStep.extCfg_pairs
#print axioms TermExtStep.extCfg_cap
#print axioms TermExtStep.extCfg_lbase
#print axioms TermExtStep.extCfg_size
#print axioms TermExtStep.extCfg_n
#print axioms TermExtStep.extCfg_trace
#print axioms TermExtStep.extCfg_ths_self
#print axioms TermExtStep.extCfg_ths_ne
#print axioms TermExtStep.Ext.frame
#print axioms TermExtStep.tstep_ext
#print axioms TermExtStep.threadSteps_ext
#print axioms TermExtStep.StepsE.ofStepsX
