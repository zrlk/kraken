import WeakCore.TermSpawnStep

/-! # TermExtStep (E1): the trusted extern configuration step

A thread at `let x = ext n a in e` takes no thread step (`tstep_ext`: `evalOp` has `[]`
for `.ext`); its only move is `Ext`, a configuration step **beside** `Step` and `Spawn`, so no existing
`Step` case split, final or liveness statement changes meaning.

* `extCfg`: the thread continues with `x := n.res i` (`current`: its own index, a `ThreadId`; else `()`),
  and `n.events ws` (`emit`: one byte; `exitEv`: the exit code) is appended to `trace`.  Memory, pairs,
  views, promises, allocations and the thread count are unchanged; no fence; nothing is read from memory.
* `Ext`: enabled iff the argument evaluates and thread `i` is certified afterwards; the calls of
  `ExtNeedsNoProm` (`exitEv`, `current()`) also need an empty promise set. The I/O step itself is never
  promised; stores after it may be (a certificate takes the same move, `Solo.ext`/`extSteps`).
* `StepsE`: runs of machine steps, spawns and extern steps (`StepsG` at `Spawn ∨ Ext`).
* `Ext.ofNoProm`: with no promises the certificate is the empty run.
-/

namespace TermExtStep
open CoreLang CoreTerm TermRun TermSpawnStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## The step

 `curCfg` and `extCfg` live in `TermRun` (before `Solo`, whose `ext` arm uses them). -/

/-- **The extern step** of thread `i`: the argument evaluates, a result the extern admits is bound, the thread is certified
afterwards (on its own post-state; a permit of another thread never affects a certificate), then `unpark`'s wake is applied.
(No enabledness premise; the only new promise premise is `devChoice`'s, a new arm: a permit-less `park` return and a
promiseful `park`/`unpark` are steps, as the prelude `ret ()` calls are today, so `StepsE` loses no old execution.) -/
inductive Ext (p : Prog) (k : Promises.Knobs) (arch : Arch) : Cfg → Cfg → Prop
  | mk {c : Cfg} (i : Nat) (x : String) (n : ExtName) (a : At) (e : Expr) (th : TTh) (rt : Ty) (ws rs : List Word) :
      c.ths[i]? = some th → th.term = .let_ x (.ext n a) e → (ExtNeedsNoProm n th → th.promises = []) →
      evalAt th.env a = some (rt, ws) → n.Admits i ws c.trace rs →
      Certified p k arch (extCfg c i th x n e ws rs) i →
      Ext p k arch c (wake (extCfg c i th x n e ws rs) i (relView th.vs) n ws)

/-- Runs of machine steps, spawns (capacity `cap`) and extern steps. -/
abbrev StepsE (p : Prog) (k : Promises.Knobs) (arch : Arch) (cap : Nat) : Cfg → Cfg → Prop :=
  StepsG p k arch (fun c c' => Spawn p k arch cap c c' ∨ Ext p k arch c c')

/-- Elimination form of `Ext`. -/
theorem Ext.elim {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} (h : Ext p k arch c c') :
    ∃ i x n a e th rt ws rs, c.ths[i]? = some th ∧ th.term = .let_ x (.ext n a) e ∧
      (ExtNeedsNoProm n th → th.promises = []) ∧ evalAt th.env a = some (rt, ws) ∧ n.Admits i ws c.trace rs ∧
      Certified p k arch (extCfg c i th x n e ws rs) i ∧ c' = wake (extCfg c i th x n e ws rs) i (relView th.vs) n ws := by
  cases h with
  | mk i x n a e th rt ws rs h1 h2 h3 h4 h5 h6 => exact ⟨i, x, n, a, e, th, rt, ws, rs, h1, h2, h3, h4, h5, h6, rfl⟩

/-- Thread `i` keeps its promises across `extCfg`. -/
theorem extCfg_noPromises {c : Cfg} {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) (x : String) (n : ExtName)
    (e : Expr) (ws rs : List Word) : noPromises (extCfg c i th x n e ws rs) i = th.promises.isEmpty := by
  have hi : i < c.ths.size := by
    rcases Nat.lt_or_ge i c.ths.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hth
  unfold extCfg curCfg; split <;> (try split) <;> simp [noPromises, Array.set!, hi]

/-- **With no promises an extern step needs no certificate beyond the empty run**: every extern step by a
thread with no outstanding promises is an `Ext` step. -/
theorem Ext.ofNoProm {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {x : String} {n : ExtName}
    {a : At} {e : Expr} {th : TTh} {rt : Ty} {ws rs : List Word} (hth : c.ths[i]? = some th)
    (hterm : th.term = .let_ x (.ext n a) e) (hnp : th.promises = []) (hev : evalAt th.env a = some (rt, ws))
    (hrs : n.Admits i ws c.trace rs) :
    Ext p k arch c (wake (extCfg c i th x n e ws rs) i (relView th.vs) n ws) :=
  .mk i x n a e th rt ws rs hth hterm (fun _ => hnp) hev hrs
    ⟨_, .refl _, by rw [extCfg_noPromises hth, hnp]; rfl⟩

/-! ## What the step leaves alone -/

theorem extCfg_mem (c : Cfg) (i : Nat) (th : TTh) (x : String) (n : ExtName) (e : Expr) (ws rs : List Word) :
    (extCfg c i th x n e ws rs).mem = c.mem := by unfold extCfg curCfg; split <;> (try split) <;> rfl

theorem extCfg_pairs (c : Cfg) (i : Nat) (th : TTh) (x : String) (n : ExtName) (e : Expr) (ws rs : List Word) :
    (extCfg c i th x n e ws rs).pairs = c.pairs := by unfold extCfg curCfg; split <;> (try split) <;> rfl

theorem extCfg_cap (c : Cfg) (i : Nat) (th : TTh) (x : String) (n : ExtName) (e : Expr) (ws rs : List Word) :
    (extCfg c i th x n e ws rs).cap = c.cap := by unfold extCfg curCfg; split <;> (try split) <;> rfl

theorem extCfg_lbase (c : Cfg) (i : Nat) (th : TTh) (x : String) (n : ExtName) (e : Expr) (ws rs : List Word) :
    (extCfg c i th x n e ws rs).lbase = c.lbase := by unfold extCfg curCfg; split <;> (try split) <;> rfl

theorem extCfg_size (c : Cfg) (i : Nat) (th : TTh) (x : String) (n : ExtName) (e : Expr) (ws rs : List Word) :
    (extCfg c i th x n e ws rs).ths.size = c.ths.size := by
  unfold extCfg curCfg; split <;> (try split) <;> simp

theorem extCfg_n (c : Cfg) (i : Nat) (th : TTh) (x : String) (n : ExtName) (e : Expr) (ws rs : List Word) :
    (extCfg c i th x n e ws rs).n = c.n := by
  simp [Cfg.n, extCfg_cap, extCfg_size]

/-- The trace only grows: by `n.events ws rs`. -/
theorem extCfg_trace (c : Cfg) (i : Nat) (th : TTh) (x : String) (n : ExtName) (e : Expr) (ws rs : List Word) :
    (extCfg c i th x n e ws rs).trace = c.trace ++ n.events ws rs := by
  unfold extCfg curCfg; split <;> (try split) <;> simp [ExtName.events]

/-- The stepping thread after a non-`current` step ((D4) `park` acquires and clears its permit). -/
theorem extCfg_ths_self {c : Cfg} {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) (x : String) (n : ExtName)
    (e : Expr) (ws rs : List Word) (hn : n ≠ .current) :
    (extCfg c i th x n e ws rs).ths[i]? =
      some { th with term := e, env := (x, n.sig.2, rs) :: th.env, vs := if n = .park then parkVs c.mem.size th else th.vs,
                     permit := if n = .park then none else th.permit } := by
  have hi : i < c.ths.size := by
    rcases Nat.lt_or_ge i c.ths.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hth
  unfold extCfg; split
  · exact absurd rfl hn
  · simp [Array.set!, hi]

/-- The other threads are untouched. -/
theorem extCfg_ths_ne (c : Cfg) {i j : Nat} (th : TTh) (x : String) (n : ExtName) (e : Expr) (ws rs : List Word)
    (hj : j ≠ i) : (extCfg c i th x n e ws rs).ths[j]? = c.ths[j]? := by
  unfold extCfg curCfg; split <;> (try split) <;> simp [Array.set!, Ne.symm hj]

/-! ## (D4) The wake: only one thread's permit changes -/

theorem setPermit_eq (c : Cfg) (j : Nat) (v : Ts) :
    setPermit c j v = c ∨ ∃ th, c.ths[j]? = some th ∧
      setPermit c j v = { c with ths := c.ths.set! j { th with permit := some (max (th.permit.getD 0) v) } } := by
  unfold setPermit; split
  · rename_i th h; exact .inr ⟨th, h, rfl⟩
  · exact .inl rfl

theorem wake_eq (c : Cfg) (i : Nat) (v : Ts) (n : ExtName) (ws : List Word) :
    wake c i v n ws = c ∨ ∃ j th u, c.ths[j]? = some th ∧
      wake c i v n ws = { c with ths := c.ths.set! j { th with permit := some u } } := by
  unfold wake; split
  · split
    · rename_i j _
      rcases setPermit_eq c j (if j = i then 0 else v) with h | ⟨th, h1, h2⟩
      · exact .inl h
      · exact .inr ⟨j, th, _, h1, h2⟩
    · exact .inl rfl
  · exact .inl rfl

theorem wake_mem (c : Cfg) (i : Nat) (v : Ts) (n : ExtName) (ws : List Word) : (wake c i v n ws).mem = c.mem := by
  rcases wake_eq c i v n ws with h | ⟨_, _, _, _, h⟩ <;> rw [h]

theorem wake_pairs (c : Cfg) (i : Nat) (v : Ts) (n : ExtName) (ws : List Word) : (wake c i v n ws).pairs = c.pairs := by
  rcases wake_eq c i v n ws with h | ⟨_, _, _, _, h⟩ <;> rw [h]

theorem wake_cap (c : Cfg) (i : Nat) (v : Ts) (n : ExtName) (ws : List Word) : (wake c i v n ws).cap = c.cap := by
  rcases wake_eq c i v n ws with h | ⟨_, _, _, _, h⟩ <;> rw [h]

theorem wake_lbase (c : Cfg) (i : Nat) (v : Ts) (n : ExtName) (ws : List Word) : (wake c i v n ws).lbase = c.lbase := by
  rcases wake_eq c i v n ws with h | ⟨_, _, _, _, h⟩ <;> rw [h]

theorem wake_boxFence (c : Cfg) (i : Nat) (v : Ts) (n : ExtName) (ws : List Word) : (wake c i v n ws).boxFence = c.boxFence := by
  rcases wake_eq c i v n ws with h | ⟨_, _, _, _, h⟩ <;> rw [h]

theorem wake_trace (c : Cfg) (i : Nat) (v : Ts) (n : ExtName) (ws : List Word) : (wake c i v n ws).trace = c.trace := by
  rcases wake_eq c i v n ws with h | ⟨_, _, _, _, h⟩ <;> rw [h]

theorem wake_size (c : Cfg) (i : Nat) (v : Ts) (n : ExtName) (ws : List Word) : (wake c i v n ws).ths.size = c.ths.size := by
  rcases wake_eq c i v n ws with h | ⟨_, _, _, _, h⟩ <;> rw [h]; simp

theorem wake_n (c : Cfg) (i : Nat) (v : Ts) (n : ExtName) (ws : List Word) : (wake c i v n ws).n = c.n := by
  simp [Cfg.n, wake_cap, wake_size]

/-- Each thread after the wake: unchanged, or the same thread with its permit set (to some view). -/
theorem wake_get (c : Cfg) (i : Nat) (v : Ts) (n : ExtName) (ws : List Word) (j : Nat) :
    (wake c i v n ws).ths[j]? = c.ths[j]? ∨
      ∃ th u, c.ths[j]? = some th ∧ (wake c i v n ws).ths[j]? = some { th with permit := some u } := by
  rcases wake_eq c i v n ws with h | ⟨j', th, u, h1, h2⟩
  · exact .inl (by rw [h])
  · rw [h2]
    by_cases hj : j = j'
    · subst hj
      have hi : j < c.ths.size := by
        rcases Nat.lt_or_ge j c.ths.size with h | h
        · exact h
        · simp [Array.getElem?_eq_none h] at h1
      exact .inr ⟨th, u, h1, by simp [Array.set!, hi]⟩
    · exact .inl (by simp [Array.set!, Ne.symm hj])

/-- Not an `unpark`: no wake. -/
theorem wake_of_ne (c : Cfg) (i : Nat) (v : Ts) {n : ExtName} (ws : List Word) (hn : n ≠ .unpark) : wake c i v n ws = c := by
  unfold wake; split
  · exact absurd rfl hn
  · rfl

/-- An `Ext` step keeps memory, pairs, `cap`, `lbase` and the thread count, and extends the trace. -/
theorem Ext.frame {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} (h : Ext p k arch c c') :
    c'.mem = c.mem ∧ c'.pairs = c.pairs ∧ c'.cap = c.cap ∧ c'.lbase = c.lbase ∧ c'.ths.size = c.ths.size ∧
      c.trace <+: c'.trace := by
  obtain ⟨i, x, n, a, e, th, rt, ws, rs, -, -, -, -, -, -, rfl⟩ := h.elim
  simp only [wake_mem, wake_pairs, wake_cap, wake_lbase, wake_size, wake_trace]
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
#print axioms TermExtStep.setPermit_eq
#print axioms TermExtStep.wake_eq
#print axioms TermExtStep.wake_get
#print axioms TermExtStep.wake_of_ne
#print axioms TermExtStep.Ext.frame
#print axioms TermExtStep.tstep_ext
#print axioms TermExtStep.threadSteps_ext
#print axioms TermExtStep.StepsE.ofStepsX
