import WeakCore.TermProgressDefs
import WeakCore.TermLiveMach
import WeakCore.TermPermit
/-! # TermLiveMachE — the liveness machine with extern and spawn moves (item 37 S0)

`machineE` is **the** liveness system from item 37 on: `TermLiveMach.machine` has thread and promise labels only,
so a run of it never takes an extern step (the wrapper start ends with `ext exitEv`) and never spawns.
`machineE` adds both as thread moves `(i, true)`, as `TermLive.successorsL` labels extern successors.
It is meant to be reused unchanged by item 38 (tier-1 completeness): do not add another variant.

The bridge `machineE_run_stepsE` turns a `machineE` run into an EM0 run (`StepsE` at the start's capacity), the
relation the EM0 finals (`ExtArmZ.machine_tokens_main_em0`) are stated over. -/

namespace TermLiveL3
open CoreLang CoreTerm TermRun TermSpawnStep TermExtStep TermLiveMach TermProgress
open WeakMem (Arch Address)

/-! ### S0: the liveness system with extern and spawn moves -/

/-- (D4) The label kinds of `machineE`: a thread move, a promise, an environment move (a spurious wake). -/
inductive Lbl | thr | prom | env deriving DecidableEq, Repr
/-- (D4) A spurious wake: a thread parked WITHOUT a permit returns from `park` anyway (promises allowed, as for every
`Ext`; `Certified` is the premise). An `Ext` step, not a thread move: fairness never forces it. At a park site
`Ext = ExtBy ∨ SpuriousWake` exactly (D1), so `machineE` matches `StepsE` there. -/
def SpuriousWake (p : Prog) (k : Promises.Knobs) (arch : Arch) (c : Cfg) (i : Nat) (c' : Cfg) : Prop :=
  ∃ x a e th rt ws, c.ths[i]? = some th ∧ th.term = .let_ x (.ext .park a) e ∧ th.permit = none ∧
    evalAt th.env a = some (rt, ws) ∧ Certified p k arch (extCfg c i th x .park e ws []) i ∧
    c' = extCfg c i th x .park e ws []
def mstepE (p : Prog) (k : Promises.Knobs) (arch : Arch) (c : Cfg) : Nat × Lbl → Cfg → Prop
  | (i, .thr), c' => (c' ∈ threadSteps p k arch c i ∧ Certified p k arch c' i) ∨ SpawnBy c.cap c i c' ∨ ExtBy p k arch c i c'
  | (i, .prom), c' => ∃ a v w, i < c.ths.size ∧ w < c.mem.size ∧ Certified p k arch (promise c i a v w) i ∧ c' = promise c i a v w
  | (i, .env), c' => SpuriousWake p k arch c i c'
def machineE (p : Prog) (k : Promises.Knobs) (arch : Arch) : LSys where
  L := Nat × Lbl
  S := mstepE p k arch
  actor l := some l.1
  thr i := (i, .thr)

/-- A `mstepE` move is a machine step, a spawn at the configuration's capacity, or an extern step. -/
theorem mstepE_step {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {l : Nat × Lbl}
    (h : mstepE p k arch c l c') : Step p k arch c c' ∨ Spawn p k arch c.cap c c' ∨ Ext p k arch c c' := by
  obtain ⟨i, b⟩ := l
  cases b with
  | thr =>
      rcases h with ⟨h1, h2⟩ | ⟨x, f, a, T, ts, e, th, rt, ws, h1, h2, h3, h4, h5, rfl⟩ |
        ⟨x, n, a, e, th, rt, ws, rs, h1, h2, h3, -, h4, h5, h6, rfl⟩
      · exact .inl (.thread i h1 h2)
      · exact .inr (.inl (.mk i x f a T ts e th rt ws h1 h2 h3 h4 h5))
      · exact .inr (.inr (.mk i x n a e th rt ws rs h1 h2 h3 h4 h5 h6))
  | prom =>
      obtain ⟨a, v, w, hi, hw, hc, rfl⟩ := h
      exact .inl (.prom i a v w hi hw hc)
  | env =>
      obtain ⟨x, a, e, th, rt, ws, h1, h2, -, h4, h5, rfl⟩ := h
      -- O5: at a `park` site the return is an `Ext` step whatever the permit and the promises
      have hx := TermPermit.park_site_step p k arch h1 h2 h4 h5
      rw [wake_of_ne _ _ _ _ (by decide)] at hx
      exact .inr (.inr hx)

/-- (D4) Elimination form of an environment move. -/
theorem spuriousWake_elim {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (h : mstepE p k arch c (i, .env) c') :
    ∃ x a e th rt ws, c.ths[i]? = some th ∧ th.term = .let_ x (.ext .park a) e ∧ th.permit = none ∧
      evalAt th.env a = some (rt, ws) ∧ c' = extCfg c i th x .park e ws [] := by
  obtain ⟨x, a, e, th, rt, ws, h1, h2, h3, h4, -, rfl⟩ := h
  exact ⟨x, a, e, th, rt, ws, h1, h2, h3, h4, rfl⟩

theorem spawn_cap_eq {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c c' : Cfg}
    (h : Spawn p k arch cap c c') : c'.cap = c.cap := by
  cases h; rfl

theorem step_cap_eq {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} (h : Step p k arch c c') :
    c'.cap = c.cap := by
  cases h with
  | thread i hs _ =>
      unfold threadSteps at hs
      split at hs
      · cases hs
      · simp only [List.mem_map] at hs
        obtain ⟨_, _, rfl⟩ := hs
        rfl
  | prom i a v w _ _ _ => unfold promise; split <;> rfl

theorem ext_cap_eq {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} (h : Ext p k arch c c') :
    c'.cap = c.cap := by
  cases h with
  | mk i x n a e th rt ws =>
      rw [wake_cap]
      unfold extCfg
      split
      · unfold curCfg; split <;> rfl
      · rfl

theorem stepsG_snoc {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {c c' c'' : Cfg}
    (h : StepsG p k arch Sp c c') (h' : Step p k arch c' c'' ∨ Sp c' c'') : StepsG p k arch Sp c c'' := by
  induction h with
  | refl => exact .step h' (.refl _)
  | step hs _ ih => exact .step hs (ih h')

/-- **S0 bridge.** Every prefix of a `machineE` run is an EM0 run (`StepsE`) at the start's capacity;
the capacity is constant along the run. -/
theorem machineE_run_stepsE {p : Prog} {k : Promises.Knobs} {arch : Arch} {r : LRun (machineE p k arch).L}
    (hr : (machineE p k arch).Run r) (n : Nat) :
    StepsE p k arch (r.cfg 0).cap (r.cfg 0) (r.cfg n) ∧ (r.cfg n).cap = (r.cfg 0).cap := by
  induction n with
  | zero => exact ⟨.refl _, rfl⟩
  | succ n ih =>
      obtain ⟨hs, hcap⟩ := ih
      have hm := hr n
      cases hl : r.lbl n with
      | none =>
          rw [hl] at hm
          have he : r.cfg (n + 1) = r.cfg n := hm
          rw [he]; exact ⟨hs, hcap⟩
      | some l =>
          rw [hl] at hm
          have hm' : mstepE p k arch (r.cfg n) l (r.cfg (n + 1)) := hm
          rcases mstepE_step hm' with h | h | h
          · exact ⟨stepsG_snoc hs (.inl h), (step_cap_eq h).trans hcap⟩
          · exact ⟨stepsG_snoc hs (.inr (.inl (hcap ▸ h))), (spawn_cap_eq h).trans hcap⟩
          · exact ⟨stepsG_snoc hs (.inr (.inr h)), (ext_cap_eq h).trans hcap⟩

end TermLiveL3
#print axioms TermLiveL3.mstepE_step
#print axioms TermLiveL3.spuriousWake_elim
#print axioms TermLiveL3.machineE_run_stepsE
