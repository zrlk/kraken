import WeakCore.TermExtStep
/-!
# TermProgressDefs — item 36's vocabulary: why a thread is stuck, and a thread's own moves

`StuckWhy`, `SpawnBy`, `ExtBy`, `MovesBy` and `movesBy_step`: the original statement texts, verbatim.  Shared by `TermProgress` and the
liveness system with extern and spawn moves.
-/

namespace TermProgress
open CoreLang CoreTerm TermRun TermSpawnStep TermExtStep
open WeakMem (Arch)

/-- Why thread `i` (`th`) of `c` cannot move: (u) promises out and not certifiable; (s) at a spawn site, promise-free,
at capacity. -/
inductive StuckWhy (p : Prog) (k : Promises.Knobs) (arch : Arch) (cap : Nat) (c : Cfg) (i : Nat) (th : TTh) : Prop
  | uncert : th.promises ≠ [] → ¬ Certified p k arch c i → StuckWhy p k arch cap c i th
  | atCap : AtSite th → th.promises = [] → cap ≤ c.ths.size → StuckWhy p k arch cap c i th
  | parked : (∃ x a e, th.term = .let_ x (.ext .park a) e) → th.permit = none →
      (∀ a v w, w < c.mem.size → ¬ Certified p k arch (promise c i a v w) i) → StuckWhy p k arch cap c i th

/-- `c'` is a spawn by thread `i` (the data of `Spawn.mk` at `i`). -/
def SpawnBy (cap : Nat) (c : Cfg) (i : Nat) (c' : Cfg) : Prop :=
  ∃ x f a T ts e th rt ws, c.ths[i]? = some th ∧ th.term = .let_ x (.spawn f a T ts) e ∧ th.promises = [] ∧
    c.ths.size < cap ∧ evalAt th.env a = some (rt, ws) ∧ c' = spawnCfg c i th x e f ts T ws

/-- `c'` is an extern THREAD move of `i` (the data of `Ext.mk` at `i`, enabled): item 36's vocabulary, restated. -/
def ExtBy (p : Prog) (k : Promises.Knobs) (arch : Arch) (c : Cfg) (i : Nat) (c' : Cfg) : Prop :=
  ∃ x n a e th rt ws rs, c.ths[i]? = some th ∧ th.term = .let_ x (.ext n a) e ∧
    (ExtNeedsNoProm n th → th.promises = []) ∧ ExtEnabled n th ∧ evalAt th.env a = some (rt, ws) ∧
    n.Admits i ws c.trace rs ∧ Certified p k arch (extCfg c i th x n e ws rs) i ∧ c' = wake (extCfg c i th x n e ws rs) i (relView th.vs) n ws

/-- Thread `i` has a move of its own: a certified thread step, a certified promise, a spawn, or an extern step. -/
def MovesBy (p : Prog) (k : Promises.Knobs) (arch : Arch) (cap : Nat) (c : Cfg) (i : Nat) : Prop :=
  (∃ c', c' ∈ threadSteps p k arch c i ∧ Certified p k arch c' i) ∨
  (∃ a v w, i < c.ths.size ∧ w < c.mem.size ∧ Certified p k arch (promise c i a v w) i) ∨
  (∃ c', SpawnBy cap c i c') ∨ (∃ c', ExtBy p k arch c i c')

/-- A move of thread `i` is a machine move. -/
theorem movesBy_step {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c : Cfg} {i : Nat}
    (h : MovesBy p k arch cap c i) :
    ∃ c', Step p k arch c c' ∨ Spawn p k arch cap c c' ∨ Ext p k arch c c' := by
  rcases h with ⟨c', h1, h2⟩ | ⟨a, v, w, hi, hw, hc⟩ | ⟨c', x, f, a, T, ts, e, th, rt, ws, h1, h2, h3, h4, h5, rfl⟩ |
    ⟨c', x, n, a, e, th, rt, ws, rs, h1, h2, h3, -, h4, h5, h6, rfl⟩
  · exact ⟨c', .inl (.thread i h1 h2)⟩
  · exact ⟨_, .inl (.prom i a v w hi hw hc)⟩
  · exact ⟨_, .inr (.inl (.mk i x f a T ts e th rt ws h1 h2 h3 h4 h5))⟩
  · exact ⟨_, .inr (.inr (.mk i x n a e th rt ws rs h1 h2 h3 h4 h5 h6))⟩

end TermProgress
#print axioms TermProgress.movesBy_step
