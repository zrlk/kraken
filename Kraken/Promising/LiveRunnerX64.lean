/-
**Liveness with declarations, x64: the bridge.**

The x64 instance of `LiveRunnerSim`: the map is `State.noDecls` (drop the
thread's declarations) and the set `GD ds e` is "runs the executable `e`
with declarations `ds`". Under `CellsDeclsAgree ds e` (every cell of `e`,
at every machine state, makes only accesses that `ds` resolves to their own
footprint: `X64VecDecls`) the two commute with `exec` (`exec_noDecls`, from
`X64VecDecls.exec_declsAgree`), so `execSimD` is an `ExecSim` and every
promise-free liveness theorem at `decls = {}` transfers to `decls = ds`
(`liveFrom_transfer`, `progressFrom_transfer`).

`CellsDeclsAgree` is a static per-image fact. For an image whose accesses are
all at absolute operands (`(next)`, `(lock)`, …) of a fixed width it reduces
to `ds.AgreesAt sym w` for each symbol (`cellsDeclsAgree_layoutL`, then one
`simp` sweep over the directives). **`AgreesAt` is weaker than the safety
side's `ds.Sized`** in the relevant sense: it asks only that the symbols the
code touches resolve to themselves (true for `{}` and for the runner's strict
sized declarations of a typed header), nothing about other declarations.
-/
import Kraken.Promising.LiveRunnerSim
import Kraken.Promising.SLR.EnvG.X64VecDecls

namespace Kraken.Promising.Live.RunnerX64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.RunnerSim

/-! ## The bridge -/

/-- The states the bridge covers: running the executable `e` with
declarations `ds`. -/
structure GD (ds : Decls) (e : _root_.Executable) (s : isa.State) : Prop where
  exe : s.exe = e
  decls : s.decls = ds

/-- The map: drop the declarations. -/
abbrev noD : isa.State → isa.State := State.noDecls

/-- **`exec` of the state without declarations** is `exec`, with the
declarations dropped in the leaves, when the cells agree. -/
theorem exec_noDecls {s : State} [Kraken.Executable.ValidLayout s.exe] (hc : CellsDeclsAgree s.decls s.exe) :
    isa.exec s.noDecls = (isa.exec s).map (EvTree.map State.noDecls) := by
  rw [exec_declsAgree hc]
  show exec s.noDecls = Option.map _ (Option.map _ (exec s.noDecls))
  unfold exec
  split
  · rfl
  · simp only [Option.map_some, evTree_map_map_vec]
    rfl

/-- **The x64 simulation**: `noD` commutes with `exec` on `GD ds e` when the
cells of `e` agree with `ds`. -/
theorem execSimD {ds : Decls} {e : _root_.Executable} [hv : Kraken.Executable.ValidLayout e]
    (hc : CellsDeclsAgree ds e) : ExecSim (I := isa) noD (GD ds e) where
  exec s hs := by
    obtain ⟨he, hd⟩ := hs
    haveI : Kraken.Executable.ValidLayout s.exe := he ▸ hv
    exact exec_noDecls (by rw [he, hd]; exact hc)
  deps _ _ := rfl
  showInstr _ _ := rfl
  leaves s hs tree h := by
    change exec s = some tree at h
    unfold exec at h
    split at h
    · cases h
    · cases h
      exact EvTree.All.map _ (fun _ => ⟨hs.exe, hs.decls⟩) _
  inj s s' hs hs' h := by
    obtain ⟨-, hd⟩ := hs
    obtain ⟨-, hd'⟩ := hs'
    have e := congrArg (State.withDecls ds) h
    cases s; cases s'
    simp only [State.withDecls] at e hd hd'
    subst hd hd'
    exact e

/-- A laid-out program's cells agree if every directive agrees at the
program's own labels (a copy of `X64VecPublish.cellsDeclsAgree_layoutP`,
which is in a program file). -/
theorem cellsDeclsAgree_layoutL [layout : _root_.Layout] {ds : Decls} {p : Program}
    (h : ∀ d ∈ p, ∀ (s : MachineData) (rng : Std.Rco Int64)
      (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects),
      (∀ s', (next s').DeclsAgree ds) → (∀ pc' s', (jmp pc' s').DeclsAgree ds) →
      Effects.DeclsAgree ds (@Directive.interp (_root_.Executable.labels (layout p)) d s rng next jmp)) :
    CellsDeclsAgree ds (layout p) := by
  intro d z hm s pc
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) _ _ _ _ (fun _ => trivial) (fun _ _ => trivial)

end Kraken.Promising.Live.RunnerX64

open Kraken.Promising.Live.RunnerX64 in
#print axioms execSimD
