/-
**Source typing across extern steps that are machine steps.**
`Scc/Sem/SrcStart.lean`'s `srcTyped_of_init` covers `SrcHooks.none` only.
WeakCore's token theorem (`machine_tokens_main_spawn`) is about
`StepsG … (Spawn p k arch cap)` runs: machine steps and spawns. An extern
step outside those is outside the theorem (`SrcHooks.ext` is an arbitrary
relation; DESIGN §8). An extern step that *is* a machine step of the same
thread, only labelled with events (`ExtIsStep`: `ext i c c'` implies
`StepBy p k arch i c c'`), adds no configuration step, so the runs of
`source P p` are still runs with spawns and the typing carries over.

- `ExtIsStep P p`: every extern step of `P.hooks` is a machine step
  (`StepBy`) of its thread; `extIsStep_none` for `SrcHooks.none`.
- `source_run_spawn_of`: under `ExtIsStep`, a run of `source P p` is a
  `StepsG … (Spawn p k arch cap)` run.
- `srcTyped_of_init_ext`: `srcTyped_of_init` for every hook with
  `ExtIsStep`.

The configuration (`TermRun.Cfg`) has no event list, so such a hook's
`trace` cannot record what its steps emitted; a hook that prints needs a
source configuration carrying the trace.
-/
import Scc.Sem.SrcStart

namespace Scc.Sem.SrcExtStep

open CoreLang CoreTerm TermRun TermSpawnStep
open Scc.Sem.PubFree Scc.Sem.SrcStart

/-- **Every extern step is a machine step of its thread**: the hook only
labels steps the machine takes anyway. -/
def ExtIsStep (P : SrcSem.SrcParams) (p : Prog) : Prop :=
  ∀ i c c', P.hooks.ext i c c' → SrcSem.StepBy p P.k P.arch i c c'

/-- `SrcHooks.none` has no extern step. -/
theorem extIsStep_none {P : SrcSem.SrcParams} {p : Prog} (hP : P.hooks = SrcSem.SrcHooks.none) :
    ExtIsStep P p :=
  fun _ _ _ h => by rw [hP] at h; exact h.elim

/-- **With extern steps that are machine steps, the runs of `source P p` are
runs with spawns** at capacity `P.cap`. -/
theorem source_run_spawn_of {P : SrcSem.SrcParams} {p : Prog} (hx : ExtIsStep P p)
    {c c' : Cfg} {tr : List Ev} (h : (SrcSem.source P p).Run c tr c') :
    StepsG p P.k P.arch (Spawn p P.k P.arch P.cap) c c' := by
  have key : ∀ {c c' : Cfg},
      StepsG p P.k P.arch (fun c c' => ∃ i, SrcSem.SpawnBy P.cap i c c' ∨ P.hooks.ext i c c') c c' →
      StepsG p P.k P.arch (Spawn p P.k P.arch P.cap) c c' := by
    intro c c' h
    induction h with
    | refl => exact .refl _
    | step hs _ ih =>
      refine .step ?_ ih
      rcases hs with hs | ⟨i, hs | hs⟩
      · exact .inl hs
      · exact .inr hs.spawn
      · exact .inl (hx i _ _ hs).step
  exact key (SrcSem.source_run_stepsG h)

/-- **Every configuration the source reaches is typed**, for a program
passing `SrcChecks`, with the source's default knobs, the `main` start and an
extern hook whose steps are machine steps. -/
theorem srcTyped_of_init_ext {p : Prog} {r : Ty} (hp : SrcChecks p r) {P : SrcSem.SrcParams}
    (hk : P.k = Promises.Knobs.all) (hi : P.init = SrcSem.mainInit P.cap) (hx : ExtIsStep P p) :
    ∀ tr s, (SrcSem.source P p).Reach tr s → SrcTyped p s := by
  rintro tr s ⟨s0, h0, hr⟩
  change P.init s0 at h0
  rw [hi] at h0
  subst h0
  have hks : P.k.storeDepRts = true := by rw [hk]; rfl
  exact srcTyped_spawn_of_noPublish (Init := .zero) hp.checked hp.scope runScope_main hp.noPub runPF_main hks
    (startOKX_main hp.entry) (source_run_spawn_of hx hr)

/-! ## Test -/

/-- A hook whose extern steps are the machine steps of thread 0 (with an
empty event list): it satisfies `ExtIsStep` by construction. -/
def stepHook (p : Prog) : SrcSem.SrcHooks :=
  ⟨fun i c c' => i = 0 ∧ SrcSem.StepBy p Promises.Knobs.all .arm i c c', fun _ => []⟩

/-- The test parameters of `SrcStart` with `stepHook`. -/
def testPx : SrcSem.SrcParams := { testP with hooks := stepHook [mainD] }

/-- **End to end with a non-empty hook**: every configuration the test
program reaches is typed. -/
theorem srcTyped_main_ext : ∀ tr s, (SrcSem.source testPx [mainD]).Reach tr s → SrcTyped [mainD] s :=
  srcTyped_of_init_ext srcChecks_main rfl rfl fun _ _ _ h => h.2

end Scc.Sem.SrcExtStep
