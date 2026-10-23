/-
**Results for any source whose core runs are WeakCore's runs with spawns.**
`Sim.transfer_source` (`Scc/Sem/Correct.lean`), `srcTyped_of_init`
(`Scc/Sem/SrcStart.lean`), `threads_abort_unjustified`
(`Scc/Sem/Target.lean`) and `not_correct_event_after_exit`
(`Scc/Sem/Holes.lean`) are stated for `SrcSem.source P p`, whose
configurations are `TermRun.Cfg`. WeakCore's extern step will fix the
source's final shape (possibly a configuration with an event list beside the
core one). Here they are stated for every `S : SrcSem` whose steps project,
through `S.core`, to a machine step, a spawn, or no core change of the same
thread (`CoreProj`), so they hold for whichever source lands.

- `CoreStep`, `CoreProj S p k arch cap I0`: every step of `S` is a
  `CoreStep` on the cores, and every start's core satisfies `I0`.
  `CoreProj.run`: a run of `S` projects to a `StepsG … (Spawn …)` run.
- `coreProj_source`: `source P p` is an instance when its extern steps are
  machine steps (`SrcExtStep.ExtIsStep`; `SrcHooks.none` included).
- `transfer_proj`: `Sim.transfer_source` for a `CoreProj` source.
- `srcTyped_proj`, `transfer_typed`: `srcTyped_of_init` for a `CoreProj`
  source started at `SrcSem.mainInit cap`, and its transfer to the target.
- `threads_abort_unjustified_proj`: a `threads` abort with thread capacity
  within `B.threads` and no refused `clone` is never justified.
- `ExitFinal S`, `not_correct_event_after_exit_of`: no source trace has an
  event after an exit, hence a target with trace `[exit 0, exit 0]` is not
  `Correct`; `exitFinal_source` for `source P p` with a growing hook.
-/
import Scc.Sem.SrcExtStep
import Scc.Sem.Holes
import Scc.Sem.Target

namespace Scc.Sem.SrcProj

open Kraken.Promising
open CoreLang CoreTerm TermRun TermSpawnStep
open Scc.Sem.PubFree Scc.Sem.SrcStart Scc.Sem.SrcExtStep

/-! ## Core projection -/

/-- **A core step of thread `i`**: no change, a machine step of `i`
(`StepBy`), or a spawn by `i` at capacity `cap`. -/
def CoreStep (p : Prog) (k : Promises.Knobs) (arch : WeakMem.Arch) (cap i : Nat) (c c' : Cfg) : Prop :=
  c' = c ∨ SrcSem.StepBy p k arch i c c' ∨ SrcSem.SpawnBy cap i c c'

/-- **The source's cores run WeakCore's machine with spawns**: every start's
core satisfies `I0`, and every step of thread `i` is a core step of `i`. -/
structure CoreProj (S : SrcSem) (p : Prog) (k : Promises.Knobs) (arch : WeakMem.Arch) (cap : Nat)
    (I0 : Cfg → Prop) : Prop where
  init : ∀ s, S.init s → I0 (S.core s)
  step : ∀ i s es s', S.step i s es s' → CoreStep p k arch cap i (S.core s) (S.core s')

namespace CoreProj

variable {S : SrcSem} {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {cap : Nat} {I0 : Cfg → Prop}

/-- A run of the source projects to a run with spawns. -/
theorem run (hP : CoreProj S p k arch cap I0) {s s' : S.Cfg} {tr : List Ev} (h : S.Run s tr s') :
    StepsG p k arch (Spawn p k arch cap) (S.core s) (S.core s') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih =>
    obtain ⟨i, hs⟩ := hs
    rcases hP.step _ _ _ _ hs with he | hs | hs
    · rw [← he]; exact ih
    · exact .step (.inl hs.step) ih
    · exact .step (.inr hs.spawn) ih

/-- A reachable source configuration's core is reached by a run with spawns
from a core satisfying `I0`. -/
theorem reach (hP : CoreProj S p k arch cap I0) {s : S.Cfg} {tr : List Ev} (h : S.Reach tr s) :
    ∃ c0, I0 c0 ∧ StepsG p k arch (Spawn p k arch cap) c0 (S.core s) :=
  let ⟨s0, h0, hr⟩ := h
  ⟨S.core s0, hP.init s0 h0, hP.run hr⟩

/-- A step keeps the number of threads or adds one below the capacity. -/
theorem step_size (hP : CoreProj S p k arch cap I0) {i : Nat} {s s' : S.Cfg} {es : List Ev}
    (h : S.step i s es s') : (S.core s').ths.size ≤ max (S.core s).ths.size cap := by
  rcases hP.step _ _ _ _ h with he | hs | hs
  · rw [he]; exact Nat.le_max_left _ _
  · rw [SrcSem.stepBy_size hs]; exact Nat.le_max_left _ _
  · have := SrcSem.spawnBy_size hs; omega

end CoreProj

/-- **`source P p` is a `CoreProj` source** when its extern steps are machine
steps. -/
theorem coreProj_source {P : SrcSem.SrcParams} {p : Prog} (hx : ExtIsStep P p) :
    CoreProj (SrcSem.source P p) p P.k P.arch P.cap P.init where
  init _ h := h
  step i _ _ _ h := by
    obtain ⟨-, hs | hs | hs, -⟩ := h
    · exact .inr (.inl hs)
    · exact .inr (.inr hs)
    · exact .inr (.inl (hx i _ _ hs))

/-! ## Transfer -/

section Transfer

variable {T : Target} {S : SrcSem} {Λ : Layout} {B : Budget} {asm : T.Asm}

/-- **Transfer of a WeakCore safety result to a `CoreProj` source**: a
property of every configuration reachable along runs with spawns from `I0`
holds of the core of a source configuration related to each reachable
target configuration. -/
theorem transfer_proj (h : Sim T S Λ B asm) {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch}
    {cap : Nat} {I0 : Cfg → Prop} (hP : CoreProj S p k arch cap I0) {Q : Cfg → Prop}
    (hQ : ∀ c0 c, I0 c0 → StepsG p k arch (Spawn p k arch cap) c0 c → Q c)
    {t0 t : T.M.Cfg} {tr : List Ev} (h0 : T.load asm Λ = some t0) (hr : T.M.Run (T.marks asm Λ) t0 tr t) :
    ∃ s, h.R t s ∧ Q (S.core s) ∧ ∃ w : Witness T.M, Components T.M Λ w t (S.core s) :=
  h.transfer (Inv := fun s => Q (S.core s))
    (fun _ _ hs => let ⟨c0, hi, hrun⟩ := hP.reach hs; hQ c0 _ hi hrun) h0 hr

/-- **Every configuration a `CoreProj` source reaches from `main`'s start
has a typed core**, for a program passing `SrcChecks`, with all knobs on. -/
theorem srcTyped_proj {p : Prog} {r : Ty} (hp : SrcChecks p r) {arch : WeakMem.Arch} {cap : Nat}
    (hP : CoreProj S p Promises.Knobs.all arch cap (SrcSem.mainInit cap)) :
    ∀ tr s, S.Reach tr s → SrcTyped p (S.core s) := by
  intro tr s hs
  obtain ⟨c0, h0, hr⟩ := hP.reach hs
  change c0 = _ at h0
  subst h0
  exact srcTyped_spawn_of_noPublish (Init := .zero) hp.checked hp.scope runScope_main hp.noPub runPF_main
    storeDepRts_all (startOKX_main hp.entry) hr

/-- **Source typing at the target**: each reachable target configuration is
related to a source configuration with a typed core. -/
theorem transfer_typed (h : Sim T S Λ B asm) {p : Prog} {r : Ty} (hp : SrcChecks p r) {arch : WeakMem.Arch}
    {cap : Nat} (hP : CoreProj S p Promises.Knobs.all arch cap (SrcSem.mainInit cap))
    {t0 t : T.M.Cfg} {tr : List Ev} (h0 : T.load asm Λ = some t0) (hr : T.M.Run (T.marks asm Λ) t0 tr t) :
    ∃ s, h.R t s ∧ SrcTyped p (S.core s) ∧ ∃ w : Witness T.M, Components T.M Λ w t (S.core s) :=
  h.transfer (Inv := fun s => SrcTyped p (S.core s)) (srcTyped_proj hp hP) h0 hr

end Transfer

/-! ## The `threads` abort -/

/-- **A `threads` abort is not justified** for a `CoreProj` source whose
thread capacity is within `B.threads`, when no `clone` was refused (the
generalisation of `threads_abort_unjustified`). -/
theorem threads_abort_unjustified_proj {S : SrcSem} {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch}
    {cap : Nat} {I0 : Cfg → Prop} (hP : CoreProj S p k arch cap I0) {B : Budget} (hcap : cap ≤ B.threads)
    {tr : List Ev} (hc : Ev.cloneErr ∉ tr) {s : S.Cfg} {i : Nat} : ¬ AbortJustified B S tr s i .threads := by
  rintro (h | ⟨es, s', hs, hle, hgt⟩)
  · exact hc h
  apply hgt
  show (S.core s').ths.size ≤ B.threads
  have hle' : (S.core s).ths.size ≤ B.threads := hle
  have := hP.step_size hs
  omega

/-! ## No event after an exit -/

/-- **No source trace has an event after an exit.** -/
def ExitFinal (S : SrcSem) : Prop :=
  ∀ tr s, S.Reach tr s → ∀ pre (c : Fin 256) rest, tr = pre ++ .exit c :: rest → rest = []

/-- `source P p` has `ExitFinal` when its hook's event list is empty at the
start and only grows (`source_run_trace`, `cutAtExit_exit_last`). -/
theorem exitFinal_source {P : SrcSem.SrcParams} {p : Prog}
    (hinit : ∀ c, P.init c → SrcSem.srcObs P.hooks.trace c = [])
    (hgrow : ∀ i c c', SrcSem.StepBy p P.k P.arch i c c' ∨ SrcSem.SpawnBy P.cap i c c' ∨ P.hooks.ext i c c' →
      P.hooks.trace c <+: P.hooks.trace c') :
    ExitFinal (SrcSem.source P p) := by
  rintro tr s ⟨s0, hs0, hr⟩ pre c rest rfl
  have ht := SrcSem.source_run_trace hgrow hr
  rw [hinit _ hs0, List.nil_append] at ht
  exact SrcSem.cutAtExit_exit_last ht

/-- **Rejected for every `ExitFinal` source: an event after the exit**
(`Holes.not_correct_event_after_exit` for any source shape). -/
theorem not_correct_event_after_exit_of (I : ISA) (A : Arch) (st : I.State) {S : SrcSem} (hS : ExitFinal S) :
    ¬ Correct (Holes.exitTwice I A st) S trivLayout Holes.noBudget () := by
  rintro ⟨h⟩
  obtain ⟨tr', s, hs, -, hp⟩ := h.sim _ [.exit 0, .exit 0] _ rfl
    (LRun.step (es := [.exit 0]) (tr := [.exit 0]) ⟨0, .sys ⟨by simp, rfl⟩ (.inl ⟨rfl, rfl, rfl⟩) (by simp)
        (by simp) (fun _ _ _ _ h => by simp [Target.marks] at h)⟩
      (LRun.step (es := [.exit 0]) (tr := []) ⟨0, .sys ⟨by simp, rfl⟩ (.inr ⟨rfl, rfl, rfl⟩) (by simp) (by simp)
        (fun _ _ _ _ h => by simp [Target.marks] at h)⟩ (.refl _)))
  obtain ⟨d, rfl⟩ := hp
  have he : obs [.exit 0, .exit 0] ++ d = [] ++ .exit 0 :: (.exit 0 :: d) := by
    simp [obs, List.filter_cons, Ev.isObs]
  exact absurd (hS _ s (he ▸ hs) [] 0 _ rfl) (by simp)

/-! ## Tests -/

/-- `SrcStart`'s test source is a `CoreProj` source. -/
theorem coreProj_test : CoreProj (SrcSem.source testP [mainD]) [mainD] Promises.Knobs.all .arm 4
    (SrcSem.mainInit 4) :=
  coreProj_source (extIsStep_none rfl)

/-- Its configurations are typed, through the generic route. -/
theorem srcTyped_test : ∀ tr s, (SrcSem.source testP [mainD]).Reach tr s → SrcTyped [mainD] s :=
  srcTyped_proj srcChecks_main coreProj_test

/-- With the hook of `SrcExtStep`'s test (extern steps that are machine
steps) as well. -/
theorem srcTyped_testx : ∀ tr s, (SrcSem.source testPx [mainD]).Reach tr s → SrcTyped [mainD] s :=
  srcTyped_proj srcChecks_main (coreProj_source fun _ _ _ h => h.2)

/-- **A source with a non-trivial core projection**: configurations carry a
step counter beside the core, and a step either advances the counter
(leaving the core) or takes a machine step. -/
def countSrc (p : Prog) : SrcSem where
  Cfg := Cfg × Nat
  core := Prod.fst
  init s := SrcSem.mainInit 4 s.1 ∧ s.2 = 0
  step i s _ s' := (s'.1 = s.1 ∧ s'.2 = s.2 + 1) ∨ (SrcSem.StepBy p Promises.Knobs.all .arm i s.1 s'.1 ∧ s'.2 = s.2)

theorem coreProj_count (p : Prog) : CoreProj (countSrc p) p Promises.Knobs.all .arm 4 (SrcSem.mainInit 4) where
  init _ h := h.1
  step _ _ _ _ h := by
    rcases h with ⟨h, -⟩ | ⟨h, -⟩
    · exact .inl h
    · exact .inr (.inl h)

/-- Typing for the counter source, a configuration type other than
`TermRun.Cfg`. -/
theorem srcTyped_count : ∀ tr s, (countSrc [mainD]).Reach tr s → SrcTyped [mainD] s.1 :=
  srcTyped_proj srcChecks_main (coreProj_count _)

/-- The `threads` abort for the test source at a budget of four threads. -/
theorem threads_test {tr : List Ev} (hc : Ev.cloneErr ∉ tr) {s : Cfg} {i : Nat} :
    ¬ AbortJustified ⟨0, 4, 0⟩ (SrcSem.source testP [mainD]) tr s i .threads :=
  threads_abort_unjustified_proj coreProj_test (by decide) hc

end Scc.Sem.SrcProj
