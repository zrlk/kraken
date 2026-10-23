/-
**Certification under a code semantics `cexec`** (`CertOkC`, the canonical
targets' `Kernel.certExec`), for any ISA, extracted from the closed toys
`Spike/Lib/A64ExtToy.lean` and `Spike/Lib/A64ExtToy2.lean`.

- `stepC_silent`: a certification step (`ThreadStepC`) at a `SilentTree`
  keeps memory and promises and ends at a leaf (as `Spike.Lib.k_silent_out`,
  under `cexec`).
- `stepC_dead`: there is no certification step at a dead end (`.choose 0`:
  `exit_group` under `certExec`).
- `no_certOkC_of_closed`: from states of an invariant kept by every
  certification step, with the promises, no certification empties a
  non-empty promise set.
- `no_certOkC_of_silent`: the same when every tree `cexec` yields from the
  invariant is silent with leaves in it: **code that never writes memory
  certifies no promise**.
-/
import Scc.Sem.Ext
import Kraken.Promising.Lower.Silent

namespace Spike.Bridge.CertC

open Kraken.Promising Kraken.Promising.Lower Scc.Sem

variable {I : ISA} {A : Arch} {cs : CertSem I} {tid : Nat}

/-- **A certification step at a silent tree** (as `Spike.Lib.k_silent_out`,
under `cexec`): the memory and the promises stay, the thread is at a leaf. -/
theorem stepC_silent {t : Thread I} {mem : Memory} {q : Thread I × Memory} {tree : EvTree I.State}
    {P : I.State → Prop} (hex : cs.exec t.st = some tree) (hs : SilentTree P tree)
    (h : ThreadStepC A cs tid (t, mem) q) : q.2 = mem ∧ q.1.prom = t.prom ∧ P q.1.st := by
  obtain ⟨outs, o, hso, ho, rfl⟩ := h
  simp only [CertSem.step, stepOneWithD, hex, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq] at hso
  subst hso
  rw [List.mem_flatMap] at ho
  obtain ⟨x, hx, ho⟩ := ho
  obtain ⟨s, hP, rfl⟩ := hs.run A tid _ hx
  simp only [List.mem_map, Except.ok.injEq] at ho
  obtain ⟨th, hth, rfl⟩ := ho
  exact ⟨rfl, (finishInstr_relKey hth).1, (finishInstr_st hth) ▸ hP⟩

/-- A certification step at a dead end (`exit_group`: no branch) has no outcome. -/
theorem stepC_dead {t : Thread I} {mem : Memory} {q : Thread I × Memory} {n : Nat} {f : Fin n → EvTree I.State}
    (hex : cs.exec t.st = some (.choose n f)) (hn : n = 0) : ¬ ThreadStepC A cs tid (t, mem) q := by
  subst hn
  rintro ⟨outs, o, hso, ho, -⟩
  simp only [CertSem.step, stepOneWithD, hex, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq] at hso
  subst hso
  simp [runTree] at ho

/-- A state at which `cexec` yields nothing has no certification step. -/
theorem stepC_none {t : Thread I} {mem : Memory} {q : Thread I × Memory} (hex : cs.exec t.st = none) :
    ¬ ThreadStepC A cs tid (t, mem) q := by
  rintro ⟨outs, o, hso, -, -⟩
  simp [CertSem.step, stepOneWithD, hex] at hso

/-- **No certification from an invariant empties a promise set**, when every
certification step from it keeps the promises and the invariant. -/
theorem no_certOkC_of_closed {Q : I.State → Prop}
    (hQ : ∀ (t : Thread I) mem q, Q t.st → ThreadStepC A cs tid (t, mem) q → q.1.prom = t.prom ∧ Q q.1.st)
    {t : Thread I} {mem : Memory} (hc : Q t.st) (hp : t.prom ≠ []) : ¬ CertOkC A cs tid t mem := by
  rintro ⟨t', mem', hrun, hp'⟩
  suffices H : ∀ q q', ThreadNPC A cs tid q q' → Q q.1.st → q.1.prom ≠ [] → q'.1.prom ≠ [] from
    H _ _ hrun hc hp hp'
  intro q q' hr
  induction hr with
  | refl => exact fun _ h => h
  | step hs _ ih =>
    intro hc hp
    obtain ⟨hpr, hc'⟩ := hQ _ _ _ hc hs
    exact ih hc' (hpr ▸ hp)

/-- **Code that never writes memory certifies no promise**: if every tree
`cexec` yields from the invariant `Q` is silent with its leaves in `Q`, no
certification from `Q` empties a non-empty promise set. -/
theorem no_certOkC_of_silent {Q : I.State → Prop}
    (hs : ∀ s, Q s → ∀ tree, cs.exec s = some tree → SilentTree Q tree)
    {t : Thread I} {mem : Memory} (hc : Q t.st) (hp : t.prom ≠ []) : ¬ CertOkC A cs tid t mem := by
  refine no_certOkC_of_closed (fun t mem q hq h => ?_) hc hp
  cases hex : cs.exec t.st with
  | none => exact absurd h (stepC_none hex)
  | some tree =>
    obtain ⟨-, hpr, hP⟩ := stepC_silent hex (hs _ hq _ hex) h
    exact ⟨hpr, hP⟩

end Spike.Bridge.CertC
