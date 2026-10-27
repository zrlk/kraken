/-
**The source safety of an `Accepted2` program at every start of the
program** (`progInit`): with a setup block the start is before it
(`setupStart`), without one at `main` on a unit argument (`mainStart`); both
keep `CfgB` and are free of `AcqOp`, so `SrcSafeS` holds at WeakCore's output
hooks (`srcP1o arch p`) for every frame invariant (`srcSafeS_srcP1oX` in
`Spike/Lib/Src/SrcSafe2X.lean`, `srcSafeS_srcP1oA` in
`Spike/Lib/Src/SrcSafe2A.lean`).

- `cfgB_mainStart`, `mainStart_noAcq`: `main`'s start.
- `progInit_cfgB`: every start of an `Accepted2` program.
-/
import Spike.Lib.Src.SrcSafe2
import Spike.Lib.Src.NoAcq
import Spike.Lib.Src.Accepted2Out

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm A9NoSpawn TermRun Scc.Sem

/-- `main`'s start keeps the invariant: its one thread is a tail call. -/
theorem cfgB_mainStart (cap : Nat) : CfgB { SrcSem.mainStart with cap := cap } := by
  intro j th hj
  have : j = 0 := by
    rcases j with _ | j
    · rfl
    · simp [SrcSem.mainStart] at hj
  subst this
  simp only [SrcSem.mainStart, List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hj
  subst hj
  exact ⟨Or.inr (by simp [NoS]), by simp⟩

/-- `main`'s start is free of `AcqOp`. -/
theorem mainStart_noAcq (cap : Nat) : CfgNoS AcqOp { SrcSem.mainStart with cap := cap } := by
  intro j th hj
  have : j = 0 := by
    rcases j with _ | j
    · rfl
    · simp [SrcSem.mainStart] at hj
  subst this
  simp only [SrcSem.mainStart, List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hj
  subst hj
  exact ⟨by simp [NoS], by simp⟩

/-- **Every start of an `Accepted2` program** keeps the invariant and is
free of `AcqOp`. -/
theorem progInit_cfgB {p : Prog} (hA : Scc.Lower.Accepted2 p = true) {cap : Nat} {c : Cfg}
    (h : SrcSem.progInit p cap c) : CfgB c ∧ CfgNoS AcqOp c := by
  cases hs : Scc.Lower.setupOf p with
  | some _ =>
    rw [progInit_of_setupOf_some hs] at h
    exact ⟨cfgB_setupStart h, setupInit_noAcq h⟩
  | none =>
    rw [progInit_of_setupOf_none hA hs] at h
    change c = _ at h
    subst h
    exact ⟨cfgB_mainStart cap, mainStart_noAcq cap⟩

/--
info: 'Spike.Lib.LowerNode.progInit_cfgB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms progInit_cfgB

end Spike.Lib.LowerNode
