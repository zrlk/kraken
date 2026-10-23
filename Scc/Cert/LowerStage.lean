import Scc.Lower.Spec

/-!
# The lowering in two kernel steps (`scc --cert`, both ISAs)

A certificate checks `lowered1 config prog_src = some loweredLit`
(`Scc/Cert/OutStageA64.lean`, `OutStageX64.lean`): the kernel runs
`lowerIR`. That lowers the program twice: once at depth limit `0` for the
frames (`stackBudget`), and once more at the resulting limit
(`lowerWithMarks`). Checked as one definitional equality, the kernel keeps
the intermediate terms of both runs alive in one declaration (on a large x64
program, 9 GB).

This module splits it into two equations on literals, each one lowering:

* `frames1 cfg p = some fr`: the depth limit `stackBudget` computes
  (`StackBudget.frames`);
* `ir1 cfg p fr = some (ir, setup)`: the lowering at the limit `fr`
  (`lowerWith`), and whether `scc_rt_main` has a setup block.

`lowerIR_of_stages` gives `lowerIR`'s IR and setup flag from them, which each
ISA's `lowered1_of_stages` states as `lowered1 cfg p = some (ir, setup)`.
-/

namespace Scc.Cert.LowerStage

open CoreTerm

/-- **The depth limit** of `p`'s lowering (`none`: the frontend's entry or
the budget fails). -/
def frames1 (cfg : Scc.Config) (p : Prog) : Option Nat :=
  match Scc.Lower.checkedOf p >>= Scc.Lower.stackBudget cfg with
  | .ok b => some b.frames
  | .error _ => none

/-- **The lowering at depth limit `fr`**: the IR and whether `scc_rt_main`
has a setup block (`none`: the lowering fails). -/
def ir1 (cfg : Scc.Config) (p : Prog) (fr : Nat) : Option (Scc.IR.Program × Bool) :=
  match Scc.Lower.checkedOf p with
  | .ok c =>
    match Scc.Lower.lowerWith cfg c (some fr) with
    | .ok ir => some (ir, c.entry.arg == .setupTid)
    | .error _ => none
  | .error _ => none

/-- **`lowerIR` from its stages**: where the budget gives the depth limit
`fr` and the lowering at `fr` gives `r`, `lowerIR`'s IR and setup flag are
`r`. -/
theorem lowerIR_of_stages {cfg : Scc.Config} {p : Prog} {fr : Nat} {r : Scc.IR.Program × Bool}
    (h1 : frames1 cfg p = some fr) (h2 : ir1 cfg p fr = some r) :
    (match Scc.Lower.lowerIR cfg p with
      | .ok l => some (l.ir, l.checked.entry.arg == .setupTid)
      | .error _ => none) = some r := by
  unfold frames1 at h1
  unfold ir1 at h2
  unfold Scc.Lower.lowerIR
  cases hc : Scc.Lower.checkedOf p with
  | error e => simp [hc] at h2
  | ok c =>
    simp only [hc] at h1 h2
    cases hb : Scc.Lower.stackBudget cfg c with
    | error e => simp [hb, bind, Except.bind] at h1
    | ok b =>
      simp only [hb, bind, Except.bind, Option.some.injEq] at h1
      subst h1
      unfold Scc.Lower.lowerWith at h2
      cases hm : Scc.Lower.lowerWithMarks cfg c (some b.frames) with
      | error e => simp [hm, Functor.map, Except.map] at h2
      | ok m =>
        simp only [hm, Functor.map, Except.map] at h2
        simp only [bind, Except.bind, pure, Except.pure, hb, hm]
        rw [← h2]

end Scc.Cert.LowerStage
