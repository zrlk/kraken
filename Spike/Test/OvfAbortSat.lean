/-
**Satisfiability of `AbortPath.at_`'s overflow case** (`Spike/Lib/OvfAbort.lean`):
the control of `Scc/Test/overflow.w`'s addition, `let s = big + 1 in ret s`
with `big` bound to `2^64 - 1`, is about to overflow (`OvfReady`) in a small
environment (`EnvSmall`). The run of that program aborts with status 101
(`Scc/Test/overflow.code`, `Scc/Test/run.sh`).
-/
import Spike.Lib.OvfAbort

namespace Spike.Test.OvfAbortSat

open CoreLang CoreTerm Spike.Lib

/-- `let s = big + 1 in ret s`, `big` bound to `2^64 - 1`. -/
def cOvf : Ctl := ⟨.let_ "s" (.add (.var "big") (.lit 1)) (.ret (.var "s")),
  [("big", .int, [TermRun.cst (.num (2 ^ 64 - 1))])], none⟩

/-- **The overflow case is satisfiable.** -/
theorem cOvf_ok : OvfReady cOvf ∧ EnvSmall cOvf.env := by
  refine ⟨⟨"s", .var "big", .lit 1, .ret (.var "s"), .int, .intS (.lit 1), TermRun.cst (.num (2 ^ 64 - 1)),
    TermRun.cst (.num 1), 2 ^ 64 - 1, 1, rfl, ?_, ?_, rfl, rfl, by omega⟩, ?_⟩
  · rfl
  · rfl
  · intro b hb w hw n hn
    simp [cOvf] at hb; subst hb
    simp at hw; subst hw
    simp [TermRun.cst, Promises.TVal.mk0] at hn; omega

end Spike.Test.OvfAbortSat
