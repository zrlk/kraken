/-
**wake.w: main's source facts for `main_closed_wakeW`**: the
source side of `A64WakeMainClosedW.main_closed_wakeW`'s `hrun`, `hterm`,
`hev`, `hval`, `htag` together with `hwb`, `hcPf`, `hcP`, `hfvP`, `hc0`,
`hfv0`, `hE`, `hfvE`, `hxc`, at main's control `cP` at `WakeM0.mTail`
(the tail call of `waitLoop`, past the spawn) with `c` bound to the flag's
word `w`.

- `waitBody_eq`: `WakeMainSrc.waitBody` is `WakeM0.wlBody`.
- `mTail_ne`: `mTail` is neither `wlBody` nor `wlIf` (`hcPf`), nor `wlRet`.
- `main_src_wake`: from `cP.term = mTail` and `c` bound to `w`, the loop's
  control `c0` (at `wlBody`, `x := "d"`, `e := wlIf`, `cv := "c"`) and every
  source premise of `main_closed_wakeW` listed above.
-/
import Spike.Lib.WakeMainSrc
import Spike.Lib.WakeM0

namespace Spike.Lib.WakeMainSrcW

open CoreLang CoreTerm
open Scc.Sem (ValRep)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeM0 (mTail wlBody wlIf wlPark)
open Spike.Lib.WakeMLive (wlRet)

/-- `WakeMainSrc.waitBody` is `WakeM0.wlBody`. -/
theorem waitBody_eq : WakeMainSrc.waitBody = wlBody := rfl

/-- `mTail` is neither `wlBody` nor `wlIf` (`main_closed_wakeW`'s `hcPf`),
nor `wlRet` (its `hcP`). -/
theorem mTail_ne : mTail ≠ wlBody ∧ mTail ≠ wlIf ∧ mTail ≠ wlRet := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mTail, wlBody, wlIf, wlRet]

/-- **main's source premises of `main_closed_wakeW`**: from main's control
`cP` at `mTail` with `c` bound to the word `w` (a locative at offset 0
placed at `A`), one local step to `c0` at `wlBody`, the flag load
`let d = load true c in wlIf`, with every source premise of
`main_closed_wakeW` at `x := "d"`, `e := wlIf`, `cv := "c"`. -/
theorem main_src_wake {lbl : WeakMem.AllocLabel → Option Nat} {A : BitVec 64} {cP : Spike.Lib.Ctl}
    {ty : Ty} {w : TermRun.Word} (ht : cP.term = mTail)
    (hc : TermRun.lookupE cP.env "c" = some (ty, [w])) (hval : ValRep lbl w.val A.toNat)
    (htag : ∃ sa, w.val = .loc sa 0) :
    ∃ c0 : Spike.Lib.Ctl,
      Spike.Lib.LocalRun wakeSrc cP c0 ∧ c0.term = .let_ "d" (.load true (.var "c")) wlIf ∧
      TermRun.evalAt c0.env (.var "c") = some (.ptr .pub .int, [w]) ∧ ValRep lbl w.val A.toNat ∧
      (∃ sa, w.val = .loc sa 0) ∧
      c0.term = wlBody ∧ (cP.term ≠ wlBody ∧ cP.term ≠ wlIf) ∧
      cP.term ≠ wlRet ∧ (∀ y ∈ Scc.Sem.exprFv cP.term, y = "c") ∧
      TermRun.lookupE c0.env "c" = some (.ptr .pub .int, [w]) ∧
      c0.term ≠ wlRet ∧ (∀ y ∈ Scc.Sem.exprFv c0.term, y = "c") ∧
      wlIf ≠ wlRet ∧ (∀ y ∈ Scc.Sem.exprFv wlIf, y = "d" ∨ y = "c") ∧ ("d" : String) ≠ "c" := by
  have hrun := WakeMainSrc.main_src_run (cP := cP) (ty := ty) (w := w) ht hc
  have hl : TermRun.lookupE (WakeMainSrc.waitC w).env "c" = some (.ptr .pub .int, [w]) := by
    simp [WakeMainSrc.waitC, TermRun.lookupE]
  refine ⟨_, hrun, rfl, hl, hval, htag, rfl, ⟨ht ▸ mTail_ne.1, ht ▸ mTail_ne.2.1⟩, ht ▸ mTail_ne.2.2, ?_, hl,
    ?_, ?_, ?_, ?_, by decide⟩
  · rw [ht]; simp [mTail, Scc.Sem.exprFv, Scc.Sem.atVars]
  · simp [WakeMainSrc.waitC, WakeMainSrc.waitBody, wlRet]
  · simp [WakeMainSrc.waitC, WakeMainSrc.waitBody, Scc.Sem.exprFv, Scc.Sem.atVars, Scc.Sem.opVars, Scc.Sem.opAts]
  · simp [wlIf, wlRet]
  · simp [wlIf, wlPark, wlRet, Scc.Sem.exprFv, Scc.Sem.atVars, Scc.Sem.opVars, Scc.Sem.opAts]

/-- info: 'Spike.Lib.WakeMainSrcW.main_src_wake' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_src_wake

end Spike.Lib.WakeMainSrcW
