/-
**The setup block's call is a source call** (x86-64; the twin of
`Spike/Lib/LowerA64/SetupHCall.lean`): the `hcall` premise
`∃ cE fr, CallTo p c0 cE fr` of `mainSC_segWS` and the h0 wrappers
(`Spike/Lib/Rt/X64MainSS.lean`, `Spike/Lib/LowerX64/Start2W2.lean`) at a
control at `setupTerm` (`let r = call rodata u in setupRest`).

- `callTo_setupTerm`: at `setupTerm` with `u` bound, and `rodata` a
  declaration of `p`, the call is `CallTo` into `rodata`'s body with the
  frame returning into `r` and `setupRest`;
- `CallTo.unique`: the callee's control and the frame are determined by the
  caller's control (so `hPS` is asked at one pair only);
- `hcall_of_setupOf`: for an `Accepted2` program with a setup block
  (`setupOf p = some s`, `rodata_of_setupOf`), `hcall` at such a control;
- `hcall_setupStart`: `hcall` at the start's thread (`setupStart`'s:
  `me` the main thread's word, `u` the unit).
-/
import Spike.Lib.X64CallS
import Spike.Lib.Src.NumQLower

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Sem.SrcSem (setupTerm)
open Spike.Lib.LowerNode (setupRest setupTerm_eq rodata_of_setupOf)

/-- **The setup block's call at `setupTerm`**: with `u` bound to `(t, ws)`
and `rodata` a declaration `d` of `p`, the control calls `rodata`'s body on
`ws`, the frame returning into `r` and `setupRest` in the caller's
environment. -/
theorem callTo_setupTerm {p : Prog} {c0 : Ctl} {t : Ty} {ws : List TermRun.Word} {d : Decl}
    (ht : c0.term = setupTerm) (hu : TermRun.evalAt c0.env (.var "u") = some (t, ws))
    (hd : p.find? (·.name == "rodata") = some d) :
    Spike.Lib.X64.Flow.CallTo p c0 ⟨d.body, [(d.arg, d.argTy, ws)], none⟩ ⟨"r", setupRest, c0.env, [], d.retTy⟩ :=
  ⟨"r", "rodata", .var "u", setupRest, d, t, ws, by rw [ht, setupTerm_eq], hd, hu, rfl, rfl⟩

/-- **A source call's callee and frame are determined by the caller's
control.** -/
theorem CallTo.unique {p : Prog} {c cE cE' : Ctl} {fr fr' : TermRun.Frame}
    (h : Spike.Lib.X64.Flow.CallTo p c cE fr) (h' : Spike.Lib.X64.Flow.CallTo p c cE' fr') :
    cE = cE' ∧ fr = fr' := by
  obtain ⟨x, f, a, e, d, t, ws, ht, hd, ha, rfl, rfl⟩ := h
  obtain ⟨x', f', a', e', d', t', ws', ht', hd', ha', rfl, rfl⟩ := h'
  rw [ht] at ht'
  cases ht'
  rw [hd] at hd'
  cases hd'
  rw [ha] at ha'
  cases ha'
  exact ⟨rfl, rfl⟩

/-- **`hcall` for an `Accepted2` program with a setup block**: at a control
at `setupTerm` with `u` bound, the setup block's call is a source call
(`rodata` is a declaration, `rodata_of_setupOf`). -/
theorem hcall_of_setupOf {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {s : Ty}
    (hs : Scc.Lower.setupOf p = some s) {c0 : Ctl} {t : Ty} {ws : List TermRun.Word}
    (ht : c0.term = setupTerm) (hu : TermRun.evalAt c0.env (.var "u") = some (t, ws)) :
    ∃ cE fr, Spike.Lib.X64.Flow.CallTo p c0 cE fr :=
  let ⟨_, hd, _⟩ := rodata_of_setupOf hp hs
  ⟨_, _, callTo_setupTerm ht hu hd⟩

/-- **`hcall` at the start's thread** (`setupStart`'s: `setupTerm`, `me` the
main thread's word `meW`, `u` the unit). -/
theorem hcall_setupStart {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {s : Ty}
    (hs : Scc.Lower.setupOf p = some s) (meW : TermRun.Word) :
    ∃ cE fr, Spike.Lib.X64.Flow.CallTo p ⟨setupTerm, [("me", .ptr .pub .void, [meW]), ("u", .unit, [])], none⟩
      cE fr :=
  hcall_of_setupOf hp hs (t := .unit) (ws := []) rfl (by simp [TermRun.evalAt, TermRun.lookupE])

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hcall_setupStart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hcall_setupStart

/-- info: 'Spike.Lib.LowerX64.CallTo.unique' does not depend on any axioms -/
#guard_msgs in #print axioms CallTo.unique

end Spike.Lib.LowerX64
