/-
**The concrete control fact's source premises, x86-64** (the twin of `Spike/Lib/A64HelloZSrc.lean`): the control
facts `X64HelloZ`'s and `X64HelloZR`'s node lemmas ask, at hello's worker controls (`X64HelloSplit.wcP`, `wcR`,
the controls past the store, `print`'s predicate `X64HelloWorkerCallSrc.PrW`).

- `unpk_noStep`: no local step at an `unpark` binding (an extern).
- `prW_notUnpk`: `print`'s predicate's controls are at no `unpark` binding (`wc_hZP`'s, `wc_hZA`'s premises at
  `PrW`).
- `kcW_notPass`, `wcP_notPass`, `wcR_notPass`: the call's and the store's controls are before the store
  (`wc_hZC`, `wc_hz`, `wc_hZE`, `wc_hZW`).
- `c1_pass`, `c2_pass`: the controls after the store and the `unpark`, past it (`wc_hZW`, `wc_hZU`).

Unlike AArch64: the call's control fact `KcW` also pins the count register `%rsi` (AArch64: `x1`), which plays no
part here; the source program is `X64HelloSrc.helloSrc` and the local runs' case split `X64HelloW1`'s.
-/
import Spike.Lib.X64HelloZ
import Spike.Lib.X64HelloWorkerCallSrc

namespace Spike.Lib.X64.Flow.Worker.Hello.Z

open CoreLang CoreTerm TermRun
open Spike.Lib
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloSplit (envP wcP wcR workerRestH workerCallH)
open Spike.Lib.X64HelloWorkerCallSrc (PrW KcW)
open Spike.Lib.X64HelloPrintSrcPub (PrintCP printLBodyP)
open Spike.Lib.X64.Flow.Worker.Hello.Pass (HPassC)
open Spike.Lib.WorkerSrc (wkUnpark)

/-- **No local step at an `unpark` binding** (an extern). -/
theorem unpk_noStep {c c₁ : Ctl} (h : LocalStepS helloSrc c c₁) {x : String} {a : CoreTerm.At} {e : Expr}
    (ht : c.term = .let_ x (.ext .unpark a) e) : False := by
  have := h.2 { p := helloSrc, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 } #[] []
    { term := c.term, env := c.env } rfl rfl rfl rfl
  simp [TermRun.tstep, ht, TermRun.evalOp] at this

/-- **`print`'s predicate's controls are at no `unpark` binding**: one has no local step, and `printL`'s top is no
binding of an extern. -/
theorem prW_notUnpk {pw wn : Word} {n m k : Nat} {c : Ctl} (h : PrW pw wn n m k c) : NotUnpk c := by
  intro x a e ht
  obtain ⟨⟨c1, hr, i, j, hc1, -⟩, -⟩ := h
  rcases X64HelloW1.localRunS_cases hr with rfl | ⟨c₂, hs⟩
  · rw [hc1] at ht; simp [printLBodyP] at ht
  · exact unpk_noStep hs ht

theorem wcP_notPass (w0 w1 w2 w3 w4 : Word) : ¬ HPassC (wcP w0 w1 w2 w3 w4) := by
  simp [HPassC, wcP, workerCallH, wkUnpark]

theorem kcW_notPass {w0 w1 w2 w3 w4 : Word} {n m : Nat} {σ : Spike.Lib.X64.AS} {c : Ctl}
    (h : KcW w0 w1 w2 w3 w4 n m σ c) : ¬ HPassC c :=
  h.1 ▸ wcP_notPass w0 w1 w2 w3 w4

theorem wcR_notPass (w0 w1 w2 w3 w4 : Word) : ¬ HPassC (wcR w0 w1 w2 w3 w4) := by
  simp [HPassC, wcR, workerRestH, wkUnpark]

theorem c1_pass {env : Env} : HPassC ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), env, none⟩ := .inl rfl

theorem c2_pass {env : Env} : HPassC ⟨.ret .unit, env, none⟩ := .inr rfl

/-- The source premises are inhabited: the worker's call control is before the store, the controls after the
store and the `unpark` past it. -/
example (w : Word) : ¬ HPassC (wcP w w w w w) ∧ HPassC ⟨.ret .unit, [], none⟩ :=
  ⟨wcP_notPass w w w w w, c2_pass⟩

end Spike.Lib.X64.Flow.Worker.Hello.Z

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Z.prW_notUnpk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Z.prW_notUnpk
