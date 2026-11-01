/-
**The concrete control fact's source premises** (rows 5j-k
and C4, AArch64): the control facts `A64HelloZ`'s node lemmas ask, at
hello's worker controls (`HelloSplit.wcP`, `wcR`, the controls past the
store, `print`'s predicate `HelloWorkerCallSrc.PrW`).

- `unpk_noStep`: no local step at an `unpark` binding (an extern).
- `prW_notUnpk`: `print`'s predicate's controls are at no `unpark` binding
  (`wc_hZP`'s, `wc_hZA`'s premises at `Pr := Qa := PrW`).
- `kcW_notPass`, `wcP_notPass`, `wcR_notPass`: the call's and the store's
  controls are before the store (`wc_hZC`, `wc_hz`, `wc_hZE`, `wc_hZW`).
- `c1_pass`, `c2_pass`: the controls after the store and the `unpark`, past
  it (`wc_hZW`, `wc_hZU`).
-/
import Spike.Lib.A64HelloZ
import Spike.Lib.HelloWorkerCallSrc

namespace Spike.Lib.A64.Flow.Worker.Hello.Z

open CoreLang CoreTerm TermRun
open Spike.Lib
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSplit (envP wcP wcR workerRestH workerCallH)
open Spike.Lib.HelloWorkerCallSrc (PrW KcW)
open Spike.Lib.HelloPrintSrcPub (PrintCP printLBodyP)
open Spike.Lib.A64.Flow.Worker.Hello.Pass (HPassC)
open Spike.Lib.WorkerSrc (wkUnpark)

/-- **No local step at an `unpark` binding** (an extern). -/
theorem unpk_noStep {c c₁ : Ctl} (h : LocalStepS helloSrc c c₁) {x : String} {a : CoreTerm.At} {e : Expr}
    (ht : c.term = .let_ x (.ext .unpark a) e) : False := by
  have := h.2 { p := helloSrc, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 } #[] []
    { term := c.term, env := c.env } rfl rfl rfl rfl
  simp [TermRun.tstep, ht, TermRun.evalOp] at this

/-- **`print`'s predicate's controls are at no `unpark` binding**: one has no
local step, and `printL`'s top is no binding of an extern. -/
theorem prW_notUnpk {pw wn : Word} {n m k : Nat} {c : Ctl} (h : PrW pw wn n m k c) : NotUnpk c := by
  intro x a e ht
  obtain ⟨⟨c1, hr, i, j, hc1, -⟩, -⟩ := h
  rcases HelloW1.localRunS_cases hr with rfl | ⟨c₂, hs⟩
  · rw [hc1] at ht; simp [printLBodyP] at ht
  · exact unpk_noStep hs ht

theorem wcP_notPass (w0 w1 w2 w3 w4 : Word) : ¬ HPassC (wcP w0 w1 w2 w3 w4) := by
  simp [HPassC, wcP, workerCallH, wkUnpark]

theorem kcW_notPass {w0 w1 w2 w3 w4 : Word} {n m : Nat} {σ : AS} {c : Ctl} (h : KcW w0 w1 w2 w3 w4 n m σ c) :
    ¬ HPassC c :=
  h.1 ▸ wcP_notPass w0 w1 w2 w3 w4

theorem wcR_notPass (w0 w1 w2 w3 w4 : Word) : ¬ HPassC (wcR w0 w1 w2 w3 w4) := by
  simp [HPassC, wcR, workerRestH, wkUnpark]

theorem c1_pass {env : Env} : HPassC ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), env, none⟩ := .inl rfl

theorem c2_pass {env : Env} : HPassC ⟨.ret .unit, env, none⟩ := .inr rfl

end Spike.Lib.A64.Flow.Worker.Hello.Z
