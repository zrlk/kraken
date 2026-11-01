/-
**hello's worker landing fact** (AArch64; rows 5j-wit-W and 5j-wit-E-call): the fragment `XH` the worker's
segment invariant lies in (`HelloSegTCSX.SegTCSX`'s `X`, `HelloWorkerSideX.wi_existsHX`): every frame placed
(`PlacedSE`); and on an empty stack, the caller frame of the call the control runs to placed (`hcall`).
`print`'s caller frame in `wc_worker`'s slots is not part of it: at the call node it comes from the node's own
slots (`XHLand.uPl_call`), and it does not hold at `wc_worker`'s prologue, whose control is already `wcP`.

- `XH`: the fragment; `hplW_of`, `hcall_of`: the rows `hplW` and `hcall` by projection.
- `localRunS_cmp`: two local runs from one control are comparable (local steps are deterministic).
- `localRunS_call`: a control at a call runs locally only to itself.
- `kidC`, `kid_run_wcP`: the child's control at `tail worker` runs locally to a call of `print` only at `wcP`.
- `iH_kid`: the root's table has no immediate at `kidC`.
- `xh3_wcP`, `xh3_kid`: `XH`'s third conjunct at `wcP` and at `kidC` from their `PlacedSE` (the root's table has
  no immediate at either).
-/
import Spike.Lib.A64HelloUFramePl
import Spike.Lib.A64HelloPlacedFr
import Spike.Lib.A64WakeStartH0B
import Spike.Lib.Frames1

namespace Spike.Lib.A64.HelloPh.XH

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib (Ctl LocalStepS LocalRunS FragS)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.A64PlacedFr
open Spike.Lib.A64.HelloPh.PlacedFrH
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSplit (workerCallH workerRestH envP wcP)

/-- **The worker's landing fact**: every frame placed; on an empty stack, the caller frame of a call of `print`
the control runs to placed. -/
def XH (Λ : Scc.Sem.Layout) (lbl : Lbl) : FragS isaLSE2 := fun s c fs =>
  PlacedSE Λ lbl s c fs ∧
    (fs = [] → ∀ c', LocalRunS helloSrc c c' → c'.term = workerCallH →
      FramesPlaced Λ lbl s [⟨"u", workerRestH, c'.env, [], .unit⟩])

variable {ι : Type} {Λ : Scc.Sem.Layout} {L : ι → Lbl}

/-- **`hplW` by projection.** -/
theorem hplW_of {Wi : ι → FragS isaLSE2} (h : ∀ w s c fs, Wi w s c fs → XH Λ (L w) s c fs) :
    ∀ w st c fs, Wi w st c fs → PlacedSE Λ (L w) st c fs :=
  fun w st c fs hw => (h w st c fs hw).1

/-- **`hcall` by projection.** -/
theorem hcall_of {Wi : ι → FragS isaLSE2} (h : ∀ w s c fs, Wi w s c fs → XH Λ (L w) s c fs) :
    ∀ w st c, Wi w st c [] → ∀ c', LocalRunS helloSrc c c' → c'.term = workerCallH →
      FramesPlaced Λ (L w) st [⟨"u", workerRestH, c'.env, [], .unit⟩] :=
  fun w st c hw c' hr ht => (h w st c [] hw).2 rfl c' hr ht

/-! ## Local runs to the call -/

/-- **Two local runs from one control are comparable.** -/
theorem localRunS_cmp {p : Prog} {c c1 c2 : Ctl} (h1 : LocalRunS p c c1) (h2 : LocalRunS p c c2) :
    LocalRunS p c1 c2 ∨ LocalRunS p c2 c1 := by
  induction h1 generalizing c2 with
  | refl => exact .inl h2
  | step hs _ ih =>
    cases h2 with
    | refl => exact .inr (.step hs ‹_›)
    | step hs' hr' =>
      rw [LocalStepS.det hs hs'] at *
      exact ih hr'

/-- **A control at a call runs locally only to itself.** -/
theorem localRunS_call {p : Prog} {c c' : Ctl} {x f : String} {is : List String} {a : At} {ts : List Ty}
    {e : Expr} (ht : c.term = .let_ x (.call f is a ts) e) (h : LocalRunS p c c') : c' = c := by
  cases h with
  | refl => rfl
  | step hs _ => exact (hs.not_call ht).elim

/-- The child's control at `tail worker` on the packet's five words. -/
def kidC (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) : Ctl :=
  ⟨.tail "worker" [] (.var "a") [], [("a", T, [w0, w1, w2, w3, w4])], none⟩

/-- **The child's control runs locally to a call of `print` only at `wcP`.** -/
theorem kid_run_wcP {T : Ty} {w0 w1 w2 w3 w4 : TermRun.Word} {c' : Ctl}
    (h : LocalRunS helloSrc (kidC T w0 w1 w2 w3 w4) c') (ht : c'.term = workerCallH) : c' = wcP w0 w1 w2 w3 w4 := by
  have hk := Spike.Lib.HelloSplit.kid_splitH (T := T) Spike.Lib.HelloSplit.worker_find w0 w1 w2 w3 w4
  rcases localRunS_cmp h hk with h' | h'
  · exact (localRunS_call ht h').symm
  · exact localRunS_call rfl h'

/-! ## The third conjunct -/

/-- **`XH`'s third conjunct at `wcP`** from its `PlacedSE`. -/
theorem xh3_wcP {lbl : Lbl} {s : State} {w0 w1 w2 w3 w4 : TermRun.Word}
    (h : PlacedSE Λ lbl s (wcP w0 w1 w2 w3 w4) []) (hi : ∀ y k, Λ.imms workerCallH y k = none) :
    ∀ c', LocalRunS helloSrc (wcP w0 w1 w2 w3 w4) c' → c'.term = workerCallH →
      FramesPlaced Λ lbl s [⟨"u", workerRestH, c'.env, [], .unit⟩] := by
  intro c' hr _
  rw [localRunS_call rfl hr]
  exact framesPlaced_uFrame h rfl hi

theorem kid_not_ext {T : Ty} {w0 w1 w2 w3 w4 : TermRun.Word} : (kidC T w0 w1 w2 w3 w4).term ∉ externModelTerms := by
  simp [kidC, externModelTerms, modelTerms, Scc.Frontend.printBody, Scc.Frontend.printLBody,
    Scc.Frontend.printLPubBody, Scc.Frontend.printAdv, Scc.Frontend.printNext]

/-- **The caller frame at `wcP` placed from the child's control's `PlacedSE`**: `c` and `j` at the places of the
packet's words 3 and 4, the layout with no immediate at the child's term. -/
theorem framesPlaced_kid {lbl : Lbl} {s : State} {T : Ty} {w0 w1 w2 w3 w4 : TermRun.Word}
    (h : PlacedSE Λ lbl s (kidC T w0 w1 w2 w3 w4) [])
    (hi : ∀ y k, Λ.imms (kidC T w0 w1 w2 w3 w4).term y k = none) :
    FramesPlaced Λ lbl s [⟨"u", workerRestH, envP w0 w1 w2 w3 w4, [], .unit⟩] := by
  rcases h with h | ⟨hm | hfv, -⟩
  · obtain ⟨envm, hrep, htot, himm⟩ := h
    have hl : TermRun.lookupE (kidC T w0 w1 w2 w3 w4).env "a" = some (T, [w0, w1, w2, w3, w4]) := by
      simp [kidC, TermRun.lookupE]
    obtain ⟨p3, hp3⟩ := htot 0 _ ["a"] (by simp [envsOf]) (by simp [fvOf, kidC, exprFv, atVars]) "a" (by simp)
      T _ hl 3 (by simp)
    obtain ⟨p4, hp4⟩ := htot 0 _ ["a"] (by simp [envsOf]) (by simp [fvOf, kidC, exprFv, atVars]) "a" (by simp)
      T _ hl 4 (by simp)
    let em : Nat → String → Nat → Option (WordPlace (machine (kernel 1)).I.RegId) := fun d y k =>
      if d = 0 ∧ k = 0 then (if y = "c" then some p3 else if y = "j" then some p4 else none) else none
    refine ⟨em, ?_, ?_, ?_⟩
    · intro d f hf y ty ws hy k wd wp hwd hwp
      rcases d with _ | d
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
        subst hf
        by_cases hk : k = 0
        · subst hk
          by_cases hc : y = "c"
          · subst hc
            simp only [em, and_self, ite_true, Option.some.injEq] at hwp
            subst hwp
            simp [envP, TermRun.lookupE] at hy
            obtain ⟨-, rfl⟩ := hy
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hwd
            subst hwd
            exact hrep 0 _ (by simp [envsOf]) "a" T _ hl 3 w3 p3 (by simp) hp3
          · by_cases hj : y = "j"
            · subst hj
              simp only [em, and_self, ite_true, Option.some.injEq, show ("j" : String) ≠ "c" by decide,
                ite_false] at hwp
              subst hwp
              simp [envP, TermRun.lookupE] at hy
              obtain ⟨-, rfl⟩ := hy
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hwd
              subst hwd
              exact hrep 0 _ (by simp [envsOf]) "a" T _ hl 4 w4 p4 (by simp) hp4
            · simp [em, hc, hj] at hwp
        · simp [em, hk] at hwp
      · simp at hf
    · intro d f hf y hy ty ws hl' k hk
      rcases d with _ | d
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
        subst hf
        have e : (exprFv workerRestH).filter (· != "u") = ["c", "j"] := rfl
        rw [e] at hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · simp [envP, TermRun.lookupE] at hl'
          obtain ⟨-, rfl⟩ := hl'
          obtain rfl : k = 0 := by simpa using hk
          exact ⟨p3, by simp [em]⟩
        · simp [envP, TermRun.lookupE] at hl'
          obtain ⟨-, rfl⟩ := hl'
          obtain rfl : k = 0 := by simpa using hk
          exact ⟨p4, by simp [em]⟩
      · simp at hf
    · intro d f y k n _ hwp
      by_cases h1 : d = 0 ∧ k = 0
      · by_cases hc : y = "c"
        · simp only [em, h1, hc, and_self, ite_true, Option.some.injEq] at hwp
          subst hwp
          have := himm 0 (kidC T w0 w1 w2 w3 w4).term "a" 3 n (by simp [termsOf]) hp3
          rw [hi] at this
          cases this
        · by_cases hj : y = "j"
          · simp only [em, h1, hj, and_self, ite_true, Option.some.injEq, show ("j" : String) ≠ "c" by decide,
              ite_false] at hwp
            subst hwp
            have := himm 0 (kidC T w0 w1 w2 w3 w4).term "a" 4 n (by simp [termsOf]) hp4
            rw [hi] at this
            cases this
          · simp [em, h1, hc, hj] at hwp
      · simp [em, h1] at hwp
  · exact absurd hm kid_not_ext
  · simp [kidC, exprFv, atVars] at hfv

/-- **`XH`'s third conjunct at the child's control** from its `PlacedSE`. -/
theorem xh3_kid {lbl : Lbl} {s : State} {T : Ty} {w0 w1 w2 w3 w4 : TermRun.Word}
    (h : PlacedSE Λ lbl s (kidC T w0 w1 w2 w3 w4) [])
    (hi : ∀ y k, Λ.imms (kidC T w0 w1 w2 w3 w4).term y k = none) :
    ∀ c', LocalRunS helloSrc (kidC T w0 w1 w2 w3 w4) c' → c'.term = workerCallH →
      FramesPlaced Λ lbl s [⟨"u", workerRestH, c'.env, [], .unit⟩] := by
  intro c' hr ht
  rw [kid_run_wcP hr ht]
  exact framesPlaced_kid h hi

/-- **The root's immediate table has no entry at the child's control.** -/
theorem iH_kid (Λ0 : Scc.Sem.Layout) {T : Ty} {w0 w1 w2 w3 w4 : TermRun.Word} (y : String) (k : Nat) :
    Spike.Lib.A64.HelloPh.ImmsH.iH Λ0 (kidC T w0 w1 w2 w3 w4).term y k = none := by
  simp [Spike.Lib.A64.HelloPh.ImmsH.iH, Spike.Lib.A64.HelloPh.C0S.immsH, SccCode.helloImms, kidC,
    Scc.Sem.SrcSem.setupTerm, SccCode.helloImm_t0, SccCode.helloImm_t1, SccCode.helloImm_t2]

/-- At the root's table the immediate premise is met: the child's placed control gives the caller frame at
`wcP` (through `kid_splitH`'s run). -/
example (Λ0 : Scc.Sem.Layout) (hi : Λ.imms = Spike.Lib.A64.HelloPh.ImmsH.iH Λ0) {lbl : Lbl} {s : State} {T : Ty}
    {w0 w1 w2 w3 w4 : TermRun.Word} (hpl : PlacedSE Λ lbl s (kidC T w0 w1 w2 w3 w4) []) :
    FramesPlaced Λ lbl s [⟨"u", workerRestH, (wcP w0 w1 w2 w3 w4).env, [], .unit⟩] :=
  xh3_kid hpl (fun y k => by rw [hi]; exact iH_kid Λ0 y k) _
    (Spike.Lib.HelloSplit.kid_splitH Spike.Lib.HelloSplit.worker_find w0 w1 w2 w3 w4) rfl

end Spike.Lib.A64.HelloPh.XH

/-- info: 'Spike.Lib.A64.HelloPh.XH.hcall_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XH.hcall_of

/-- info: 'Spike.Lib.A64.HelloPh.XH.xh3_kid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XH.xh3_kid

/-- info: 'Spike.Lib.A64.HelloPh.XH.xh3_wcP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.XH.xh3_wcP
