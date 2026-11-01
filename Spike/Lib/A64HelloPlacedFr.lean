/-
**hello's worker frames placed through `print`'s call and return** (AArch64):
`A64PlacedFr`'s call and return transfers at the worker's `let u = call print
q sl in workerRestH` (`HelloSplit.workerCallH`), the caller's frame
`⟨"u", workerRestH, env, [], .unit⟩` pushed.

- `workerCallH_not_ext`, `workerRestH_not_ext`: neither the call nor its
  continuation is a model term of the output extern.
- `iH_workerCallH`: the root's immediate table (`ImmsH.iH`) has no entry at the
  call, so the transfers' immediate premise holds (`himm_workerCall`).
- `framesPlaced_uFrame`: the caller's frame placed at the call's `PlacedSE`
  (the frames inside `print` at the call's state).
- `placedSE_printCall`: `print`'s entry at `PlacedSE`.
- `placedSE_printRet`: `print`'s `ret ()` at `PlacedSE` from the
  continuation's.
-/
import Spike.Lib.A64PlacedFr
import Spike.Lib.HelloSplit
import Spike.Lib.HelloPrintSrcPub
import Spike.Lib.A64HelloImmsH
import Spike.Lib.LowerA64.PrintPlacedSE

namespace Spike.Lib.A64.HelloPh.PlacedFrH

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.A64PlacedFr
open Spike.Lib.HelloSplit (workerCallH workerRestH)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {fs : List TermRun.Frame}

/-- **The worker's call of `print` is no model term** of the output extern. -/
theorem workerCallH_not_ext : workerCallH ∉ externModelTerms := by
  simp [externModelTerms, modelTerms, Scc.Frontend.printBody, Scc.Frontend.printLBody, Scc.Frontend.printLPubBody,
    Scc.Frontend.printAdv, Scc.Frontend.printNext, workerCallH, workerRestH]

/-- **The call's continuation is no model term** of the output extern. -/
theorem workerRestH_not_ext : workerRestH ∉ externModelTerms := by
  simp [externModelTerms, modelTerms, Scc.Frontend.printBody, Scc.Frontend.printLBody, Scc.Frontend.printLPubBody,
    Scc.Frontend.printAdv, Scc.Frontend.printNext, workerRestH]

/-- **The root's immediate table has no entry at the call.** -/
theorem iH_workerCallH (Λ0 : Scc.Sem.Layout) (y : String) (k : Nat) :
    Spike.Lib.A64.HelloPh.ImmsH.iH Λ0 workerCallH y k = none := by
  simp [Spike.Lib.A64.HelloPh.ImmsH.iH, Spike.Lib.A64.HelloPh.C0S.immsH, SccCode.helloImms, workerCallH, workerRestH,
    Scc.Sem.SrcSem.setupTerm, SccCode.helloImm_t0, SccCode.helloImm_t1, SccCode.helloImm_t2]

/-- **The transfers' immediate premise at the call**, at a layout with no
immediate at the call (`iH_workerCallH` at the root's). -/
theorem himm_workerCall (hi : ∀ y k, Λ.imms workerCallH y k = none) :
    ∀ y k n, Λ.imms workerCallH y k = some n → Λ.imms workerRestH y k = some n := by
  intro y k n h
  rw [hi] at h
  cases h

/-- **The caller's frame placed at the call**: the call's control at
`PlacedSE` places the frames with `⟨"u", workerRestH, c.env, [], .unit⟩`
pushed, at the same state. -/
theorem framesPlaced_uFrame (h : PlacedSE Λ lbl s c fs) (ht : c.term = workerCallH)
    (hi : ∀ y k, Λ.imms workerCallH y k = none) :
    FramesPlaced Λ lbl s (⟨"u", workerRestH, c.env, [], .unit⟩ :: fs) :=
  framesPlaced_pushSE h (by rw [ht]; exact workerCallH_not_ext) ht rfl rfl rfl (by rw [ht]; exact himm_workerCall hi)

/-- **`print`'s entry at `PlacedSE`** (`FrameStep.call` at `printPD`'s
declaration): its body a model term (`printBody_ext`), the caller's frame
pushed. -/
theorem placedSE_printCall (h : PlacedSE Λ lbl s c fs) (ht : c.term = workerCallH)
    (hi : ∀ y k, Λ.imms workerCallH y k = none) {ws : List TermRun.Word} :
    PlacedSE Λ lbl s ⟨Spike.Lib.PrintSrc.printBody, [("a", Spike.Lib.HelloRodataSrc.sliceTyP, ws)], none⟩
      (⟨"u", workerRestH, c.env, [], .unit⟩ :: fs) :=
  PlacedSE.of_ext (.inl Spike.Lib.LowerA64.printBody_ext) (framesPlaced_uFrame h ht hi)

/-- **`print`'s `ret ()` at `PlacedSE`** from the continuation's `PlacedSE`
(the return's successor). -/
theorem placedSE_printRet {env : TermRun.Env} {t : Ty} {ws : List TermRun.Word} {hd : Option (Nat × TermRun.Word)}
    {c' : Ctl} (hr : c'.term = .ret .unit)
    (h : PlacedSE Λ lbl s ⟨workerRestH, ("u", t, ws) :: env, hd⟩ fs) :
    PlacedSE Λ lbl s c' (⟨"u", workerRestH, env, [], .unit⟩ :: fs) :=
  placedSE_ret (fr := ⟨"u", workerRestH, env, [], .unit⟩) hr rfl h workerRestH_not_ext

/-- The premises are met: a call control with no bound variable is placed
(`PlacedS` at the empty place map), and the root's table has no immediate at
the call. -/
example (Λ0 : Scc.Sem.Layout) (hi : Λ.imms = Spike.Lib.A64.HelloPh.ImmsH.iH Λ0) :
    FramesPlaced Λ lbl s [⟨"u", workerRestH, [], [], .unit⟩] := by
  have hpl : PlacedSE Λ lbl s ⟨workerCallH, [], none⟩ [] := by
    refine .inl ⟨fun _ _ _ => none, ?_, ?_, ?_⟩
    · intro _ _ _ _ _ _ _ _ _ _ _ h
      cases h
    · intro d env _ hd _ _ _ _ _ hl
      rcases d with _ | d
      · simp only [envsOf, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at hd
        subst hd
        simp [TermRun.lookupE] at hl
      · simp [envsOf] at hd
    · intro _ _ _ _ _ _ h
      cases h
  exact framesPlaced_uFrame hpl rfl fun y k => by rw [hi]; exact iH_workerCallH Λ0 y k

end Spike.Lib.A64.HelloPh.PlacedFrH

/-- info: 'Spike.Lib.A64.HelloPh.PlacedFrH.framesPlaced_uFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.PlacedFrH.framesPlaced_uFrame

/-- info: 'Spike.Lib.A64.HelloPh.PlacedFrH.placedSE_printCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.PlacedFrH.placedSE_printCall

/-- info: 'Spike.Lib.A64.HelloPh.PlacedFrH.placedSE_printRet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.PlacedFrH.placedSE_printRet
