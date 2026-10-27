/-
**The setup frame placed** (AArch64): the start's call of the setup block
leaves the frame `fr` whose only live word, `me`'s, is at the immediate
`imms2Me_setupK`, placed at every state.

- `framesPlaced_setup`: `FramesPlacedInI` of `[fr]` at any state.
-/
import Spike.Lib.LowerA64.SetupHCall
import Spike.Lib.LowerA64.PinnedTcbA
import Spike.Lib.A64FramesPlacedI
import Spike.Lib.Src.ImmsMe
import Spike.Lib.Rt.A64LayoutOfPlaceOK

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64.Flow
open Spike.Lib.A64ConsumerS (FramesPlacedInI)
open Spike.Lib.LowerNode (imms2Me)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The program's start control (`S0A`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).env, none⟩ : Ctl)

/-- **The setup frame is placed** at any state: the start's call of the
setup block leaves the frame `fr` (`callTo_setupTerm`), whose only live
word, `me`'s, is at the immediate `imms2Me_setupK` (the first TCB, which
the start's `me` word is, `valRep_meW2_of_placeOKAtA`). -/
theorem framesPlaced_setup (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {cE : Ctl} {fr : TermRun.Frame} (hct : Spike.Lib.A64.Flow.CallTo p C0 cE fr) (s : State) :
    ∃ B, FramesPlacedInI (Ly).Λ (fun _ => none) s [fr] B := by
  obtain ⟨dr, hf, -⟩ := Spike.Lib.LowerNode.rodata_of_setupOf hp hty
  have hc0 : C0 = Spike.Lib.Ctl.mk Scc.Sem.SrcSem.setupTerm [("me", .ptr .pub .void,
      [meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))]), ("u", .unit, [])] none := by
    simp only [th02, hty]
  have hcall := callTo_setupTerm (p := p) (c0 := C0) (by rw [hc0]) (by rw [hc0]; rfl) hf
  obtain ⟨-, rfl⟩ := CallTo.unique hct hcall
  refine ⟨fun _ => False, fun d x k => if d = 0 ∧ x = "me" ∧ k = 0 then some (.imm ((lay2 Λ p).pinned.lo + 8))
    else none, ?_, ?_, ?_, ?_⟩
  · intro d f hfd y ty' ws hy k wd wp hwd hwp
    by_cases hc : d = 0 ∧ y = "me" ∧ k = 0
    · obtain ⟨rfl, rfl, rfl⟩ := hc
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hfd
      subst hfd
      simp only [and_self, ite_true, Option.some.injEq] at hwp
      subst hwp
      simp [th02, hty, TermRun.lookupE] at hy
      obtain ⟨-, rfl⟩ := hy
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hwd
      subst hwd
      exact valRep_meW2_of_placeOKAtA h (fun _ => none)
    · simp only [hc, ite_false] at hwp
      exact absurd hwp (by simp)
  · intro d f hfd y hy ty' ws hl k hk
    rcases d with _ | d
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hfd
      subst hfd
      have hme : y = "me" := by
        revert hy
        simp [Spike.Lib.LowerNode.setupRest, Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, Scc.Sem.atVars]
      subst hme
      simp [th02, hty, TermRun.lookupE] at hl
      obtain ⟨-, rfl⟩ := hl
      have hk0 : k = 0 := by simpa using hk
      subst hk0
      exact ⟨_, if_pos ⟨rfl, rfl, rfl⟩⟩
    · simp at hfd
  · intro d x k wp hwp
    by_cases hc : d = 0 ∧ x = "me" ∧ k = 0
    · simp only [hc, and_self, ite_true, Option.some.injEq] at hwp
      subst hwp
      intro pl hpl
      simp [Scc.Sem.WordPlace.places] at hpl
    · simp only [hc, ite_false] at hwp
      exact absurd hwp (by simp)
  · intro d f x k n hfd hwp
    by_cases hc : d = 0 ∧ x = "me" ∧ k = 0
    · obtain ⟨rfl, rfl, rfl⟩ := hc
      simp only [and_self, ite_true, Option.some.injEq, Scc.Sem.WordPlace.imm.injEq] at hwp
      subst hwp
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hfd
      subst hfd
      exact Spike.Lib.LowerNode.imms2Me_setupK hty
    · simp only [hc, ite_false] at hwp
      exact absurd hwp (by simp)

end Assembled

/-- info: 'Spike.Lib.LowerA64.framesPlaced_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms framesPlaced_setup

end Spike.Lib.LowerA64
