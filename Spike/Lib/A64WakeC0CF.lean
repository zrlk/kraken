/-
**`CFacts` of main's box control `c0W`** (AArch64): at any layout with
`WakeImmsC0.immsW2 Λ0 i0` as its immediates (`i0` keeping `z` at `0` at the
box's term) and `Λ0`'s pinned region, `c0W` has `CFacts` at `L0T`: no `ret`,
no load or store and no buffer allocation (its term is `let o = new z in …`),
and placed at every state (`WakeImmsC0.placedSE_c0W`, `z` at `.imm 0`, `me`
at `.imm tcb0`).

- `PlacedS.head`: a placed frame stack's current frame is `Placed`.
- `cfacts_c0W`: `CFacts` at `immsW2`; `cfacts_c0WW` at `ofPlaceW` with
  `i := immsW2 Λ0 wakeImms` (`WakeFinalCAW.iW`).
-/
import Spike.Lib.WakeImmsC0

namespace Spike.Lib.A64.WakeC0CF

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64Consumer (Lbl Placed CFacts)
open Spike.Lib.A64ConsumerS (PlacedS envsOf fvOf termsOf)
open Spike.Lib.WakeLoadT (L0T)
open Spike.Lib.WakeC0 (c0W c0W_term)

/-- **The current frame of a placed frame stack is placed** (`envm 0`). -/
theorem PlacedS.head {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : PlacedS Λ lbl s c fs) : Placed Λ lbl s c := by
  obtain ⟨envm, hrep, htot, himm⟩ := h
  exact ⟨envm 0, fun x ty ws hl k wd wp hwd hwp => hrep 0 c.env (by simp [envsOf]) x ty ws hl k wd wp hwd hwp,
    fun x hx ty ws hl k hk => htot 0 c.env _ (by simp [envsOf]) (by simp [fvOf]) x hx ty ws hl k hk,
    fun x k n h => himm 0 c.term x k n (by simp [termsOf]) h⟩

/-- **`c0W`'s source facts** at `immsW2` (`hi`), `Λ0`'s pinned region
(`hpin`), `z` at `0` at the box (`hz`). -/
theorem cfacts_c0W {Λ Λ0 : Scc.Sem.Layout} {i0 : Expr → String → Nat → Option Nat}
    (hi : Λ.imms = WakeImmsC0.immsW2 Λ0 i0) (hpin : Λ.pinned = Λ0.pinned)
    (hz : i0 SccCode.wakeImm_t1 "z" 0 = some 0) : CFacts Λ (L0T Λ) c0W := by
  refine ⟨fun a h => ?_, fun x a e ty w h => ?_, fun x a τ e h => ?_, fun s => ?_⟩
  · rw [c0W_term] at h; cases h
  · rcases h with h | ⟨b, h⟩ <;> rw [c0W_term] at h <;> cases h
  · rw [c0W_term] at h; cases h
  · rcases WakeImmsC0.placedSE_c0W hi hpin hz s with h | ⟨h, -⟩
    · exact PlacedS.head h
    · exfalso
      rcases h with h | h <;> rw [c0W_term] at h
      · simp [Scc.Sem.externModelTerms, Scc.Sem.modelTerms, Scc.Frontend.printBody, Scc.Frontend.printLBody,
          Scc.Frontend.printLPubBody, Scc.Frontend.printAdv, Scc.Frontend.printNext] at h
      · simp [Scc.Sem.exprFv] at h
        have h1 := h.1
        simp only [Scc.Sem.opVars, Scc.Sem.opAts] at h1
        simp [Scc.Sem.atVars] at h1

/-- **`c0W`'s source facts at the runtime's layout** with
`i := immsW2 Λ0 wakeImms`. -/
theorem cfacts_c0WW {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : Spike.Lib.PlaceW pcfg Λ0 o) :
    let Λ := (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp (WakeImmsC0.immsW2 Λ0 SccCode.wakeImms)).Λ
    CFacts Λ (L0T Λ) c0W :=
  cfacts_c0W rfl rfl (by simp [SccCode.wakeImms])

end Spike.Lib.A64.WakeC0CF

/-- info: 'Spike.Lib.A64.WakeC0CF.PlacedS.head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeC0CF.PlacedS.head

/-- info: 'Spike.Lib.A64.WakeC0CF.cfacts_c0W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeC0CF.cfacts_c0W

/-- info: 'Spike.Lib.A64.WakeC0CF.cfacts_c0WW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeC0CF.cfacts_c0WW
