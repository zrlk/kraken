/-
**The take site at its label under `PlaceW`** (wake.w, AArch64): at the
placed runtime layout `L := RuntimeLayout.ofPlaceW hp i` of any output
passing wake's placement facts (`PlaceW`, so wakeProg's), the marks' take
site (`PhRec.μ L`) is the take site label's address
(`StackTake.siteL`, `scc_rt_take_site`) in the loaded thread: the premise
`hsite` that `A64WakeMainWf`, `A64WakeMainGlue`, `A64PhRec.off` and their
users carry, in exactly that form.

The proof is `PhRec.site_ofPlaceOK`'s, from `PlaceW`'s A6 instead of
`placeOKAt`: A6's phase check resolves every site label in the program
(`sitesBy`'s `mapM codeOf`), so `scc_rt_take_site` has a `codeOf` address
`a`, and the loaded thread's label there is `a` (`PlaceW.lab_toNat`: the
label below the data symbols, the code's end below `2 ^ 64`). No pc
literal: the address is the label's, whatever the layout.

- `site_ofPlaceW`: `(PhRec.μ L).site .take = some (L.lab siteL).toBitVec.toNat`.
-/
import Spike.Lib.PlaceWRt

namespace Spike.Lib.PlaceW

open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}

/-- **A label of a resolved list resolves**: every member of `l` has a
`codeOf` address when `l.mapM (codeOf base prog)` does. -/
theorem codeOf_of_mapM {base : Nat} {prog : _root_.Program} :
    ∀ {l : List String} {ss : List Nat}, l.mapM (codeOf base prog) = some ss →
      ∀ x ∈ l, ∃ a, codeOf base prog x = some a := by
  intro l
  induction l with
  | nil => intro _ _ x hx; cases hx
  | cons y ys ih =>
    intro ss hm x hx
    rw [List.mapM_cons] at hm
    cases hy : codeOf base prog y with
    | none => rw [hy] at hm; cases hm
    | some c =>
      cases hys : ys.mapM (codeOf base prog) with
      | none => rw [hy, hys] at hm; cases hm
      | some cs =>
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨c, hy⟩
        · exact ih hys x hx

/-- **The take site at its label** in the loaded thread of `ofPlaceW`
(`hsite`): A6 resolves `scc_rt_take_site`, and the loaded label there is
its `codeOf` address (`lab_toNat`). -/
theorem site_ofPlaceW (hp : PlaceW pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    (Spike.Lib.A64.PhRec.μ (RuntimeLayout.ofPlaceW hp i)).site .take =
      some ((RuntimeLayout.ofPlaceW hp i).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  have h6 := hp.a6
  simp only [Scc.Cert.PlaceOK.A64.a6, Bool.and_eq_true] at h6
  have h6 := h6.1
  unfold Scc.Cert.Rt.A64.phasesOk Scc.Cert.Rt.A64.phasesOkBy at h6
  rw [Scc.Cert.Rt.A64.codeT_eq] at h6
  split at h6
  · next T ss hT hs =>
    have hl : "scc_rt_take_site" ∈ Scc.Cert.Rt.A64.siteLabels Λ := by
      simp [Scc.Cert.Rt.A64.siteLabels]
    unfold Scc.Cert.Rt.A64.sitesBy at hs
    obtain ⟨a, ha⟩ := codeOf_of_mapM hs _ hl
    show codeOf Λ.code.lo o.prog "scc_rt_take_site" = _
    rw [ha, lab_toNat hp i ha]
  · cases h6

-- `hsite` in the form its users carry (`PhRec.off`'s premise, at `ofPlaceW`).
example (hp : PlaceW pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat) (rS : Scc.Sem.Range) :=
  Spike.Lib.A64.PhRec.off (RuntimeLayout.ofPlaceW hp i) (rS := rS) (site_ofPlaceW hp i)

end Spike.Lib.PlaceW

/-- info: 'Spike.Lib.PlaceW.site_ofPlaceW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.PlaceW.site_ofPlaceW
