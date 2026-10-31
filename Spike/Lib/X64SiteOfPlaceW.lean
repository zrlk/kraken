/-
**The take site at its label under `PlaceWX`** (wake.w, x86-64; the twin of
`Spike/Lib/A64SiteOfPlaceW.lean`): at the placed runtime layout
`L := RuntimeLayout.ofPlaceWX hp i` of any output passing wake's placement
facts (`PlaceWX`), the marks' take site (`PhRec.μ L`) is the take site
label's address (`StackTake.siteL`, `scc_rt_take_site`) in the loaded
thread: the premise `hsite` that the x86-64 wake files carry, in exactly
that form.

The proof is `PhRec.site_ofPlaceOK`'s (`Spike/Lib/X64PhRec.lean`), from
`PlaceWX`'s A6 instead of `placeOKAt`: A6's phase check resolves every site
label in the program (`sitesBy`'s `mapM codeLabel`), so `scc_rt_take_site`
has a `codeLabel` address `a`, and the loaded thread's label there is `a`
(`PlaceWX.lab_toNat`). No pc literal.

- `codeLabel_of_mapM`: a member of a resolved list resolves.
- `site_ofPlaceWX`: `(PhRec.μ L).site .take = some (L.lab siteL).toBitVec.toNat`.

Names: x86-64 uses `codeLabel` for A64's `codeOf`, and `PlaceWX` /
`ofPlaceWX` for `PlaceW` / `ofPlaceW` (the x86-64 names of
`Spike/Lib/X64PlaceW.lean`); the namespace is `Spike.Lib.PlaceWX`.
-/
import Spike.Lib.X64PlaceWRt

namespace Spike.Lib.PlaceWX

open Scc.Sem.X64 (codeLabel)
open Spike.Lib.X64.Rt (RuntimeLayout)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}

/-- **A label of a resolved list resolves**: every member of `l` has a
`codeLabel` address when `l.mapM (codeLabel base cells)` does. -/
theorem codeLabel_of_mapM {base : Nat} {cells : List (Directive × Nat)} :
    ∀ {l : List String} {ss : List Nat}, l.mapM (codeLabel base cells) = some ss →
      ∀ x ∈ l, ∃ a, codeLabel base cells x = some a := by
  intro l
  induction l with
  | nil => intro _ _ x hx; cases hx
  | cons y ys ih =>
    intro ss hm x hx
    rw [List.mapM_cons] at hm
    cases hy : codeLabel base cells y with
    | none => rw [hy] at hm; cases hm
    | some c =>
      cases hys : ys.mapM (codeLabel base cells) with
      | none => rw [hy, hys] at hm; cases hm
      | some cs =>
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨c, hy⟩
        · exact ih hys x hx

/-- **The take site at its label** in the loaded thread of `ofPlaceWX`
(`hsite`): A6 resolves `scc_rt_take_site`, and the loaded label there is
its `codeLabel` address (`lab_toNat`). -/
theorem site_ofPlaceWX (hp : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    (Spike.Lib.X64.PhRec.μ (RuntimeLayout.ofPlaceWX hp i)).site .take =
      some ((RuntimeLayout.ofPlaceWX hp i).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  have h6 := hp.a6
  simp only [Scc.Cert.PlaceOK.X64.a6, Bool.and_eq_true] at h6
  have h6 := h6.1
  unfold Scc.Cert.Rt.X64.phasesOk Scc.Cert.Rt.X64.phasesOkBy at h6
  rw [Scc.Cert.Rt.X64.codeT_eq] at h6
  split at h6
  · next T ss hT hs =>
    have hl : "scc_rt_take_site" ∈ Scc.Cert.Rt.X64.siteLabels Λ := by
      simp [Scc.Cert.Rt.X64.siteLabels]
    unfold Scc.Cert.Rt.X64.sitesBy at hs
    obtain ⟨a, ha⟩ := codeLabel_of_mapM hs _ hl
    show codeLabel Λ.code.lo o.prog "scc_rt_take_site" = _
    rw [ha, lab_toNat hp i ha]
  · cases h6

end Spike.Lib.PlaceWX

/-- info: 'Spike.Lib.PlaceWX.codeLabel_of_mapM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.PlaceWX.codeLabel_of_mapM

/-- info: 'Spike.Lib.PlaceWX.site_ofPlaceWX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.PlaceWX.site_ofPlaceWX
