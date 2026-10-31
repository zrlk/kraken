/-
**Off the `writeErr` and `threads` abort sites, by label** (x86-64; twin of
`Spike/Lib/A64AbOffL.lean`): the abort sites are the `codeLabel` addresses
of the stubs' exit calls (`PlaceWX.abortAt_eq`), so a pc that is none of
those labels is off the sites, at the runtime's layout of a placed output.

- (`PcOff`, `AbOffL`, `RunsOff`, `abOffL_of_runs` are in
  `Spike/Lib/X64AbOffLDef.lean`, imported by the segment files.)
- `abOff_of_L_ofPlaceOK`: at `RuntimeLayout.ofPlaceWX`, `AbOffL` of its
  labels puts the pc off the `writeErr` and `threads` sites of its marks
  (`abortAt_eq`, `lab_toNat`).
- `off_of_A_ofPlaceOK`: there, `X64WakeOff.AbOffA` is off every abort site
  (`WakeM0.MSide.off`).
- `noSite_of_A_ofPlaceOK`: there, `AbOffA` is at no transfer site
  (`WCompat0.noSite0`).

**Unlike AArch64**: the layout is `RuntimeLayout.ofPlaceWX` at `PlaceWX`
(A64: `ofPlaceW` at `PlaceW`), labels resolve through `codeLabel` (A64:
`codeOf`).
-/
import Spike.Lib.X64AbOffLDef
import Spike.Lib.X64WakeOffDef
import Spike.Lib.X64PlaceWRt
import Spike.Lib.X64WakePostAb

namespace Spike.Lib.X64AbOffL

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (pcOf codeLabel)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.PhRec (μ)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : Spike.Lib.PlaceWX pcfg Λ o)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`AbOffL` is `AbOff`** at the runtime's layout of a placed output. -/
theorem abOff_of_L_ofPlaceOK {s : State} {c : Ctl} (hL : AbOffL (RuntimeLayout.ofPlaceWX h i).lab s c) :
    Spike.Lib.X64WakePostAb.AbOff (μ (RuntimeLayout.ofPlaceWX h i)) s := by
  intro k a ha hpc
  rw [Spike.Lib.PlaceWX.abortAt_eq h i] at ha
  have hpc' : s.st.2.toBitVec.toNat = a := hpc
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · subst hk
    apply hL.1
    have := Spike.Lib.PlaceWX.lab_toNat h i ha
    exact Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (hpc'.trans this.symm))
  · subst hk
    apply hL.2.1
    have := Spike.Lib.PlaceWX.lab_toNat h i ha
    exact Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (hpc'.trans this.symm))

/-- **`AbOffA` is off every abort site** at the runtime's layout of a
placed output (`WakeM0.MSide.off`'s form). -/
theorem off_of_A_ofPlaceOK {s : State} {c : Ctl}
    (hL : Spike.Lib.X64WakeOff.AbOffA (RuntimeLayout.ofPlaceWX h i).lab s c) :
    ∀ k a, (μ (RuntimeLayout.ofPlaceWX h i)).abortAt k = some a → pcOf s ≠ a := by
  intro k a ha hpc
  rw [Spike.Lib.PlaceWX.abortAt_eq h i] at ha
  have hpc' : s.st.2.toBitVec.toNat = a := hpc
  have heq : s.st.2 = (RuntimeLayout.ofPlaceWX h i).lab (Scc.Cert.Link.abortName k) :=
    Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (hpc'.trans (Spike.Lib.PlaceWX.lab_toNat h i ha).symm))
  have hL' : Spike.Lib.X64WakeOff.PcOffA (RuntimeLayout.ofPlaceWX h i).lab s.st.2 := hL
  cases k
  · exact hL'.1 heq
  · exact hL'.2.1 heq
  · exact hL'.2.2.1 heq
  · exact hL'.2.2.2.2.1 heq
  · exact hL'.2.2.2.1 heq

/-- **`AbOffA` is at no transfer site** at the runtime's layout of a placed
output (`WCompat0.noSite0`'s form): the take and release sites are the
`codeLabel` addresses of `scc_rt_take_site` and `scc_rt_release_site`. -/
theorem noSite_of_A_ofPlaceOK {s : State} {c : Ctl}
    (hL : Spike.Lib.X64WakeOff.AbOffA (RuntimeLayout.ofPlaceWX h i).lab s c) :
    Scc.Sem.Kernel.siteAt Scc.Sem.X64.abi (μ (RuntimeLayout.ofPlaceWX h i)) s = none := by
  have hL' : Spike.Lib.X64WakeOff.PcOffA (RuntimeLayout.ofPlaceWX h i).lab s.st.2 := hL
  refine Scc.Sem.Kernel.siteAt_eq_none_iff.mpr ⟨fun ht => ?_, fun hr => ?_⟩
  · change codeLabel Λ.code.lo o.prog "scc_rt_take_site" = some (pcOf s) at ht
    exact hL'.2.2.2.2.2.1 (Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq
      (Spike.Lib.PlaceWX.lab_toNat h i ht).symm))
  · change codeLabel Λ.code.lo o.prog "scc_rt_release_site" = some (pcOf s) at hr
    exact hL'.2.2.2.2.2.2 (Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq
      (Spike.Lib.PlaceWX.lab_toNat h i hr).symm))

end Place

end Spike.Lib.X64AbOffL

/-- info: 'Spike.Lib.X64AbOffL.abOff_of_L_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64AbOffL.abOff_of_L_ofPlaceOK

/-- info: 'Spike.Lib.X64AbOffL.off_of_A_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64AbOffL.off_of_A_ofPlaceOK

/-- info: 'Spike.Lib.X64AbOffL.noSite_of_A_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64AbOffL.noSite_of_A_ofPlaceOK
