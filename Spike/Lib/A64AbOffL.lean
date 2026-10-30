/-
**Off the `writeErr` and `threads` abort sites, by label** (AArch64): the state predicate `W` of wake's main after the spawn
(`SegLW`, `Spike/Lib/SegLW.lean`), a pc test against the two exit calls'
labels, so each block's check is decided on the concrete listing.

- `AbOffL lab`: the pc is neither `scc_rt_abort_write_exit` nor
  `scc_rt_abort_threads_exit` (`PcOff lab` of the pc).
- `RunsOff lab runs`: every pc `label l + 4j` of the runs is off them
  (`abOffL_of_runs`); a segment's `W` checks are this hypothesis, decided
  on the listing.
- (`PcOff`, `AbOffL`, `RunsOff`, `abOffL_of_runs` are in
  `Spike/Lib/A64AbOffLDef.lean`, imported by the segment files.)
- `abOff_of_L_ofPlaceOK`: at `RuntimeLayout.ofPlaceW`, `AbOffL` of its
  labels is `WakePostAb.AbOff` of its marks (`abortAt_eq`, `lab_toNat`).
- `off_of_A_ofPlaceOK`: there, `A64WakeOff.AbOffA` is off every abort site
  (`WakeM0.MSide.off`).
-/
import Spike.Lib.A64AbOffLDef
import Spike.Lib.A64WakeOffDef
import Spike.Lib.LowerA64.AbortOfPlaceOK
import Spike.Lib.WakePostAb
import Spike.Lib.PlaceWRt

namespace Spike.Lib.A64AbOffL

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf)
open Scc.Cert.PlaceOK.A64
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.PhRec (μ)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : PlaceW pcfg Λ o)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`AbOffL` is `AbOff`** at the runtime's layout of a placed output. -/
theorem abOff_of_L_ofPlaceOK {s : State} {c : Ctl} (hL : AbOffL (RuntimeLayout.ofPlaceW h i).lab s c) :
    Spike.Lib.WakePostAb.AbOff (μ (RuntimeLayout.ofPlaceW h i)) s := by
  intro k a ha hpc
  rw [PlaceW.abortAt_eq h i] at ha
  have hpc' : s.st.2.toBitVec.toNat = a := hpc
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · subst hk
    apply hL.1
    have := PlaceW.lab_toNat h i ha
    exact Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (hpc'.trans this.symm))
  · subst hk
    apply hL.2.1
    have := PlaceW.lab_toNat h i ha
    exact Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (hpc'.trans this.symm))

/-- **`AbOffA` is off every abort site** at the runtime's layout of a
placed output (`WakeM0.MSide.off`'s form). -/
theorem off_of_A_ofPlaceOK {s : State} {c : Ctl}
    (hL : Spike.Lib.A64WakeOff.AbOffA (RuntimeLayout.ofPlaceW h i).lab s c) :
    ∀ k a, (μ (RuntimeLayout.ofPlaceW h i)).abortAt k = some a → pcOf s ≠ a := by
  intro k a ha hpc
  rw [PlaceW.abortAt_eq h i] at ha
  have hpc' : s.st.2.toBitVec.toNat = a := hpc
  have heq : s.st.2 = (RuntimeLayout.ofPlaceW h i).lab (Scc.Cert.Link.abortName k) :=
    Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (hpc'.trans (PlaceW.lab_toNat h i ha).symm))
  have hL' : Spike.Lib.A64WakeOff.PcOffA (RuntimeLayout.ofPlaceW h i).lab s.st.2 := hL
  cases k
  · exact hL'.1 heq
  · exact hL'.2.1 heq
  · exact hL'.2.2.1 heq
  · exact hL'.2.2.2.2.1 heq
  · exact hL'.2.2.2.1 heq

/-- **`AbOffA` is at no transfer site** at the runtime's layout of a placed
output (`WCompat0.noSite0`'s form): the take and release sites are the
`codeOf` addresses of `scc_rt_take_site` and `scc_rt_release_site`. -/
theorem noSite_of_A_ofPlaceOK {s : State} {c : Ctl}
    (hL : Spike.Lib.A64WakeOff.AbOffA (RuntimeLayout.ofPlaceW h i).lab s c) :
    Scc.Sem.Kernel.siteAt Scc.Sem.A64.abi (μ (RuntimeLayout.ofPlaceW h i)) s = none := by
  have hL' : Spike.Lib.A64WakeOff.PcOffA (RuntimeLayout.ofPlaceW h i).lab s.st.2 := hL
  refine Scc.Sem.Kernel.siteAt_eq_none_iff.mpr ⟨fun ht => ?_, fun hr => ?_⟩
  · change codeOf Λ.code.lo o.prog "scc_rt_take_site" = some (pcOf s) at ht
    exact hL'.2.2.2.2.2.1 (Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq
      (PlaceW.lab_toNat h i ht).symm))
  · change codeOf Λ.code.lo o.prog "scc_rt_release_site" = some (pcOf s) at hr
    exact hL'.2.2.2.2.2.2 (Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq
      (PlaceW.lab_toNat h i hr).symm))

end Place

end Spike.Lib.A64AbOffL
