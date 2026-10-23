/-
**The runtime rows' phase checks from the placement check**
(`rtNodesOk_of_placeOK`): `RtNodesOk` (`Spike/Lib/Rt/A64RtNodes.lean`) of
any groups of an output passing `Scc.Cert.PlaceOK.A64.placeOK`, at the
program's sites and phases (A6, `Rt.A64.okPcOf`, `Rt.A64.phOf`), its labels
in the canonical loader's thread, any return points, each row's dead
targets those off its entry's phase (`offPh`).

- A6 checks the rows' pcs, not their targets; `offPh` holds every row's
  crossings (`crossOf`, `Spike/Lib/A64PhasesOfPlaceOK.lean`) by its
  definition, so the premise is discharged with no further check.
- The node lemmas also need each dead target unreached (`hdead`), a run
  fact the node's proof supplies; a check at a smaller dead set holding
  the row's crossings gives the one at a larger set (`blkPh_mono`).
- **Oracle**: `ret0.w`'s runtime rows (`Spike/Test/A64RtPhOfPlaceOK.lean`).
-/
import Spike.Lib.Rt.A64RtNodes
import Spike.Lib.A64PhasesOfPlaceOK

namespace Spike.Lib.A64.Rt

open Kraken Kraken.Promising.AArch64
open Spike.Lib.A64Consumer (blkPh)
open Spike.Lib.A64.Phases (crossOf blkPh_of_placeOK)
open Scc.Cert.PlaceOK.A64 (placeOK placeOKAt tablesOf)
open Scc.Cert.Rt.A64 (OGrp OBlk)

/-- **A row's targets off its entry's phase**: at label `l`, offset `k`,
the pcs `t` in another phase than `lab l + 4 k`'s. -/
def offPh (ph : Nat → Nat) (lab : Label → Int64) (l : Label) (k : Nat) (t : Nat) : Bool :=
  ph t != ph (lab l + Int64.ofNat (4 * k)).toBitVec.toNat

/-- **A crossing is off the entry's phase.** -/
theorem ph_ne_of_mem_crossOf {lab : Label → Int64} {ph : Nat → Nat} {pc ra : Int64} {blk : List Directive}
    {t : Nat} (ht : t ∈ crossOf lab ph pc ra blk) : ph t ≠ ph pc.toBitVec.toNat := by
  simp only [crossOf, List.mem_flatMap] at ht
  obtain ⟨k, -, hk⟩ := ht
  split at hk
  · split at hk
    · have := (List.mem_filter.mp hk).2
      simpa using this
    · cases hk
  · cases hk

/-- **The phase check is monotone in the dead set.** -/
theorem blkPh_mono {okPc : Nat → Bool} {ph : Nat → Nat} {d d' : Nat → Bool} {lab : Label → Int64}
    {pc ra : Int64} {blk : List Directive} (hd : ∀ t, d t = true → d' t = true)
    (h : blkPh okPc ph d lab pc ra blk = true) : blkPh okPc ph d' lab pc ra blk = true := by
  unfold blkPh at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro k hk
  have h := h k hk
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  revert h
  rintro ⟨-, h⟩
  split at h
  · split at h
    · rw [List.all_eq_true] at h ⊢
      intro t ht
      have := h t ht
      simp only [Bool.or_eq_true] at this ⊢
      exact this.imp_right (hd _)
    · cases h
  · cases h

variable {cfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out}

/-- **`RtNodesOk` of an output passing `placeOK`**: any groups of its
table, at its sites and phases, its labels in the canonical loader's
thread (`hl`, any entry state and data symbols), any return points, the
dead targets those off each row's entry's phase. -/
theorem rtNodesOk_of_placeOK {Λ : Scc.Sem.Layout} (h : placeOKAt cfg Λ o = true) {E : Scc.Sem.Entry} {syms : List
    (String × Nat)}
    {lab : Label → Int64}
    (hl : (_root_.Executable.labels
      (Scc.Sem.A64.threadAt E Λ.code.lo o.prog syms).exe).label = lab)
    (hs : ∀ p ∈ syms, Λ.code.lo ≤ p.2) (ra : Label → Int64) {gs : List OGrp} (hgs : ∀ g ∈ gs, g ∈ o.place.blocks) :
    RtNodesOk (Scc.Cert.Rt.A64.okPcOf Λ.code.lo o.prog Λ)
      (Scc.Cert.Rt.A64.phOf Λ.code.lo o.prog)
      (offPh (Scc.Cert.Rt.A64.phOf Λ.code.lo o.prog) lab) lab ra gs := by
  intro g hg b hb
  refine blkPh_of_placeOK h (hgs g hg) hb hl hs fun t ht => ?_
  have := ph_ne_of_mem_crossOf ht
  simpa [offPh] using this

end Spike.Lib.A64.Rt
