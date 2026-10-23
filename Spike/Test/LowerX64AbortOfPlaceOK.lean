/-
**The overflow abort path's premises at `ret0`'s placement check**
(`Spike/Lib/LowerX64/AbortOfPlaceOK.lean`): the generic discharges hold at
`ret0_placeOK`; the overflow exit call resolves at the hand site; `ret0`'s
seven sites resolve and are distinct (A6's check, satisfiable), and the
exit call's site premises (`hrel`, `htk`, `hk`, `hKex`) follow; they also
hold by hand at `ret0`'s record, and fail for the heap exit call's address
(so they carry content); a layout naming the heap kind's exit call at the
overflow one's label has duplicate sites.
-/
import Spike.Lib.LowerX64.AbortOfPlaceOK
import Spike.Test.X64PhRec

namespace Spike.Test.LowerX64AbortOfPlaceOK

open Scc.Cert.PlaceOK.X64 (atTables)

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.LowerX64
open Spike.Lib.X64.Rt (ret0P)
open Spike.Lib.X64.PhRec (μ)
open Scc.Cert.PlaceOK.X64.Test (ret0_placeOK)
open SccCode (ret0Λ ret0Cells ret0Secs ret0Imms)

/-- **Oracle**: the overflow exit call resolves at the hand site. -/
theorem ret0_ovf : Scc.Sem.X64.codeLabel ret0Λ.code.lo ret0Cells "scc_rt_abort_overflow_exit" = some 4198555 := by
  decide +kernel

/-- The generic discharges at `ret0`'s placement check. -/
example := ovf_codeLabel (atTables ret0_placeOK)
example := hprog_ofPlaceOK (atTables ret0_placeOK) ret0Imms
example := hsysIn_ofPlaceOK (atTables ret0_placeOK) ret0Imms
example := hms_ofPlaceOK (atTables ret0_placeOK) ret0Imms (rd := fun _ => True) (G := fun _ _ => True)
  (own := fun _ => []) (lbl := fun _ => none) (lsize := fun _ => 0)

/-- **Oracle**: `ret0`'s sites, in `siteLabels`' order. -/
theorem ret0_sitesOf :
    Scc.Cert.Rt.X64.sitesOf (Scc.Cert.Link.X64.linkOf ret0Cells ret0Secs).code.lo ret0Cells
      (Scc.Cert.Link.X64.linkOf ret0Cells ret0Secs) =
      some [4196177, 4196217, 4198555, 4198623, 4198691, 4198759, 4198827] := by
  decide +kernel

/-- **Satisfiable**: `ret0`'s sites are distinct. -/
example : [4196177, 4196217, 4198555, 4198623, 4198691, 4198759, 4198827].Nodup := by decide

/-- The site discharges at `ret0`'s placement check. -/
example := sites7 (atTables ret0_placeOK)
example := hrel_ofPlaceOK (atTables ret0_placeOK) ret0Imms
example := htk_ofPlaceOK (atTables ret0_placeOK) ret0Imms
example := hk_ofPlaceOK (atTables ret0_placeOK) ret0Imms
example (rS : Scc.Sem.Range) := hKex_ofPlaceOK (atTables ret0_placeOK) ret0Imms (rS := rS)

/-- A layout naming the heap kind's exit call at the overflow one's label. -/
def dupΛ : Scc.Sem.Layout :=
  { Scc.Cert.Link.X64.linkOf ret0Cells ret0Secs with
    abortLbl := fun k => match k with
      | .heap => Scc.Cert.Link.abortName .overflow
      | k => Scc.Cert.Link.abortName k }

/-- **Negative**: with the heap exit call at the overflow one's label, the
sites resolve but are not distinct, so A6's check fails on them. -/
example : ¬ ∃ ss, Scc.Cert.Rt.X64.sitesOf dupΛ.code.lo ret0Cells dupΛ = some ss ∧ ss.Nodup := by
  rintro ⟨ss, hs, hnd⟩
  have : Scc.Cert.Rt.X64.sitesOf dupΛ.code.lo ret0Cells dupΛ =
      some [4196177, 4196217, 4198555, 4198555, 4198691, 4198759, 4198827] := by decide +kernel
  rw [this] at hs; cases hs
  simp at hnd

/-- The exit call's address at `ret0`'s record. -/
theorem ret0P_exit : (ret0P.lab Abort.overflow.exit).toBitVec.toNat = 4198555 :=
  lab_toNat (atTables ret0_placeOK) ret0Imms ret0_ovf

/-- **The site premises hold by hand at `ret0`'s record**: the exit call is off the release and take sites and no
other abort kind's exit call. -/
example :
    (∀ a, (μ ret0P).site .release = some a → (ret0P.lab Abort.overflow.exit).toBitVec.toNat ≠ a) ∧
    (∀ a, (μ ret0P).site .take = some a → (ret0P.lab Abort.overflow.exit).toBitVec.toNat ≠ a) ∧
    (∀ k a, (μ ret0P).abortAt k = some a → (ret0P.lab Abort.overflow.exit).toBitVec.toNat = a →
      k = .overflow) := by
  rw [ret0P_exit]
  refine ⟨fun a h => ?_, fun a h => ?_, fun k a h e => ?_⟩
  · have hr : (μ ret0P).site .release = some 4196217 := by decide +kernel
    rw [hr] at h; cases h; decide
  · have ht : (μ ret0P).site .take = some 4196177 := by decide +kernel
    rw [ht] at h; cases h; decide
  · subst e
    cases k with
    | overflow => rfl
    | heap => exact absurd h (by decide +kernel)
    | stack => exact absurd h (by decide +kernel)
    | threads => exact absurd h (by decide +kernel)
    | writeErr => exact absurd h (by decide +kernel)

/-- **Negative**: `hk` fails at the heap exit call's address (the heap
kind's site is there). -/
example : ¬ (∀ k a, (μ ret0P).abortAt k = some a → (4198623 : Nat) = a → k = .overflow) := by
  intro hk
  have hh : (μ ret0P).abortAt .heap = some 4198623 := by decide +kernel
  cases hk .heap 4198623 hh rfl

/-- **Negative**: the heap exit call is not at the overflow exit call. -/
example : Scc.Sem.X64.codeLabel ret0Λ.code.lo ret0Cells "scc_rt_abort_heap_exit" ≠ some 4198555 := by
  decide +kernel

end Spike.Test.LowerX64AbortOfPlaceOK
