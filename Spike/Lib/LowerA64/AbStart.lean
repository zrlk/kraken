/-
**The loaded thread is off the write abort** (AArch64): `hab0` of the
consumers (`¬ WriteAb.Ab lab s` at the canonical loader's thread) at the
runtime's layout of an output passing `placeOK` (`RuntimeLayout.ofPlaceOK`).
The thread starts at `_start` (A1, `hpc_ofPlaceOKE`), the first instruction
of `_start`'s run (A11's `_start` block), while every pc of
`WriteAb.abPcs` is a position in a run of a runtime label of
`scc_rt_print`, `scc_rt_abort` or `scc_rt_abort_write` (`abPos_inRun`, from
A7's `printIn` and `abortIn`); distinct positions sit at distinct pcs
(`pc_ne_of_inRun`).

- `start_notAbPc_ofPlaceOK`: `lab "_start" ∉ abPcs lab`.
- `hab0_ofPlaceOKE`: `hab0` at any entry state; `hab0_ofPlaceOK` at Linux's.
-/
import Spike.Lib.LowerA64.AllocRa
import Spike.Lib.A64StartOfPlaceOK
import Spike.Lib.Rt.A64RtCodeSetup

namespace Spike.Lib.LowerA64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Rt.A64 (inRun_of_blockAt pc_ne_of_inRun)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WriteAb (Ab abPcs not_ab_of_pc)

/-- No label of the write abort's positions is `_start`. -/
theorem abPos_ne_start : abPos.all (fun p => p.1 != "_start") = true := by decide

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

/-- **`_start` is none of the write abort's pcs** at the record of an
output passing `placeOK`. -/
theorem start_notAbPc_ofPlaceOK :
    (RuntimeLayout.ofPlaceOK h i).lab "_start" ∉ abPcs (RuntimeLayout.ofPlaceOK h i).lab := by
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  have hs := inRun_of_blockAt (Spike.Lib.A64.Rt.rtCode0_of_placeOKAt h).entry (i := 0) (by decide)
  rw [abPcs_eq, List.mem_map]
  rintro ⟨p, hp, he⟩
  refine pc_ne_of_inRun (RuntimeLayout.ofPlaceOK h i).lays
    (abPos_inRun (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) p hp) hs ?_ ?_
  · intro hpe
    have hn := List.all_eq_true.mp abPos_ne_start p hp
    rw [congrArg Prod.fst hpe] at hn
    exact absurd hn (by decide)
  · rw [he]; exact (Spike.Lib.A64.Flow.ofNat4_zero _).symm

/-- **`hab0`**: the loaded thread at an entry state `E` is off the write
abort, at the record of an output passing `placeOK`. -/
theorem hab0_ofPlaceOKE (E : Scc.Sem.Entry) :
    ¬ Ab (RuntimeLayout.ofPlaceOK h i).lab
      (Spike.Lib.A64.PhRec.S0OfE E (RuntimeLayout.ofPlaceOK h i) o.prog o.secs) :=
  not_ab_of_pc (by rw [Spike.Lib.A64.PhRec.hpc_ofPlaceOKE h i E]; exact start_notAbPc_ofPlaceOK h i)

/-- **`hab0`** at the Linux entry state. -/
theorem hab0_ofPlaceOK :
    ¬ Ab (RuntimeLayout.ofPlaceOK h i).lab
      (Spike.Lib.A64.PhRec.S0OfE Scc.Sem.Entry.linux (RuntimeLayout.ofPlaceOK h i) o.prog o.secs) :=
  hab0_ofPlaceOKE h i _

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hab0_ofPlaceOKE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hab0_ofPlaceOKE

end Spike.Lib.LowerA64
