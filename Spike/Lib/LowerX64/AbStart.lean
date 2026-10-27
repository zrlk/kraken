/-
**The loaded thread is off the write abort** (x86-64): `hab0` of the
consumers (`¬ WriteAb.Ab lab s` at the canonical loader's thread) at the
runtime's layout of an output passing `placeOK` (`RuntimeLayout.ofPlaceOK`).
The thread starts at `_start` (A1, `hpc_ofPlaceOKE`), the first cell of
`_start`'s run (A11's `_start` blocks), while every pc of `WriteAb.abPcs`
is a cell in a run of a runtime label of `scc_rt_print`, `scc_rt_abort` or
`scc_rt_abort_write` (`abPos_inRunB`, from A7's `printIn` and `abortIn`);
distinct positions sit at distinct pcs (`pc_ne_of_inRunB`).

- `start_notAbPc_ofPlaceOK`: `lab "_start" ∉ abPcs lab`.
- `hab0_ofPlaceOKE`: `hab0` at any entry state; `hab0_ofPlaceOK` at Linux's.
-/
import Spike.Lib.LowerX64.AllocRa
import Spike.Lib.X64StartOfPlaceOK
import Spike.Lib.Rt.X64RtCodeSetup

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.Rt.X64 (inRunB_of_blockAt pc_ne_of_inRunB blockAt_of_blockAtB)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WriteAb (Ab abPcs not_ab_of_pc)

/-- No label of the write abort's positions is `_start`. -/
theorem abPos_ne_start : abPos.all (fun p => p.1 != "_start") = true := by decide

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

/-- **`_start` is none of the write abort's pcs** at the record of an
output passing `placeOK`. -/
theorem start_notAbPc_ofPlaceOK :
    (RuntimeLayout.ofPlaceOK h i).lab "_start" ∉ abPcs (RuntimeLayout.ofPlaceOK h i).lab := by
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  have he0 := (Spike.Lib.X64.Rt.rtCode0_of_placeOKAt h).start0
  simp only [Spike.Lib.X64.Rt.Code.Start.entryIn, Bool.and_eq_true] at he0
  obtain ⟨k, hk⟩ := blockAt_of_blockAtB he0.1.1
  have hs := inRunB_of_blockAt hk (i := 0) (by decide)
  simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero] at hs
  rw [abPcs_eq, List.mem_map]
  rintro ⟨p, hp, he⟩
  refine pc_ne_of_inRunB (RuntimeLayout.ofPlaceOK h i).lays
    (abPos_inRunB (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) p hp) hs ?_ ?_
  · intro hpe
    have hn := List.all_eq_true.mp abPos_ne_start p hp
    rw [congrArg Prod.fst hpe] at hn
    exact absurd hn (by decide)
  · rw [he]; simp

/-- **`hab0`**: the loaded thread at an entry state `E` is off the write
abort, at the record of an output passing `placeOK`. -/
theorem hab0_ofPlaceOKE (E : Scc.Sem.Entry) :
    ¬ Ab (RuntimeLayout.ofPlaceOK h i).lab
      (Scc.Sem.X64.threadAt E (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
        (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)) :=
  not_ab_of_pc (by rw [Spike.Lib.X64.PhRec.hpc_ofPlaceOKE h i E]; exact start_notAbPc_ofPlaceOK h i)

/-- **`hab0`** at the Linux entry state. -/
theorem hab0_ofPlaceOK :
    ¬ Ab (RuntimeLayout.ofPlaceOK h i).lab
      (Scc.Sem.X64.threadAt Scc.Sem.Entry.linux (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
        (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)) :=
  hab0_ofPlaceOKE h i _

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hab0_ofPlaceOKE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hab0_ofPlaceOKE

end Spike.Lib.LowerX64
