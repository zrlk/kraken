import Spike.Lib.X64StartOfPlaceOK
import Spike.Lib.X64Ret0Correct

/-!
# The start segment's runtime premises from `placeOK` (x86-64): `ret0`'s oracle

At `ret0`'s layout from its placement check (`ret0P`), the consumer's value
invariant of `Spike/Lib/X64StartOfPlaceOK.lean` (`GOf` at the canonical
load's memory `m0Of`) is `ret0`'s hand one (`Spike/Lib/X64Ret0Correct.lean`'s
`ret0G`), and the premises instantiate there.
-/

namespace Spike.Lib.X64.PhRec.Test

open Scc.Cert.PlaceOK.X64 (atTables)

open Kraken Kraken.Promising
open Spike.Lib.X64.Rt (ret0P)
open SccCode (ret0Imms)
open Scc.Cert.PlaceOK.X64.Test (ret0_placeOK)

/-- The limit word and the limit at `ret0P` are the hand ones. -/
example : limW ret0P = Spike.Lib.X64.Flow.Ret0.Correct.limW ∧ limV ret0P = Spike.Lib.X64.Flow.Ret0.Correct.limV :=
  ⟨by decide +kernel, by decide +kernel⟩

example := G0_ofPlaceOK (atTables ret0_placeOK) ret0Imms
example := limInit_ofPlaceOK (atTables ret0_placeOK) ret0Imms
example := hroomM_ofPlaceOK (atTables ret0_placeOK) ret0Imms
example {frame : Int} (h0 : 0 ≤ frame) (h1 : frame ≤ 4096) := hroomU_ofPlaceOK (atTables ret0_placeOK) ret0Imms h0 h1
example := hGf_ofPlaceOK (atTables ret0_placeOK) ret0Imms

/-- The loaded thread's phase at `ret0P` is `13`, so it is out of the take
and owns the load's counters. -/
theorem ret0_ph0 : ph ret0P (Scc.Sem.X64.pcOf (Scc.Sem.X64.threadAt Scc.Sem.Entry.linux ret0P.Λ.code.lo ret0P.prog
    (Scc.Sem.loadSyms ret0P.Λ SccCode.ret0Secs.rodata))) = 13 := by
  decide +kernel

example := htk0_ofPlaceOK (atTables ret0_placeOK) ret0Imms ret0_ph0
example := hown0_ofPlaceOK (atTables ret0_placeOK) ret0Imms ret0_ph0

/-- The loaded thread at `_start`, and the TCB's limit word off the heap and
the data, from `placeOK` alone. -/
example := hpc_ofPlaceOK (atTables ret0_placeOK) ret0Imms
example := hclr_ofPlaceOK (atTables ret0_placeOK) ret0Imms

/-- `_start`'s phase from `placeOK` alone. -/
example := hph0_ofPlaceOK (atTables ret0_placeOK) ret0Imms

set_option maxRecDepth 100000 in
/-- The pinned phases at `ret0P`: `_start`'s, and the atomic accesses' bits. -/
theorem ret0_phs : ph ret0P (ret0P.lab "_start").toBitVec.toNat = 13 ∧
    ph ret0P (Spike.Lib.X64.Flow.Ret0.AllocTcb.rmwPc ret0P.lab).toBitVec.toNat % 2 = 1 ∧
    ph ret0P (Spike.Lib.X64.Flow.Ret0.StackTake.swpPc ret0P.lab).toBitVec.toNat / 2 % 2 = 0 ∧
    ph ret0P (Spike.Lib.X64.Flow.Ret0.StackTake.nextPc ret0P.lab).toBitVec.toNat / 4 % 2 = 1 := by
  rw [show ret0P.lab = Spike.Lib.X64.Flow.Ret0.Inst.labT from Spike.Lib.X64.Flow.Ret0.Inst.ret0_labT]
  decide +kernel

end Spike.Lib.X64.PhRec.Test
