import Spike.Lib.A64StartOfPlaceOK
import Spike.Lib.A64Ret0Correct

/-!
# The start segment's runtime premises from `placeOK`: `ret0`'s oracle

At `ret0`'s layout from its placement check (`ret0P`), the consumer's value
invariant of `Spike/Lib/A64StartOfPlaceOK.lean` (`GOf` at the canonical
load's memory `m0Of`) is `ret0`'s hand one (`Spike/Lib/A64Ret0Correct.lean`'s
`ret0G`: the limit word and limit, the loaded memory), and the premises
instantiate there.
-/

namespace Spike.Lib.A64.PhRec.Test

open Kraken Kraken.Promising
open Spike.Lib.A64.Rt (ret0P)
open SccCode (ret0Prog ret0Secs ret0Imms)
open Scc.Cert.PlaceOK.A64.Test (ret0_placeOK)

/-- The limit word and the limit at `ret0P` are the hand ones. -/
example : limW ret0P = Spike.Lib.A64.Flow.Ret0.Correct.limW ∧ limV ret0P = Spike.Lib.A64.Flow.Ret0.Correct.limV :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- The canonical load's memory at `ret0P` is `ret0`'s loaded memory. -/
example : m0Of ret0P.Λ ret0Prog ret0Secs = Spike.Lib.A64.Flow.Ret0.Correct.ret0Mem0 := rfl

/-- **The value invariant at `ret0P` is `ret0G`.** -/
theorem gOf_ret0 : GOf ret0P (m0Of ret0P.Λ ret0Prog ret0Secs) = Spike.Lib.A64.Flow.Ret0.Correct.ret0G := by
  have hw : limW ret0P = Spike.Lib.A64.Flow.Ret0.Correct.limW := by decide +kernel
  have hv : limV ret0P = Spike.Lib.A64.Flow.Ret0.Correct.limV := by decide +kernel
  unfold GOf Spike.Lib.A64.Flow.Ret0.Correct.ret0G
  rw [hw, hv]
  rfl

/-- The premises at `ret0P`: the invariant at load, the limit word's initial
value, `scc_rt_main`'s room, the counters owned. -/
example : ∀ t0, Spike.Lib.A64Consumer.TPar.load (ret0Prog, ret0Secs) ret0P.Λ = some t0 →
    MemInv Spike.Lib.A64.Flow.Ret0.Correct.ret0G t0.1.mem := by
  rw [← gOf_ret0]; exact G0_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms

example : (m0Of ret0P.Λ ret0Prog ret0Secs).initVal ⟨ret0P.pinA + 16#64, 8⟩ = 0 :=
  limInit_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms

example := hroomM_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms
example {frame : Int} (h0 : 0 ≤ frame) (h1 : frame ≤ 4095) := hroomU_ofPlaceOK
    (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms h0 h1
example {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} :=
  hownT_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms (rd := rd) (G := G) (lbl := fun _ => none)
      (lsize := fun _ => 0)

/-- The runtime main's and the switch's phase records at `ret0`'s placed output. -/
example := hmph_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms
example := hsw_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms

/-- The loaded thread at `ret0P`: at `_start`, not in the take's phase, its
owned words the load's; the value invariant at `ret0`'s placed words (the
hand `ret0_Gpl`'s statement, here from `placeOK`). -/
example : (S0Of ret0P ret0Prog ret0Secs).st.2 = ret0P.lab "_start" := hpc_ofPlaceOK
    (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms
example : ¬ Tk ret0P (S0Of ret0P ret0Prog ret0Secs) := htk0_ofPlaceOK
    (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms
example := hown0_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms
example : ∀ a v, ret0P.Λ.heap.contains a ∨ ret0P.Λ.data.contains a →
    Spike.Lib.A64.Flow.Ret0.Correct.ret0G (Scc.Sem.wordLoc a) v := by
  rw [← gOf_ret0]; exact hGpl_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms

/-- The loaded thread at `ret0P` is the hand `ret0S0`. -/
example : S0Of ret0P ret0Prog ret0Secs = Spike.Lib.A64.Flow.Ret0.Correct.ret0S0 := rfl

end Spike.Lib.A64.PhRec.Test
