/-
**The runtime's phase structures at `ret0.x`'s record from `placeOK`**
(`Spike/Lib/Rt/X64RtPhRec.lean`): the switch's, `scc_rt_main`'s at
`bareMC` and `scc_rt_thread_init`'s, with no premise but the placed output.
The twin of the ARM record instance.
-/
import Spike.Lib.Rt.X64RtPhRec
import Spike.Test.X64Ret0PlaceOK

namespace Spike.Lib.X64.Rt.PhRecOfTest

open Scc.Cert.PlaceOK.X64 (atTables)

open Spike.Lib.X64.Rt Spike.Lib.X64.Rt.PhRecOf
open Scc.Cert.PlaceOK.X64.Test (ret0_placeOK)

/-- **The switch's phase facts at `ret0.x`'s record.** -/
example := swPh_ofPlaceOK (atTables ret0_placeOK) SccCode.ret0Imms

/-- **`scc_rt_main`'s phase facts at `ret0.x`'s record**, at `bareMC`. -/
example := mainPh_bare_ofPlaceOK (atTables ret0_placeOK) SccCode.ret0Imms

/-- **`scc_rt_thread_init`'s phase facts at `ret0.x`'s record.** -/
example := tiPh_ofPlaceOK (atTables ret0_placeOK) SccCode.ret0Imms

/-- The record's labels at `ret0.x`. -/
example := hlab_ofPlaceOK (atTables ret0_placeOK) SccCode.ret0Imms

/-- **`scc_rt_alloc_tcb`'s phase facts at `ret0.x`'s record**, returning to
`.Lscc_rt_start.x0`. -/
example := tcbPh_ofPlaceOK (atTables ret0_placeOK) SccCode.ret0Imms

/-- **`scc_rt_stack_take`'s phase facts at `ret0.x`'s record**, returning to
`.x7`. -/
example := takePh_ofPlaceOK (atTables ret0_placeOK) SccCode.ret0Imms

/-- The counters distinct, the TCB off them, `.rodata` off the pool, at
`ret0.x`'s record. -/
example := counters_ne (atTables ret0_placeOK) SccCode.ret0Imms
example := tcbSep (atTables ret0_placeOK) SccCode.ret0Imms
example := rodata_stackPool_disjoint_ofPlaceOK (atTables ret0_placeOK) SccCode.ret0Imms

/-! The tables `…_of_tab` reads sit in the checked ones: the switch's and
`scc_rt_thread_init`'s, `scc_rt_alloc_tcb`'s, `scc_rt_stack_take`'s and
the phase rows (`tkPhTab`) in A6's (`rtPhTab none`), `scc_rt_main`'s in the
full table. (A wrong fact in them fails `rtPhOk`: `Spike/Test/X64RtPhTab.lean`.) -/

example : ∀ f ∈ swPhTab, f ∈ rtPhTab none := fun _ hf => by simp only [rtPhTab, List.mem_append]; simp [hf]
example : ∀ f ∈ tiPhTab, f ∈ rtPhTab none := fun _ hf => by simp only [rtPhTab, List.mem_append]; simp [hf]
example : ∀ f ∈ tcbPhTab, f ∈ rtPhTab none := fun _ hf => by simp only [rtPhTab, List.mem_append]; simp [hf]
example : ∀ f ∈ takePhTab, f ∈ rtPhTab none := fun _ hf => by simp only [rtPhTab, List.mem_append]; simp [hf]
example : ∀ f ∈ tkPhTab, f ∈ rtPhTab none := fun _ hf => by simp only [rtPhTab, List.mem_append]; simp [hf]
example : ∀ f ∈ mainPhTab bareMC, f ∈ rtPhTab (some bareMC) := fun _ hf => by
  simp only [rtPhTab, List.mem_append]; simp [hf]

/-- `.x7` is `.entry` + 12 in `ret0`'s cells, the gap `tiPh_ofPlaceOK`
reads; another distance fails. -/
example : Scc.Cert.Rt.X64.labelGapB SccCode.ret0Cells Code.Ti.entryL Code.Ti.x7L 12 = true := by decide +kernel
example : Scc.Cert.Rt.X64.labelGapB SccCode.ret0Cells Code.Ti.entryL Code.Ti.x7L 7 = false := by decide +kernel

/-! The rows `noTk_tk` reads: a pc's row before the take has bit 3 set; the
take site's next pc's (`0`) does not, so it is no row for `noTk_tk`. -/
example : (Code.Tcb.lenL, 158, 13) ∈ tcbTkRows ++ takeTkRows ++ [(Code.Take.siteL, 1, 0)] := by decide
example : (Code.Take.siteL, 1, 0) ∈ tcbTkRows ++ takeTkRows ++ [(Code.Take.siteL, 1, 0)] := by decide
example : ¬ (0 / 8 % 2 = 1) := by decide
example : (Code.Tcb.lenL, 158, 12) ∉ tcbTkRows ++ takeTkRows ++ [(Code.Take.siteL, 1, 0)] := by decide

end Spike.Lib.X64.Rt.PhRecOfTest
