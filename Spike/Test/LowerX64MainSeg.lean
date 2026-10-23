import Spike.Lib.LowerX64.Main
import Spike.Lib.LowerX64.MainCode
import Spike.Test.X64Ret0PlaceOKE
import Spike.Test.LowerX64Ret0Oracle

/-!
# `main_seg_of_placeOK` at `ret0.w` (x86-64)

The twin of `Spike/Test/LowerA64MainSeg.lean`: the generic statement
(`Spike/Lib/LowerX64/Main.lean`) instantiated at `ret0.w`, every hypothesis
discharged by the program's own facts: the acceptance (`main0_accepted`),
the pipeline's success (by the kernel), the output's `PlaceOK`
(`ret0_placeOK`, `Spike/Test/X64Ret0PlaceOKE.lean`), the body's one-word
result (`ret0_lower0`). The frame it gives is
`main`'s emitted one (`mainFr`, `Spike/Test/LowerInvX64.lean`): 16 bytes,
its abort label `.Lwc_main.ovf`, and the prologue's cell sizes A9 reads off
the listing are the hand ones (`5 9 3 2 4`, by `#guard`).
-/

namespace Spike.Test.LowerX64MainSeg

open Scc.Cert.PlaceOK.X64 (atTables)

open CoreLang CoreTerm
open Spike.Lib.LowerX64 Spike.Test.LowerX64Ret0Oracle
open Scc.Lower.Inv (lower0 Res func0)

/-- A pipeline that succeeds gives its total form. -/
theorem lowerAll?_ok {cfg : Scc.Config} {p : Prog} (h : (Scc.Lower.X64.lowerAll? cfg p).isOk = true) :
    Scc.Lower.X64.lowerAll? cfg p = .ok (Scc.Lower.X64.lowerAll cfg p) := by
  unfold Scc.Lower.X64.lowerAll
  cases hl : Scc.Lower.X64.lowerAll? cfg p with
  | ok e => rfl
  | error _ => rw [hl] at h; cases h

theorem main0_accepted : Scc.Lower.Accepted0 [main0] = true := by decide +kernel

theorem ret0_lowerAll?_ok : (Scc.Lower.X64.lowerAll? { arch := .x64 } [main0]).isOk = true := by decide +kernel

/-- `[main0]` is `ret0.w`'s source. -/
theorem main0_src : [main0] = Spike.Lib.Ret0Src.ret0Src := rfl

/-- **`ret0.w`'s `main` is one segment, from its `PlaceOK`.** -/
theorem ret0_main_seg : MainSeg { arch := .x64 } main0 SccCode.ret0Asm.sizes :=
  main_seg_of_placeOK (cfg := { arch := .x64 }) main0_accepted (lowerAll?_ok ret0_lowerAll?_ok)
    (pcfg := Scc.Cert.PlaceOK.Config.canonical) (labelOffs := SccCode.ret0Asm.labelOffs)
    (by rw [main0_src]; exact Spike.Test.X64Ret0PlaceOKE.ret0_placeOK)

/-- `accepted0_ret_singleton` at `ret0.w` (`main_seg_of_placeOK` uses it in place
of a hypothesis); `ret0Res` indeed returns one word. -/
example : ∃ w, ret0Res.ret = [w] := Scc.Lower.Inv.accepted0_ret_singleton main0_accepted ret0_lower0
#guard ret0Res.ret.length == 1

-- The frame it names is `main`'s emitted one, and the cells are `ret0Cells`.
#guard (Scc.Lower.X64.lowerAll { arch := .x64 } [main0]).low.ir.funcs.contains
  (func0 (Scc.Lower.Names.user "main") ret0Res)
/-- `main`'s frame in `ret0.w`'s lowered IR. -/
def fr0 : Scc.Emit.X64.Frame :=
  frOf (Scc.Lower.X64.lowerAll { arch := .x64 } [main0]).low.ir (func0 (Scc.Lower.Names.user "main") ret0Res)

#guard fr0.size == 16 && fr0.slots == Spike.Test.LowerInvX64.mainFr.slots &&
  fr0.maps == Spike.Test.LowerInvX64.mainFr.maps && ovfL fr0 == ".Lwc_main.ovf" && proL fr0 == ".Lwc_main.stk"
#guard Scc.Cert.PlaceOK.X64.cellsOfEmitted (Scc.Lower.X64.lowerAll { arch := .x64 } [main0]) SccCode.ret0Asm.sizes ==
  SccCode.ret0Cells
#guard sizesAt SccCode.ret0Cells ".Lwc_main.chk" 0 5 == [5, 9, 3, 2, 4]

/-- **`mainCode_ofPlaceOK` at `ret0.w`**: `main`'s code facts, from its `PlaceOK`. -/
example := mainCode_ofPlaceOK (cfg := { arch := .x64 }) main0_accepted (lowerAll?_ok ret0_lowerAll?_ok)
  (labelOffs := SccCode.ret0Asm.labelOffs)
  (by rw [main0_src]; exact atTables Spike.Test.X64Ret0PlaceOKE.ret0_placeOK)

end Spike.Test.LowerX64MainSeg
