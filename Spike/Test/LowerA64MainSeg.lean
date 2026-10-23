import Spike.Lib.LowerA64.Main
import Spike.Lib.LowerA64.MainCode
import Spike.Test.A64Ret0PlaceOKE
import Spike.Test.LowerInv
import Spike.Lib.Rt.A64LayoutOfPlaceOK

/-!
# `main_seg_of_placeOK` at `ret0.w` (AArch64)

The generic statement (`Spike/Lib/LowerA64/Main.lean`) instantiated at
`ret0.w`, every hypothesis discharged by the program's own facts: the
acceptance (`main0_accepted`), the pipeline's success (by the kernel), the
output's `PlaceOK` (`ret0_placeOK`, `Spike/Test/A64Ret0PlaceOKE.lean`). The context it gives is `main`'s emitted one
(`mainCtx`, `Spike/Test/LowerInv.lean`): `wc_main` the `18`th function, a
32-byte frame, its abort label `.L18_wc_main.abort_overflow` (by `#guard`).
-/

namespace Spike.Test.LowerA64MainSeg

open CoreLang CoreTerm
open Spike.Lib.LowerA64 Spike.Test.LowerInv
open Scc.Lower.Inv (lower0 Res func0)

/-- A pipeline that succeeds gives its total form. -/
theorem lowerAll?_ok {cfg : Scc.Config} {p : Prog} (h : (Scc.Lower.A64.lowerAll? cfg p).isOk = true) :
    Scc.Lower.A64.lowerAll? cfg p = .ok (Scc.Lower.A64.lowerAll cfg p) := by
  unfold Scc.Lower.A64.lowerAll
  cases hl : Scc.Lower.A64.lowerAll? cfg p with
  | ok e => rfl
  | error _ => rw [hl] at h; cases h

theorem ret0_lowerAll?_ok : (Scc.Lower.A64.lowerAll? { arch := .arm } [main0]).isOk = true := by decide +kernel

/-- **`ret0.w`'s `main` is one segment, from its `PlaceOK`.** -/
theorem ret0_main_seg : MainSeg { arch := .arm } main0 := main_seg_of_placeOK (cfg := { arch := .arm }) main0_accepted
  (lowerAll?_ok ret0_lowerAll?_ok) (pcfg := Scc.Cert.PlaceOK.Config.canonical)
  (Scc.Cert.PlaceOK.A64.atTables Spike.Test.A64Ret0PlaceOKE.ret0_placeOK)

-- The context it names is `main`'s emitted one.
#guard (Scc.Lower.A64.lowerAll { arch := .arm } [main0]).low.ir.funcs.zipIdx.contains
  (func0 (Scc.Lower.Names.user "main") ret0Res, 18)
/-- `main`'s context in `ret0.w`'s lowered IR. -/
def cx0 : Scc.Emit.A64.FnCtx :=
  Scc.Lower.A64.ctxOf (Scc.Lower.A64.lowerAll { arch := .arm } [main0]).low.ir 18
    (func0 (Scc.Lower.Names.user "main") ret0Res)

#guard cx0.frame == 32 && cx0.local "abort_overflow" == ".L18_wc_main.abort_overflow" &&
  cx0.prefix ++ "0_entry" == ".L18_wc_main.0_entry" && proL cx0 == ".L18_wc_main.stack_grow" &&
  cx0.slots == mainCtx.slots && cx0.frame == mainCtx.frame

/-- **`mainCode_ofPlaceOK` at `ret0.w`**: `main`'s code facts, from its `PlaceOK`. -/
example := mainCode_ofPlaceOK (cfg := { arch := .arm }) main0_accepted (lowerAll?_ok ret0_lowerAll?_ok)
  (Scc.Cert.PlaceOK.A64.atTables Spike.Test.A64Ret0PlaceOKE.ret0_placeOK)

end Spike.Test.LowerA64MainSeg
