import Spike.Test.A64Hello1PlaceOKELit

/-!
# `hello1.w`'s stack need rows, per function (AArch64)

A regression test of `needOk1` (`Scc/Cert/Code1A64.lean`) on scc's own
output for `hello1.w` (`hello1L`, `Spike/Test/A64Hello1PlaceOKELit.lean`):
its three stack-checked functions `scc_rt_main`, `wc_rodata` and `wc_main`
each pass `needOk1` at their context's frame and A12's code check `fnOk1`,
one kernel decision per function. `wc_rodata` calls `scc_rt_alloc` and
`wc_main` calls `scc_rt_print`, runtime routines without a row of the stack
need table: they pass only as runtime routines within the headroom
(`rtOk`). A need below the frame, or a row-less callee that is not a
runtime routine, fails.
-/

namespace Spike.Test.A64Hello1NeedOk1

open Scc.Cert.Code1A64 (needOk1 fnOk1 callees ctxOf rtOk)
open Scc.Cert.NeedA64 (row?)
open Spike.Test.A64Hello1PlaceOKE (hello1L)

/-- `hello1.w`'s IR, as its output names it. -/
def ir : Scc.IR.Program := hello1L.place.ir.getD default

/-- The `fi`th function of the IR. -/
def fnAt (fi : Nat) : Scc.IR.Func := ir.funcs[fi]?.getD default

/-- `needOk1` of the `fi`th function at its context's frame. -/
def needAt (fi : Nat) : Bool :=
  needOk1 hello1L.place.need (fnAt fi).name (ctxOf ir fi (fnAt fi)).frame (fnAt fi)

/-- A12's code check `fnOk1` of the `fi`th function at its context. -/
def codeAt (fi : Nat) : Bool := fnOk1 hello1L.prog hello1L.place.need (ctxOf ir fi (fnAt fi)) (fnAt fi)

-- The output names its IR; its stack-checked functions are the 1st, 18th
-- and 19th, with these frames, callees and rows.
#guard hello1L.place.ir.isSome
#guard ((ir.funcs.zipIdx.filter fun (p : Scc.IR.Func × Nat) => p.1.checkStack).map
  fun (p : Scc.IR.Func × Nat) => (p.1.name, p.2)) == [("scc_rt_main", 1), ("wc_rodata", 18), ("wc_main", 19)]
#guard [1, 18, 19].map (fun fi => (ctxOf ir fi (fnAt fi)).frame) == [80, 48, 96]
#guard hello1L.place.need == [("scc_rt_main", 80, 176), ("wc_rodata", 48, 48), ("wc_main", 96, 96)]
#guard (callees (fnAt 1)) == (["wc_rodata", "wc_main"], [])
#guard (callees (fnAt 18)) == (["scc_rt_alloc"], [])
#guard (callees (fnAt 19)) == (["scc_rt_print"], [])

/-! ## One decision per function -/

theorem scc_rt_main_needOk1 : needAt 1 = true := by decide +kernel
theorem wc_rodata_needOk1 : needAt 18 = true := by decide +kernel
theorem wc_main_needOk1 : needAt 19 = true := by decide +kernel

theorem scc_rt_main_fnOk1 : codeAt 1 = true := by decide +kernel
theorem wc_rodata_fnOk1 : codeAt 18 = true := by decide +kernel
theorem wc_main_fnOk1 : codeAt 19 = true := by decide +kernel

/-! ## Callees without a row -/

-- `scc_rt_alloc` and `scc_rt_print` have no row; each is a runtime routine
-- within the headroom.
#guard (row? hello1L.place.need Scc.Lower.Names.alloc).isNone
#guard (row? hello1L.place.need Scc.Lower.Names.print).isNone
#guard rtOk Scc.Lower.Names.alloc && rtOk Scc.Lower.Names.print

-- `wc_main` calling an unknown function without a row in place of
-- `scc_rt_print` fails.
#guard !needOk1 hello1L.place.need "wc_main" 96
  { fnAt 19 with blocks := (fnAt 19).blocks.map fun b =>
      { b with insts := b.insts.map fun
        | .call ds g ws => .call ds (if g == Scc.Lower.Names.print then "foo" else g) ws
        | i => i } }

-- A need below the frame fails (`wc_rodata` with need 32 below its frame 48),
-- as does `scc_rt_main`'s need not covering its frame plus `wc_main`'s.
#guard !needOk1 [("scc_rt_main", 80, 176), ("wc_rodata", 48, 32), ("wc_main", 96, 96)] "wc_rodata" 48 (fnAt 18)
#guard !needOk1 [("scc_rt_main", 80, 175), ("wc_rodata", 48, 48), ("wc_main", 96, 96)] "scc_rt_main" 80 (fnAt 1)

end Spike.Test.A64Hello1NeedOk1
