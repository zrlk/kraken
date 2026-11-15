import Scc.Cert.Arm
import Scc.Test.Src

/-!
# `scc --granule` on the AArch64 pipeline (untrusted, empirical)

`Scc.Cert.Arm.compile` with and without `granule` (`Scc.Lower.A64.Emitted.listing`) on some
`Scc/Test/*.w` programs: without it the text has no descriptor word; with it the text has at least
one, and the GC tables (from `scc_stackmap` on) are printed unchanged after the text. That the text
without the flag is the committed one is `Spike/Gen/drift.sh`'s check. The X64 twin is
`Scc/Test/GranuleFlagX64Test.lean` (the two ISAs' modules cannot be imported together).
-/

namespace Scc.Test.GranuleFlagA64

/-- The texts of `src` without and with the granule pass. -/
def texts (src : String) : Except String (String × String) := do
  let cfg : Config := { arch := .arm }
  return (← Scc.Cert.Arm.compile cfg src, ← Scc.Cert.Arm.compile cfg src (granule := true))

/-- The number of descriptor words in a text. -/
def words (t : String) : Nat := (t.splitOn Scc.Emit.Granule.wordLine).length - 1

/-- The text after the GC tables' first label, cut at every later occurrence of it. -/
def tables (t : String) : List String := (t.splitOn "scc_stackmap:").drop 1

/-- Without the flag no word, with it at least one, and the same tables after the text. -/
def ok (src : String) : Bool :=
  match texts src with
  | .ok (off, on) => words off == 0 && words on > 0 && tables on == tables off && !(tables off).isEmpty
  | .error _ => false

#guard ok (w_src% "Scc/Test/ret0.w")
#guard ok (w_src% "Scc/Test/hello1.w")
#guard ok (w_src% "Scc/Test/wake.w")

end Scc.Test.GranuleFlagA64
