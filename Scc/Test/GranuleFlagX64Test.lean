import Scc.Cert.X64
import Scc.Test.Src

/-!
# `scc --granule` on the x86-64 pipeline (untrusted, empirical)

`Scc.Cert.X64.compile` with and without `granule` (`Scc.Lower.X64.Emitted.listing`) on some
`Scc/Test/*.w` programs: without it the text has no descriptor word; with it the text has at least
one, and the GC tables (from `scc_stackmap` on) are printed unchanged after the text. That the text
without the flag is the committed one is `Spike/Gen/drift.sh`'s check. The A64 twin is
`Scc/Test/GranuleFlagA64Test.lean` (the two ISAs' modules cannot be imported together).
-/

namespace Scc.Test.GranuleFlagX64

/-- The texts of `src` without and with the granule pass. -/
def texts (src : String) : Except String (String × String) := do
  let cfg : Config := { arch := .x64 }
  return (← Scc.Cert.X64.compile cfg src, ← Scc.Cert.X64.compile cfg src (granule := true))

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

end Scc.Test.GranuleFlagX64
