import Scc.Cert.Blocks

/-!
# The offset rows of a listing

The text of a program's block offsets (`Scc.Cert.Rt.A64.ofGrps`'s second
argument, `Scc/Cert/Rt/OffsA64.lean`): per block of the analysis
(`Blocks.analyse`), in block order, which is the block table's
(`Blocks.renderCode`), its region and entry offsets. The placement check
(`PlaceOK.A64`, A5) checks them; nothing here is trusted.
-/

namespace Scc.Cert.Blocks

/-- **The offsets of an AArch64 listing's blocks**: the definition
`{pfx}Offs : List (Int × Int × SO)`, one `(lo, hi, o)` per block. -/
def renderOffs (r : Result) (pfx : String) : String :=
  let es := r.blocks.toList.map fun b => s!"({b.lo}, {b.hi}, {A64.isa.soLean b.so})"
  s!"/-- The blocks' regions and entry offsets, in table order. -/
def {pfx}Offs : List (Int × Int × Spike.Lib.A64.Flow.SO) := [
  " ++ ",\n  ".intercalate es ++ "]
"

/-- `renderOffs` of an AArch64 listing. -/
def offsA64 (asm pfx : String) : Except String String := do
  return renderOffs (← analyse A64.isa asm) pfx

end Scc.Cert.Blocks
