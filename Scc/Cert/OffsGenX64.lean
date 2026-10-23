import Scc.Cert.Blocks

/-!
# The offset rows of an x64 listing

The x64 twin of `Scc/Cert/OffsGen.lean`: the text of a program's block
offsets (`Scc.Cert.Rt.X64.ofGrps`'s second argument,
`Scc/Cert/Rt/OffsX64.lean`): per block of the analysis (`Blocks.analyse`,
with the listing's instruction sizes), in block order, which is the block
table's (`Blocks.renderCode`), its region and entry offsets. The placement
check (`PlaceOK.X64`, A5) checks them; nothing here is trusted.
-/

namespace Scc.Cert.Blocks

/-- **The offsets of an x64 listing's blocks**: the definition
`{pfx}Offs : List (Int × Int × SO)`, one `(lo, hi, o)` per block. -/
def renderOffsX64 (r : Result) (pfx : String) : String :=
  let es := r.blocks.toList.map fun b => s!"({b.lo}, {b.hi}, {X64.isa.soLean b.so})"
  s!"/-- The blocks' regions and entry offsets, in table order. -/
def {pfx}Offs : List (Int × Int × Spike.Lib.X64.SO) := [
  " ++ ",\n  ".intercalate es ++ "]
"

/-- `renderOffsX64` of an x64 listing with its instruction sizes (one per
instruction line in text order). -/
def offsX64 (asm : String) (sizes : List Nat) (pfx : String) : Except String String := do
  return renderOffsX64 (← analyse X64.isa asm (some sizes)) pfx

end Scc.Cert.Blocks
