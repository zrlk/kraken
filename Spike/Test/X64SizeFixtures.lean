import Scc.Emit.X64Size
import Spike.Lib.X64HelloCode
import Spike.Lib.X64WakeCode
import Spike.Lib.X64Hello1Code
import Spike.Lib.X64Ret0Code

/-!
# `Scc.Emit.X64.Size` against GNU `as` on the x86-64 code fixtures

For `hello`, `wake`, `hello1` and `ret0` (`Spike/Lib/X64*Code.lean`), the
code cells the canonical loader lays out at GNU `as`'s size table: every
cell's length is `sizeAt`'s, the branch widths gas's at this layout
(`checkCells` is empty). The `call1` and `frame0` certificates are checked in
`X64SizeCall1.lean` and `X64SizeFrame0.lean` (their names clash). Untrusted.
-/

namespace Scc.Emit.X64.Size.TestFixtures

open Scc.Emit.X64.Size SccCode

#guard checkCells helloCells == []
#guard checkCells wakeCells == []
#guard checkCells hello1Cells == []
#guard checkCells ret0Cells == []

-- Not vacuous: one byte more on every cell is a mismatch at every cell.
#guard (checkCells (helloCells.map fun (d, z) => (d, z + 1))).length == helloCells.length

end Scc.Emit.X64.Size.TestFixtures
