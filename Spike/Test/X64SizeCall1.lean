import Scc.Emit.X64Size
import Spike.Test.Cert.X64Call1Cert

/-!
# `Scc.Emit.X64.Size` against GNU `as` on the x86-64 `call1` certificate

The certificate's `prog` laid out at its `sizes` (GNU `as`'s lengths,
`Kraken.Promising.X64.sizedCells`): every cell's length is `sizeAt`'s, the
branch widths gas's at this layout (`checkCells` is empty). Untrusted.
-/

namespace Scc.Emit.X64.Size.TestCall1

open Scc.Emit.X64.Size

/-- The certificate's cells (`none` if the table does not fit). -/
def cells : Option (List (Directive × Nat)) :=
  Kraken.Promising.X64.sizedCells SccCertificate.prog SccCertificate.sizes

#guard cells.isSome
#guard (cells.map checkCells) == some []

end Scc.Emit.X64.Size.TestCall1
