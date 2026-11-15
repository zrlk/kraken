import Scc.Emit.X64
import Scc.Emit.GranuleX64

/-!
# The post-emission pipeline, x86-64 (untrusted)

`postEmit` takes the emitter's items (`Scc.Emit.X64.emitItemsMaps`) to the
items scc prints, together with the table data the certificate's data
sections are built from (one list: what is rendered is what `Secs` reads).
Its stages, in order:

1. (to come, R3) the collector's tables in `.rodata`, after `scc_stackmap`;
   until then the table data is empty;
2. the granule pass (`Scc.Emit.Granule.granuleX64`), which rewrites only the
   text and passes every later item through unchanged.

It fails closed: an error of any stage is scc's error. `emitFinal` is the
text scc prints (`Scc.Cert.X64.compile`, `Scc.Lower.X64.Emitted.listing`).
The pre-pass items stay the lowering's (`Scc.Lower.X64.lowerAll`, the
certificate's `out`); a certificate relates the two by
`Scc.Cert.Granule.X64.check`.
-/

namespace Scc.Emit.X64

/-- **The post-emission pipeline**: the items scc prints and the table data
(`.rodata`, after the stack map) of the program `p` with the emitter's items
`items` and safepoints `sps`. -/
def postEmit (p : IR.Program) (items : List Item) (_sps : List (String × List Int × List Int)) :
    Except String (List Item × List Kraken.DataImage.Item) := do
  let final ← Scc.Emit.Granule.granuleX64 p items
  pure (final, [])

/-- **The assembler text scc prints** for the program `p`: the emitter's
items through `postEmit`, rendered. -/
def emitFinal (p : IR.Program) : Except String String := do
  let (items, sps) ← emitItemsMaps p
  render (← postEmit p items sps).1

end Scc.Emit.X64
