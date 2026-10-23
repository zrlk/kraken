/-
**A lowered body's blocks in their phase** (x86-64): one Boolean check
over the body's blocks (`bodyBlks`), each at its byte offset after the
body's label, that every block passes the phase check `blkPh`.

- `bodyPhOk`: the check, `bodyBlks.all blkPh`;
- `blkPh_of_inBody`: its soundness at a block: every block `InBody` at `pc`
  passes `blkPh` at `pc` (so `blkPh_sound` applies to it).

Standalone: not yet a part of `fnCodeOk` (A9). `ra` is the segment's ghost
return address: the `ret` block's target check (`ph ra` the body's phase,
or `dead ra`) is the consumer's.

Where x86-64 differs from AArch64: offsets are in bytes, and the blocks
depend on the cells (`bodyBlks` reads the sizes off them).
-/
import Spike.Lib.LowerX64.Checks
import Spike.Lib.X64SegInst

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib.X64Consumer (blkPh)

/-- **Every block of a lowered body passes `blkPh`** at its byte offset
after the body's label `l` (at `lab l`). -/
def bodyPhOk (okPc : Nat → Bool) (ph : Nat → Nat) (dead : Nat → Bool) (lab : String → Int64)
    (cells : List (Directive × Nat)) (fr : Scc.Emit.X64.Frame) (l : String)
    (is : List Scc.IR.Inst) (ws : List Scc.IR.Operand) (ra : Int64) : Bool :=
  (bodyBlks cells fr l 0 is ws).all fun x => blkPh okPc ph dead lab (lab l + Int64.ofNat x.1) ra x.2

/-- **`bodyPhOk` is sound**: a block of the body (`InBody`) at `pc` passes
`blkPh` at `pc`. -/
theorem blkPh_of_inBody {okPc : Nat → Bool} {ph : Nat → Nat} {dead : Nat → Bool} {lab : String → Int64}
    {cells : List (Directive × Nat)} {fr : Scc.Emit.X64.Frame} {l : String}
    {is : List Scc.IR.Inst} {ws : List Scc.IR.Operand} {ra pc : Int64} {blk : List (Directive × Nat)}
    (hb : InBody lab cells fr l is ws pc blk) (h : bodyPhOk okPc ph dead lab cells fr l is ws ra = true) :
    blkPh okPc ph dead lab pc ra blk = true := by
  obtain ⟨j, rfl, hj⟩ := hb
  exact List.all_eq_true.mp h _ hj

end Spike.Lib.LowerX64
