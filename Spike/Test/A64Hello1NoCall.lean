/-
**`hello1o`'s setup block has no call** (AArch64): no point of the
lowering walk in `rodata`'s body is a call's `let` (`tailsL`, decided), so
its segment `FnSpecC2` (`A64Hello1HS`'s open `hs`) is `fnSpecC2_ofLaneBuf`
from its contexts' lane stores and buffers alone (`LaneC` by `laneC_w2E`,
`NewBufC` by `newBufC_of` with `allocW2_w2Full`).

- `hello1_rodata_noCall`: the decided check at `rodata`'s compiled block;
- `hello1_rodata_noCallT`: no call at any `TailAt2` point there.
-/
import Spike.Lib.LowerA64.FnSpecLaneBuf2
import Spike.Test.Hello1MainSrc
import Spike.Lib.Src.Walk2Facts

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Spike.Lib.LowerNode (compiled2 TailAt2)

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- **No call's `let` among the points of `rodata`'s body** in `hello1o`. -/
theorem hello1_rodata_noCall : ∀ (j : Nat) (d : Decl), (compiled2 P1A)[j]? = some d → d.name = "rodata" →
    (tailsL d.body).all (fun t => !isCallLet t) = true := by
  have hc : ∀ d ∈ compiled2 P1A, d.name = "rodata" → (tailsL d.body).all (fun t => !isCallLet t) = true := by
    decide
  exact fun j d hd hn => hc d (List.mem_of_getElem? hd) hn

/-- **No call at any `TailAt2` point of `rodata`'s compiled block.** -/
theorem hello1_rodata_noCallT {j : Nat} {d : Decl} (hd : (compiled2 P1A)[j]? = some d) (hn : d.name = "rodata") :
    ∀ x g is a ts e, ¬ TailAt2 P1A j (.let_ x (.call g is a ts) e) := fun x g is a ts e ht =>
  noCall_of_tailsL (hello1_rodata_noCall j d hd hn) x g is a ts e (ht d hd)

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_rodata_noCall' depends on axioms: [propext] -/
#guard_msgs in #print axioms hello1_rodata_noCall

/-- info: 'Spike.Lib.LowerA64.hello1_rodata_noCallT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hello1_rodata_noCallT

end Spike.Lib.LowerA64
