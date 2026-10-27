/-
**`hello1o`'s setup block has no call** (x86-64; the twin of
`Spike/Test/A64Hello1NoCall.lean`): no point of the lowering walk in
`rodata`'s body is a call's `let` (`tailsL`, decided), so its segment
`FnSpecC2` (`X64Hello1HS`'s open `hs`) is `fnSpecC2_ofCxLBMe` from its
contexts' `CxLB` alone.

- `hello1_rodata_noCall`: the decided check at `rodata`'s compiled block;
- `hello1_rodata_noCallT`: no call at any `TailAt2` point there.
-/
import Spike.Lib.LowerX64.FnSpecLaneBuf2
import Spike.Test.Hello1MainSrc
import Spike.Lib.Src.Walk2Facts

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Spike.Lib.LowerNode (compiled2 TailAt2)

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- **No call's `let` among the points of `rodata`'s body** in `hello1o`. -/
theorem hello1_rodata_noCall : ∀ (j : Nat) (d : Decl), (compiled2 P1)[j]? = some d → d.name = "rodata" →
    (tailsL d.body).all (fun t => !isCallLet t) = true := by
  have hc : ∀ d ∈ compiled2 P1, d.name = "rodata" → (tailsL d.body).all (fun t => !isCallLet t) = true := by
    decide
  exact fun j d hd hn => hc d (List.mem_of_getElem? hd) hn

/-- **No call at any `TailAt2` point of `rodata`'s compiled block.** -/
theorem hello1_rodata_noCallT {j : Nat} {d : Decl} (hd : (compiled2 P1)[j]? = some d) (hn : d.name = "rodata") :
    ∀ x g is a ts e, ¬ TailAt2 P1 j (.let_ x (.call g is a ts) e) := fun x g is a ts e ht =>
  noCall_of_tailsL (hello1_rodata_noCall j d hd hn) x g is a ts e (ht d hd)

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_rodata_noCall' depends on axioms: [propext] -/
#guard_msgs in #print axioms hello1_rodata_noCall

/-- info: 'Spike.Lib.LowerX64.hello1_rodata_noCallT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hello1_rodata_noCallT

end Spike.Lib.LowerX64
