/-
**`x64_scc_correctE_closedAt1_wn` states `x64_scc_correctE_closedAt1`**
(x86-64): the compiler theorem proved along the frame `WordsNone ∧ rtF`
(`Spike/Lib/LowerX64/Correct1WN.lean`) has the released theorem's type,
`WordsNone` appearing only inside its proof. A changed statement fails the
`rfl` below. The frame bound `hfr` is a premise of both.
-/
import Spike.Lib.LowerX64.Correct1WN

namespace Spike.Test.X64Correct1WN

/-- The two closed theorems have the same type. -/
example : type_of% @Spike.Lib.LowerX64.x64_scc_correctE_closedAt1 =
    type_of% @Spike.Lib.LowerX64.x64_scc_correctE_closedAt1_wn := rfl

/-- And each proves the other's statement. -/
example : type_of% @Spike.Lib.LowerX64.x64_scc_correctE_closedAt1 :=
  @Spike.Lib.LowerX64.x64_scc_correctE_closedAt1_wn

end Spike.Test.X64Correct1WN
