/-
**`a64_scc_correctE_closedAt1_wn` states `a64_scc_correctE_closedAt1`**
(AArch64): the compiler theorem proved along the frame `WordsNone ∧ rtF`
(`Spike/Lib/LowerA64/Correct1WN.lean`) has the released theorem's type,
`WordsNone` appearing only inside its proof. A changed statement fails the
`rfl` below.
-/
import Spike.Lib.LowerA64.Correct1WN

namespace Spike.Test.A64Correct1WN

/-- The two closed theorems have the same type. -/
example : type_of% @Spike.Lib.LowerA64.a64_scc_correctE_closedAt1 =
    type_of% @Spike.Lib.LowerA64.a64_scc_correctE_closedAt1_wn := rfl

/-- And each proves the other's statement. -/
example : type_of% @Spike.Lib.LowerA64.a64_scc_correctE_closedAt1 :=
  @Spike.Lib.LowerA64.a64_scc_correctE_closedAt1_wn

end Spike.Test.A64Correct1WN
