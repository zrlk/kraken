/-
**`wc_main` through `print_callAbW`** (`Spike/Lib/A64Hello1BodyAb.lean`): the
body and the whole of `wc_main` with `print`'s obligations at `PrintAb`'s
nodes rest on the standard axioms only.
-/
import Spike.Lib.A64Hello1BodyAb

namespace Spike.Lib.A64.Flow.Hello1.Test

open Spike.Lib.A64.Flow.Hello1

/-- info: 'Spike.Lib.A64.Flow.Hello1.hello1_wc_bodyAb_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hello1_wc_bodyAb_segW

/-- info: 'Spike.Lib.A64.Flow.Hello1.hello1_wcAb_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hello1_wcAb_segW

end Spike.Lib.A64.Flow.Hello1.Test
