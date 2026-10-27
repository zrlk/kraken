import Spike.Lib.LowerA64.AbortCallS

/-!
# A function's overflow abort at depth, held back at depth 0 (AArch64)

`Spike/Lib/LowerA64/AbortCallS.lean`: the axioms of the pieces.
-/

namespace Spike.Test.LowerA64AbortCallS

open Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.stub_svc_noK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stub_svc_noK

/-- info: 'Spike.Lib.LowerA64.hab_ofS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hab_ofS

end Spike.Test.LowerA64AbortCallS
