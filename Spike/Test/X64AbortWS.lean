import Spike.Lib.X64AbortWS

/-!
# The x86-64 overflow abort at depth, held back at depth 0

`Spike/Lib/X64AbortWS.lean`: a function's `.ovf` block at frames, the
source held back at depth 0 after `SegWS.lag`; the axioms of the pieces.
-/

namespace Spike.Test.X64AbortWS

open Spike.Lib.X64.Abort.Local

/-- info: 'Spike.Lib.X64.Abort.Local.seg_localWS_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms seg_localWS_lag

end Spike.Test.X64AbortWS
