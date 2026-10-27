import Spike.Lib.LowerX64.LowerProgC2X

/-!
# `lowerAll`'s IR on an `Accepted2` program (x86-64)

`lowerAll_accepted2_x64` uses no axiom beyond Lean's.
-/

namespace Spike.Test.LowerProgC2X

/-- info: 'Spike.Lib.LowerNode.lowerAll_accepted2_x64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerNode.lowerAll_accepted2_x64

end Spike.Test.LowerProgC2X
