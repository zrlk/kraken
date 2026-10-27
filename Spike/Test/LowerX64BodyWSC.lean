import Spike.Lib.LowerX64.BodyWSC

/-!
# An x86-64 body's construct blocks with calls at depth

`Spike/Lib/LowerX64/BodyWSC.lean`: `fnC_segS`' `hWb`/`hWs` at the code
predicate with calls from the call-free `blkW_bodyS1`; the axioms of the
pieces.
-/

namespace Spike.Test.LowerX64BodyWSC

open Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.cd1_of_subCdC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cd1_of_subCdC

/-- info: 'Spike.Lib.LowerX64.hWbS_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hWbS_of

/-- info: 'Spike.Lib.LowerX64.hWsS_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hWsS_of

end Spike.Test.LowerX64BodyWSC
