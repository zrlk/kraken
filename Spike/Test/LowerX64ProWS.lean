import Spike.Lib.LowerX64.ProWS

/-!
# A code block's prologue inside the body's fragment at depth (x86-64)

`Spike/Lib/LowerX64/ProWS.lean`: the prologue obligation of `CalleePre`'s
`hpro` inside `BodyWS0` at the frames, from the prologue's code and phase
facts (with its parameter spill), and the prologue with saved registers
inside the consumer's facts (`Spike/Lib/LowerX64/UserW.lean`); the axioms
of the pieces.
-/

namespace Spike.Test.LowerX64ProWS

/-- info: 'Spike.Lib.LowerX64.proW_sfactsP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.proW_sfactsP

/-- info: 'Spike.Lib.LowerX64.spillsOk_of_hps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.spillsOk_of_hps

/-- info: 'Spike.Lib.LowerX64.proW_bodyS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.proW_bodyS

end Spike.Test.LowerX64ProWS
