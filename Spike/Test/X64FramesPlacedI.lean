import Spike.Lib.X64SFactsAtS

/-!
# The frames placed in slots or immediates, and `SFactsS` at depth (x86-64)

`Spike/Lib/X64FramesPlacedI.lean`, `Spike/Lib/X64SFactsAtS.lean`: the
axioms of the pieces.
-/

namespace Spike.Test.X64FramesPlacedI

/-- info: 'Spike.Lib.X64ConsumerS.InSlotsI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.InSlotsI

/-- info: 'Spike.Lib.X64ConsumerS.FramesPlacedInI.nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.FramesPlacedInI.nil

/-- info: 'Spike.Lib.X64ConsumerS.FramesPlacedInI.toFramesPlaced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.FramesPlacedInI.toFramesPlaced

/-- info: 'Spike.Lib.X64ConsumerS.FramesPlacedInI.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.FramesPlacedInI.mono

/-- info: 'Spike.Lib.X64ConsumerS.wordPlaceRep_of_eqI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.wordPlaceRep_of_eqI

/-- info: 'Spike.Lib.X64ConsumerS.FramesPlacedInI.of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.FramesPlacedInI.of_eq

/-- info: 'Spike.Lib.X64ConsumerS.FramesPlacedInI.push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.FramesPlacedInI.push

/-- info: 'Spike.Lib.X64ConsumerS.framesPlaced_callTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.framesPlaced_callTo

/-- info: 'Spike.Lib.X64ConsumerS.slotPlacedI_of_srep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.slotPlacedI_of_srep

/-- info: 'Spike.Lib.X64ConsumerS.SFactsS.ofSFactsAtO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.SFactsS.ofSFactsAtO

/-- info: 'Spike.Lib.X64ConsumerS.SFactsS.ofSFactsAtI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.SFactsS.ofSFactsAtI

/-- info: 'Spike.Lib.X64ConsumerS.FramesPlacedInI.of_cKept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.FramesPlacedInI.of_cKept

end Spike.Test.X64FramesPlacedI
