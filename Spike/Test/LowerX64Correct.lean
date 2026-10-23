import Spike.Lib.LowerX64.Correct

/-!
# The x86-64 compiler theorem's assembly: checks

`entry_atX` at `ret0`'s layout from its placement check (`ret0P`): the
loaded pc is `_start`'s there, so the loaded thread is at `_start`'s node;
and `x64_lower_correct` and the closed theorems (`hgen_ofPlaceOK`,
`x64_scc_correctE{,_text}_closed`) rest on the standard axioms only.
-/

namespace Spike.Lib.LowerX64.Test

open Scc.Cert.PlaceOK.X64 (atTables)

open Spike.Lib.X64.Rt (ret0P)
open SccCode (ret0Imms)
open Scc.Cert.PlaceOK.X64.Test (ret0_placeOK)

/-- **`entry_atX` at `ret0P`**: there the loaded pc is `_start`'s. -/
example := entry_atX (atTables ret0_placeOK) ret0Imms (by
  show Int64.ofNat 4194304 = (_root_.Executable.labels Spike.Lib.X64.Flow.Ret0.Mem.ret0Exe).label "_start"
  rw [Spike.Lib.X64.Flow.Ret0.Inst.ret0_labT]
  decide +kernel)

/--
info: 'Spike.Lib.LowerX64.x64_lower_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms x64_lower_correct

/-- **`startAllUW_gen`'s `hrS` at `ret0P`**: the first stack's range is the
take's at `k0 = 0`. -/
example := rS0_eq_lab ret0P

/-- **`entry_atXE` at `ret0P` and the witness entry state** (the 64 KiB
stack at `2 ^ 32`): the loaded thread is at `_start`'s node there too. -/
example := entry_atXE (atTables ret0_placeOK) ret0Imms (Spike.Lib.X64.Rt.RuntimeLayout.witness_ok_ofPlaceOK _ _)
  (Spike.Lib.X64.PhRec.hpc_ofPlaceOKE (atTables ret0_placeOK) ret0Imms _)

/--
info: 'Spike.Lib.LowerX64.x64_lower_correctE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms x64_lower_correctE

/--
info: 'Spike.Lib.LowerX64.x64_scc_correctE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms x64_scc_correctE

/--
info: 'Spike.Lib.LowerX64.x64_scc_correctE_text' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms x64_scc_correctE_text

/--
info: 'Spike.Lib.LowerX64.hgen_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgen_ofPlaceOK

/--
info: 'Spike.Lib.LowerX64.x64_scc_correctE_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms x64_scc_correctE_closed

/--
info: 'Spike.Lib.LowerX64.x64_scc_correctE_text_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms x64_scc_correctE_text_closed

/--
info: 'Spike.Lib.LowerX64.x64_scc_correctE_closedAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms x64_scc_correctE_closedAt

/--
info: 'Spike.Lib.LowerX64.x64_scc_correctE_text_closedAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms x64_scc_correctE_text_closedAt

end Spike.Lib.LowerX64.Test
