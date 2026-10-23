import Spike.Lib.LowerA64.Correct

/-!
# The AArch64 compiler theorem's assembly: checks

`entry_at` at `ret0`'s layout from its placement check (`ret0P`): the loaded
pc is `_start`'s there, so the loaded thread is at `_start`'s node;
`startAllUW_gen`'s stack premises at `ret0`'s layouts (`stackM_rS0`,
`rS0_eq_lab`); and
`a64_lower_correct` and the closed theorems (`hgen_ofPlaceOK`,
`a64_scc_correctE{,_text}_closed`) rest on the standard axioms only.
-/

namespace Spike.Lib.LowerA64.Test

open Spike.Lib.A64.Rt (ret0P)
open SccCode (ret0Prog ret0Secs ret0Imms)
open Scc.Cert.PlaceOK.A64.Test (ret0_placeOK)

/-- At `ret0P` the loaded pc is `_start`'s. -/
theorem ret0_pc : (Scc.Sem.A64.threadAt Scc.Sem.Entry.linux ret0P.Λ.code.lo ret0Prog
    (Scc.Sem.loadSyms ret0P.Λ ret0Secs.rodata)).st.2 = ret0P.lab "_start" := by
  show Int64.ofNat 4194304 = (_root_.Executable.labels Spike.Lib.A64.Flow.Ret0.Mem.ret0Exe).label "_start"
  rw [Spike.Lib.A64.Flow.Ret0.Inst.ret0_labT]
  decide +kernel

/-- **`entry_at` at `ret0P`.** -/
example := entry_at (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms ret0_pc

/-- **`startAllUW_gen`'s stack premises at `ret0P`**: the first stack's words
stable in `scc_rt_start`'s three regions, and its range the take's at
`k0 = 0`. -/
example := stackM_rS0 ret0P (Spike.Lib.A64.Rt.RuntimeLayout.linux_ok_ofPlaceOK
    (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms)
example := rS0_eq_lab ret0P

/-- The same at the layout of `ret0`'s placement check. -/
example := stackM_rS0 (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms)
  (Spike.Lib.A64.Rt.RuntimeLayout.linux_ok_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms)

/- The first stack at `ret0P` is off the entry stack's region (`entryR`, the
64 KiB below `Entry.linux.sp`). -/
#guard (Spike.Lib.A64.Rt.rS0 ret0P).lo + (Spike.Lib.A64.Rt.rS0 ret0P).size ≤
  Scc.Sem.Entry.linux.sp - 65536

/--
info: 'Spike.Lib.LowerA64.a64_lower_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms a64_lower_correct

/-- **`entry_atE` at `ret0P` and the witness entry state** (the 64 KiB
stack at `2 ^ 32`): the loaded thread is at `_start`'s node there too. -/
example := entry_atE (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms
    (Spike.Lib.A64.Rt.RuntimeLayout.witness_ok_ofPlaceOK _ _)
  (Spike.Lib.A64.PhRec.hpc_ofPlaceOKE (Scc.Cert.PlaceOK.A64.atTables ret0_placeOK) ret0Imms _)

/--
info: 'Spike.Lib.LowerA64.a64_lower_correctE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms a64_lower_correctE

/--
info: 'Spike.Lib.LowerA64.a64_scc_correctE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms a64_scc_correctE

/--
info: 'Spike.Lib.LowerA64.a64_scc_correctE_text' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms a64_scc_correctE_text

/--
info: 'Spike.Lib.LowerA64.hgen_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgen_ofPlaceOK

/--
info: 'Spike.Lib.LowerA64.a64_scc_correctE_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms a64_scc_correctE_closed

/--
info: 'Spike.Lib.LowerA64.a64_scc_correctE_text_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms a64_scc_correctE_text_closed

/--
info: 'Spike.Lib.LowerA64.a64_scc_correctE_closedAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms a64_scc_correctE_closedAt

/--
info: 'Spike.Lib.LowerA64.a64_scc_correctE_text_closedAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms a64_scc_correctE_text_closedAt

end Spike.Lib.LowerA64.Test
