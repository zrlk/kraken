/-
**The `%fs` base kept across an x86-64 segment** (`Spike/Lib/X64KeepTP.lean`):
a register write leaves `fsBase` alone, and the axioms of the operation, step
and segment lemmas.
-/
import Spike.Lib.X64KeepTP

open Kraken.Promising.X64 Spike.Lib.X64.KeepTP

/-- Writing `%rax` leaves the `%fs` base alone. -/
example (r : Reg64s) (v : BitVec 64) : (r.set64 .rax v).fsBase = r.fsBase :=
  set64_tp r .rax v

/--
info: 'Spike.Lib.X64.KeepTP.all_interp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms all_interp

/--
info: 'Spike.Lib.X64.KeepTP.all_avx' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms all_avx

/--
info: 'Spike.Lib.X64.KeepTP.exec_tp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms exec_tp

/--
info: 'Spike.Lib.X64.KeepTP.out_tp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms out_tp

/--
info: 'Spike.Lib.X64.KeepTP.SegW.keepTP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms SegW.keepTP
