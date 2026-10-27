import Spike.Lib.RtHeadroomX64

/-!
The runtime routines a stack-checked function calls fit in the headroom
(`Spike/Lib/RtHeadroomX64.lean`, `Spike/Lib/RtHeadroomA64.lean`; the two
ISAs' modules cannot be imported together, so this file tests the x86-64
one and `Spike.Test.RtHeadroomA64` the AArch64 one): their axioms, and the
depths of the runtime routines within `Tcb.headroom`.
-/

namespace Spike.Lib.RtHeadroomX64.Test

open Spike.Lib.RtHeadroomX64

/--
info: 'Spike.Lib.RtHeadroomX64.rt_call_fits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms rt_call_fits

/--
info: 'Spike.Lib.RtHeadroomX64.rt_tail_fits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms rt_tail_fits

#guard Scc.Cert.Code1X64.rtDepth.all (·.2 ≤ Scc.IR.Tcb.headroom)

end Spike.Lib.RtHeadroomX64.Test
