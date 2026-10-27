/-
**Checks of `Spike/Lib/X64Hello1WImp.lean`**: the axioms of the
two-obligation lemmas (Lean's only).
-/
import Spike.Lib.X64Hello1WImp

namespace Spike.Test.X64Hello1WImp

open Spike.Lib.X64

/--
info: 'Spike.Lib.X64.Flow.Hello1.MainPreW.imp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Flow.Hello1.MainPreW.imp

/--
info: 'Spike.Lib.X64.Flow.Hello1.MainPostW.imp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Flow.Hello1.MainPostW.imp

/--
info: 'Spike.Lib.X64.Flow.Hello1.MainPostSW.imp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Flow.Hello1.MainPostSW.imp

end Spike.Test.X64Hello1WImp
