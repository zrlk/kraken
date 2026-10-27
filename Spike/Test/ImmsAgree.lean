import Spike.Lib.LowerEnvImmAgree
import Spike.Lib.ImmsMonoA64

/-!
# From `imms1Of [d]` to `immsOf d` (AArch64)

An AArch64 `CorrectE` at the `Accepted1` table `imms1Of [d]` gives it at the
`Accepted0` table `immsOf d` for an `Accepted0` program, by
`imms1Of_sub_immsOf` (`Spike/Lib/LowerEnvImmAgree.lean`) and
`a64_correctE_imms_mono'` (`Spike/Lib/ImmsMonoA64.lean`): the step from a
theorem stated at `imms1Of` to one stated at `immsOf`. The lemmas' axioms.
-/

namespace Spike.Test.ImmsAgree

open CoreTerm Spike.Lib.LowerNode Spike.Lib.ImmsMono

example {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true) {n : Nat} {S : Scc.Sem.SrcSem} {Λ : Scc.Sem.Layout}
    {B : Scc.Sem.Budget} {asm : String}
    (h : Scc.Sem.A64.CorrectE n S { Λ with imms := Scc.Lower.imms1Of [d] } B asm) :
    Scc.Sem.A64.CorrectE n S { Λ with imms := immsOf d } B asm :=
  a64_correctE_imms_mono' h fun _ _ _ _ => imms1Of_sub_immsOf hd

/--
info: 'Spike.Lib.LowerNode.imms1Of_sub_immsOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms imms1Of_sub_immsOf

/--
info: 'Spike.Lib.ImmsMono.a64_correctE_imms_mono'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms a64_correctE_imms_mono'

end Spike.Test.ImmsAgree
