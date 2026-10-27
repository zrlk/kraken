/-
**A segment from an empty precondition** (any ISA): `SegW.of_not`, the
segment whose invariant is its empty precondition. A call of `print` on an
empty slice uses it for the unreachable system call
(`Spike/Lib/A64PrintEmpty.lean` and its x86-64 twin).
-/
import Spike.Lib.SegW

namespace Spike.Lib

open Kraken.Promising CoreLang

/-- **A segment from an empty precondition.** -/
theorem SegW.of_not {I : ISA} {W : Frag I} {K : I.State → I.State → Prop} {p : CoreTerm.Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I} {P Q : Frag I} (hP : ∀ s c, ¬ P s c) :
    SegW W K p lbl ms P Q :=
  ⟨P, fun _ _ h => h, fun s c h => (hP s c h).elim, fun s c h => (hP s c h).elim⟩

end Spike.Lib

/-- info: 'Spike.Lib.SegW.of_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.SegW.of_not
