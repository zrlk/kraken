/-
**The heap abort path inside `SFactsA`** (`Spike/Lib/X64StubHA.lean`): a
frame run from an allocation is empty, and `stubHW_sfactsA` and its node
lemmas rest on the standard axioms only.
-/
import Spike.Lib.X64StubHA

namespace Spike.Lib.X64.StubW.Test

open CoreLang CoreTerm

/-- A frame run from `let x = newBuf a τ in e` stays put, at any frames. -/
example {p : Prog} {x : String} {a : CoreTerm.At} {τ : Ty} {e : Expr} {env : TermRun.Env} {c' : Ctl}
    {fs fs' : List TermRun.Frame} (h : Spike.Lib.FrameRun p (⟨.let_ x (.newBuf a τ) e, env, none⟩, fs) (c', fs')) :
    c' = ⟨.let_ x (.newBuf a τ) e, env, none⟩ ∧ fs' = fs :=
  run_eq ⟨x, a, τ, e, rfl⟩ h

/-- info: 'Spike.Lib.X64.StubW.stubHW_sfactsA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stubHW_sfactsA

/-- info: 'Spike.Lib.X64.StubW.blkW_heapA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blkW_heapA

/-- info: 'Spike.Lib.X64.StubW.sfactsA_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sfactsA_sys

end Spike.Lib.X64.StubW.Test
