/-
**The bare start's stack bounds and `main`'s call: the statements proved**
(x86-64): `StackBounds0Stmt` from `stackBounds0`
(`Spike/Lib/LowerX64/G1NoSetupBounds.lean`) and `MainCall0Stmt` from
`mainCallWSF_bareSeg` (`Spike/Lib/LowerX64/G1NoSetupCallB.lean`). The twin of
`Spike/Lib/LowerA64/G1NoSetupCallStmt.lean`.

- `th02_none`, `c0_start_none`: without a setup block the start's thread
  is `X64Consumer.c0`'s;
- `stackBounds0Stmt : StackBounds0Stmt`;
- `mainCall0 : MainCall0Stmt` (`mainCallWSF_bareSeg` at `Bounds0X`'s
  bounds, as `UserCallWSF`).
-/
import Spike.Lib.LowerX64.G1NoSetupDefs
import Spike.Lib.LowerX64.G1NoSetupCallB

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- **Without a setup block the start's thread is `c0`'s.** -/
theorem th02_none {p : Prog} (hs : Scc.Lower.setupOf p = none) (meW : TermRun.Word) :
    th02 p meW = { term := Spike.Lib.X64Consumer.c0.term, env := Spike.Lib.X64Consumer.c0.env } := by
  unfold th02; rw [hs]

/-- **Without a setup block the start control is `c0`.** -/
theorem c0_start_none {p : Prog} (hs : Scc.Lower.setupOf p = none) (meW : TermRun.Word) :
    (⟨(th02 p meW).term, (th02 p meW).env, none⟩ : Ctl) = Spike.Lib.X64Consumer.c0 := by
  rw [th02_none hs]; rfl

/-- **The bare start's bounds exist** (`stackBounds0`). -/
theorem stackBounds0Stmt : StackBounds0Stmt :=
  fun _ _ _ _ _ _ h hp hs hcfg Lr => stackBounds0 h hp hs hcfg Lr

/-- **`main`'s call at the bare start from `main`'s segment**
(`MainCall0Stmt`): at every choice of `Bounds0X`'s bounds,
`mainCallWSF_bareSeg` at the start control `c0` (`c0_start_none`), as
`UserCallWSF` (`userCallWSF_of_mainCallWSF`). -/
theorem mainCall0 : MainCall0Stmt := by
  intro cfg pcfg p sizes labelOffs Λ hp hm hcfg hs h E El Dt HM L D lM fM nM hB J _ v
  rw [c0_start_none hs]
  exact userCallWSF_of_mainCallWSF (mainCallWSF_bareSeg h hp hs hm hcfg hB J (HM J) v)

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.th02_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms th02_none

/-- info: 'Spike.Lib.LowerX64.c0_start_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms c0_start_none

/-- info: 'Spike.Lib.LowerX64.stackBounds0Stmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stackBounds0Stmt

/-- info: 'Spike.Lib.LowerX64.mainCall0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainCall0

end Spike.Lib.LowerX64
