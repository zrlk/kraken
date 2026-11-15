/-
**The bare start's bounds and `main`'s call: the statements proved**
(AArch64): `StackBounds0Stmt` and `MainCall0Stmt`
(`Spike/Lib/LowerA64/G1NoSetupDefs.lean`) for every `Accepted2` program
without a setup block.

- `userCallWSF_of_mainCallWSF`: the entry `uN0` at the ghost `c0` is
  `uNM` at the arguments `fun c _ => c = c0`, so `MainCallWSF` there is
  `UserCallWSF`;
- `th02_none`, `c0_start_none`: without a setup block the program's start
  control is the source's start `c0`;
- `stackBounds0`: `StackBounds0Stmt` (`stackBounds0A`);
- `mainCall0`: `MainCall0Stmt` (`mainCallWSF_bareSeg` at `Bounds0A`'s
  bounds).
-/
import Spike.Lib.LowerA64.G1NoSetupDefs
import Spike.Lib.LowerA64.G1NoSetupCall

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (WcG CallerCells)
open Spike.Lib.A64.Rt (MainCallWSF UserCallWSF)

/-- **`MainCallWSF` at the arguments `c = c0` is `UserCallWSF` at the ghost
`c0`**: at a ghost with `g.c0 = c0`, `uN0`'s invariant is `uNM`'s at
`fun c _ => c = c0`. -/
theorem userCallWSF_of_mainCallWSF {W : FragS isaLSE2} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    {ra : BitVec 64} {c0 : Ctl} {tp : UInt64}
    (h : MainCallWSF W K p lbl ms exe endPc R F fn Z D ZU (fun c _ => c = c0) Post ra tp) :
    UserCallWSF W K p lbl ms exe endPc R F fn Z D ZU Post ra c0 tp := by
  intro F' hR hal hF hFF g hra hc0 htp
  subst hc0
  exact h F' hR hal hF hFF g hra htp

/-- **The start's thread without a setup block** is the source's start
`c0`'s. -/
theorem th02_none {p : Prog} (hs : Scc.Lower.setupOf p = none) (meW : TermRun.Word) :
    th02 p meW = { term := Spike.Lib.A64Consumer.c0.term, env := Spike.Lib.A64Consumer.c0.env } := by
  unfold th02; rw [hs]

/-- **The start control without a setup block is `c0`.** -/
theorem c0_start_none {p : Prog} (hs : Scc.Lower.setupOf p = none) (meW : TermRun.Word) :
    (⟨(th02 p meW).term, (th02 p meW).env, none⟩ : Ctl) = Spike.Lib.A64Consumer.c0 := by
  rw [th02_none hs]; rfl

/-- **The bare start's bounds exist** (`StackBounds0Stmt`). -/
theorem stackBounds0 : StackBounds0Stmt :=
  fun _ _ _ _ h hp hs hcfg Lr => stackBounds0A h hp hs hcfg Lr

/-- **`main`'s call at the bare start from `main`'s segment**
(`MainCall0Stmt`): at every choice of `Bounds0A`'s bounds,
`mainCallWSF_bareSeg` at the start control `c0` (`c0_start_none`), as
`UserCallWSF` (`userCallWSF_of_mainCallWSF`). -/
theorem mainCall0 : MainCall0Stmt := by
  intro cfg pcfg p Λ hp hm hcfg hs h E El Dt HM L D lM fM nM hB J _ v
  obtain ⟨hrM, -, -, hnM, hrowM, hL0, hLm, hL8, hD0, hD8, hLZ, -, -, -⟩ := hB
  rw [c0_start_none hs]
  exact userCallWSF_of_mainCallWSF
    (mainCallWSF_bareSeg h hp hs hm hcfg hrM hnM hrowM hL0 hLm hL8 hD0 hD8 hLZ J (HM J) v)

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.


/-- info: 'Spike.Lib.LowerA64.userCallWSF_of_mainCallWSF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.userCallWSF_of_mainCallWSF

/-- info: 'Spike.Lib.LowerA64.th02_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.th02_none

/-- info: 'Spike.Lib.LowerA64.c0_start_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.c0_start_none

/-- info: 'Spike.Lib.LowerA64.stackBounds0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.stackBounds0

/-- info: 'Spike.Lib.LowerA64.mainCall0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainCall0
