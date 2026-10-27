/-
**The landings' contexts' aborts gathered** (x86-64; the twin of `GA` in
`Spike/Lib/LowerA64/H1RestA.lean`): `H1OpenXW`'s aborts' fragment `Ab₀`
(`Spike/Lib/LowerX64/H1InLandW.lean`) taken as the aborts of some context
`CxOk` carries, so that `H1OpenXW.hAb` holds by construction.

- `GX`: the aborts of some context `CxOk` carries;
- `gx_hAb`: each context's aborts inside `GX` (`H1OpenXW.hAb`'s shape).
-/
import Spike.Lib.LowerX64.H1InLandW

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib

/-- **The aborts of some context** `CxOk` carries (`H1OpenXW`'s `Ab₀`
gathered). -/
def GX (CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
    (Ctl → Prop) → FragS isa → Prop) : FragS isa := fun s c fs' =>
  ∃ (j : Nat) (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64)
    (G0 : Ctl → Prop) (Ab : FragS isa), CxOk j R F fs fp ra tp G0 Ab ∧ Ab s c fs'

/-- **Each context's aborts inside `GX`** (`H1OpenXW.hAb` at `Ab₀ := GX CxOk`). -/
theorem gx_hAb {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 →
    UInt64 → (Ctl → Prop) → FragS isa → Prop} :
    ∀ j R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → ∀ s c fs', Ab s c fs' → GX CxOk s c fs' :=
  fun j R F fs fp ra tp G0 Ab hc _ _ _ hA => ⟨j, R, F, fs, fp, ra, tp, G0, Ab, hc, hA⟩

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.gx_hAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.gx_hAb
