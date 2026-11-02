/-
**hello's clone facts from `H1StmtHF`, on x86-64** (the twin of `Spike/Lib/A64HelloHClWF.lean`):
`X64HelloHClW.hClH_of` reads `h1 : H1StmtH …` only through its clone component (`h1`'s level never at the
clone), which `H1StmtHF … fr` has too. `H1StmtHF.toH` forgets the landing: an `H1StmtHF` is an `H1StmtH` with
no landing (`Rd := fun _ _ _ _ _ => False`), so `hClH_of` takes `h1.toH` directly.

- `H1StmtHF.toH`: the conversion.

## Differences from the AArch64 version

- Over `X64HelloPreA`'s `H1StmtH`, `H1StmtHF` (x86-64's `isa`).
- A64's `cloneInvH_of_I3F` and `hpostH_ofF` are dead and not twinned.
-/
import Spike.Lib.X64HelloHClW
import Spike.Lib.X64HelloWcInv3F

namespace Spike.Lib.X64HelloHClW

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (Arena FragS)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64HelloPreA (H1StmtH H1StmtHF)

variable {K : State → State → Prop} {L0 : Lbl} {L : RuntimeLayout}
  {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {ar : Arena}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {fr : List TermRun.Frame}

/-- **An `H1StmtHF` is an `H1StmtH` with no landing**: the segment and the clone facts kept. -/
theorem _root_.Spike.Lib.X64HelloPreA.H1StmtHF.toH (h1 : H1StmtHF W1 K ar L0 ms1 L Rd inv1 fr) :
    H1StmtH W1 K ar L0 ms1 L (fun _ _ _ _ _ => False) inv1 :=
  fun l b n hl hb => ⟨(h1 l b n hl hb).1, fun _ _ h => h.elim, (h1 l b n hl hb).2.2⟩

end Spike.Lib.X64HelloHClW

/-- info: 'Spike.Lib.X64HelloPreA.H1StmtHF.toH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.H1StmtHF.toH
