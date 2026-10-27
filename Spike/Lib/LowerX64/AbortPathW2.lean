/-
**The abort path from the per-pair facts** (x86-64): `AbortPathS` at an
invariant every pair of which has `W2` (`Spike/Lib/LowerX64/SFactsA2.lean`):
the abort sites from `W2.abort`, the phase kept from `W2.ab` (`AbSt`).

- `abortPathS_of_W2`.
-/
import Spike.Lib.LowerX64.SFactsA2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA

/-- **The abort path at an invariant inside `W2`** (at the arena `ar`'s
cells and counter): each field of `AbortPathS` is a field of `W2` at the
pair. -/
theorem abortPathS_of_W2 {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS}
    {Dt Ab : State → Prop} {I : InvS}
    (hI : ∀ lbl lsize s c fs, I lbl lsize s c fs → W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) :
    AbortPathS μ I Ab ar.cells ar.ctr where
  at_ lbl lsize s c fs h k a hk hpc := (hI lbl lsize s c fs h).abort k a hk hpc
  instr lbl lsize s c fs h := (hI lbl lsize s c fs h).ab.abInstr
  sys lbl lsize s c fs h := (hI lbl lsize s c fs h).ab.abSys
  take lbl lsize s c fs h := (hI lbl lsize s c fs h).ab.abTake

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.abortPathS_of_W2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.abortPathS_of_W2
