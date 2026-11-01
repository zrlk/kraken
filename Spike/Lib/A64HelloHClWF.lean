/-
**hello's clone facts from `H1StmtHF`** (AArch64): `A64HelloHClW`'s
`cloneInvH_of_I3`, `hpostH_of`, `hClH_of` read `h1 : H1StmtH …` only through its clone component (`h1`'s
level never at the clone), which `H1StmtHF … fr` has too. `H1StmtHF.toH` forgets the landing: an `H1StmtHF`
is an `H1StmtH` with no landing (`Rd := fun _ _ _ _ _ => False`), so the three apply to it unchanged.

- `H1StmtHF.toH`: the conversion.
- `cloneInvH_of_I3F`, `hpostH_ofF`: `cloneInvH_of_I3`, `hpostH_of` from `H1StmtHF`; `hClH_of` takes
  `h1.toH` directly.
-/
import Spike.Lib.A64HelloHClW
import Spike.Lib.A64HelloWcInv3F

namespace Spike.Lib.HelloHClW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks)
open Scc.Sem.A64 (abi pcOf)
open Spike.Lib (Arena FragS)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (NodesA I3)
open Spike.Lib.A64ConsumerS (TakeSiteS OwnS)
open Spike.Lib.HelloPreA (clonePcH ClonePostH CloneInvH H0StmtH H1StmtH H1StmtHF H2StmtH)
open Spike.Lib.HelloSrc (helloSrc)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : OwnS}
  {ab : Option (State → Prop)} {Cl : State → Prop}
  {W0 : FragS isaLSE2} {K : State → State → Prop} {L0 : Lbl} {ls0 : Lsize}
  {ms0 : List TermRun.Frame → MemSide isaLSE2} {L : RuntimeLayout} {endPc : Int64} {Start inv0 : FragS isaLSE2}
  {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {ar : Arena}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {fr : List TermRun.Frame}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
  {Box : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop}
  {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}

/-- **An `H1StmtHF` is an `H1StmtH` with no landing**: the segment and the clone facts kept. -/
theorem _root_.Spike.Lib.HelloPreA.H1StmtHF.toH (h1 : H1StmtHF W1 K ar L0 ms1 L Rd inv1 fr) :
    H1StmtH W1 K ar L0 ms1 L (fun _ _ _ _ _ => False) inv1 :=
  fun l b n hl hb => ⟨(h1 l b n hl hb).1, fun _ _ h => h.elim, (h1 l b n hl hb).2.2⟩

/-- **`CloneInvH` at an `I3` state at a `clone` call, from `H1StmtHF`** (`cloneInvH_of_I3`). -/
theorem cloneInvH_of_I3F (hN : NodesA Λ helloSrc μ rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) ab Cl)
    (hT : TakeSiteS helloSrc μ (I3 ar L0 ls0 inv0 inv1 inv2)) (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (h0 : H0StmtH W0 K L0 ms0 L Start inv0) (h1 : H1StmtHF W1 K ar L0 ms1 L Rd inv1 fr)
    (h2 : H2StmtH W2 K ar L0 ms2 L endPc Box inv2)
    {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I3 ar L0 ls0 inv0 inv1 inv2 lbl lsize s c fs) (hs : abi.atSys s = true) {st tl : Nat}
    (hcall : Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) :
    CloneInvH L endPc lbl s c fs :=
  cloneInvH_of_I3 hN hT hCl h0 h1.toH h2 hI hs hcall

/-- **Main's state at the clone is `ClonePostH`'s, from `H1StmtHF`** (`hpostH_of`). -/
theorem hpostH_ofF (hN : NodesA Λ helloSrc μ rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) ab Cl)
    (hT : TakeSiteS helloSrc μ (I3 ar L0 ls0 inv0 inv1 inv2)) (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (h0 : H0StmtH W0 K L0 ms0 L Start inv0) (h1 : H1StmtHF W1 K ar L0 ms1 L Rd inv1 fr)
    (h2 : H2StmtH W2 K ar L0 ms2 L endPc Box inv2)
    {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I3 ar L0 ls0 inv0 inv1 inv2 lbl lsize s c fs) (hs : abi.atSys s = true) {st tl : Nat}
    (hcall : Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) :
    ∃ t, ClonePostH L endPc t s c :=
  hpostH_of hN hT hCl h0 h1.toH h2 hI hs hcall

end Spike.Lib.HelloHClW

/-- info: 'Spike.Lib.HelloPreA.H1StmtHF.toH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.H1StmtHF.toH

/-- info: 'Spike.Lib.HelloHClW.cloneInvH_of_I3F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloHClW.cloneInvH_of_I3F

/-- info: 'Spike.Lib.HelloHClW.hpostH_ofF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloHClW.hpostH_ofF
