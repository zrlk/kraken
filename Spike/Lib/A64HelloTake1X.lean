/-
**Level 1's take fact narrowed to its use** (hello.w, AArch64): `HelloPreA.hsplitH`
reads `H1TakeH a inv1` ("level 1 is never at the take pc `a`") only to discharge `OPrem.hsplit` at level-1 states at
`a`. `H0TakeH`/`H0TakeOwnH`'s shape (at `a`, the site's range main's stack `r0Of`, and `r0Of` not in private memory)
discharges it as well: `HeldOk2`'s first case is `hsplit`'s first disjunct, its other two own `r0Of`, refuted by
`¬ StackM r0Of` (`owned_not_stackM`). That shape is the start's per-state fact `StartGlue.X0WH (AX)`'s second
conjunct, which level 1 carries (`Level1I.XR`), so level 1's invariant gives it with no strengthening.

- `H1TakeXH`: level 1's take fact at `a` (`H0TakeH ∧ H0TakeOwnH`'s shape at every label).
- `h1TakeXH_of_x0WH`: from `X0WH L a` at the invariant's states.
- `h1TakeXH_inv1G`: at `H1Gfp.inv1G` inside `X0WH` facts (`x_of_inv1G`); `h1TakeXH_and`: at `inv ∧ U`-style
  strengthenings (`RootL1U.inv1RU`).
- `hsplitHX`: `HelloPreA.hsplitH` with `h1t : H1TakeH` replaced by `H1TakeXH` (its proof, the level-1 case as
  level 0's).
-/
import Spike.Lib.A64HelloH1Gfp
import Spike.Lib.A64HelloStartGlue
import Spike.Lib.A64OwnedStackM
import Spike.Lib.A64HelloLevel1I

namespace Spike.Lib.HelloPreA.Take1X

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize Owned Unowned HeldOk2)
open Spike.Lib.A64ConsumerA (I3)
open Spike.Lib.HelloPreA (H0TakeH H0TakeOwnH H2TakeH H2TakeOwnH)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)

/-- **`h1`'s take fact at its use**: at the take pc `a`, level 1's states have the site's range main's stack and
main's stack not in private memory (`H0TakeH ∧ H0TakeOwnH`'s shape per label). -/
def H1TakeXH (L : RuntimeLayout) (a : Int64) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) : Prop :=
  ∀ l b n s c fs, inv1 l b n s c fs → pcOf s = a.toBitVec.toNat →
    Scc.Sem.Kernel.siteRange Scc.Sem.A64.abi s = Spike.Lib.A64.Rt.Ti2.r0Of L.lab ∧
      ¬ Spike.Lib.A64.Flow.Ret0.StackM (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) s.st.1

/-- **`H1TakeXH` from the start's per-state fact** `X0WH L a` at the invariant's states. -/
theorem h1TakeXH_of_x0WH {L : RuntimeLayout} {a : Int64} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (h : ∀ l b n s c fs, inv1 l b n s c fs → X0WH L a s) : H1TakeXH L a inv1 :=
  fun l b n s c fs hi hpc => (h l b n s c fs hi).2 hpc

/-- **`H1TakeXH` at `H1Gfp.inv1G`** whose per-state facts `X` give `X0WH L a` (`Level1I.XR`'s by definition). -/
theorem h1TakeXH_inv1G {L : RuntimeLayout} {a : Int64} {W1 X : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {K : State → State → Prop} {L0 : Lbl}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
    (hX : ∀ l b n s c fs, X l b n s c fs → X0WH L a s) :
    H1TakeXH L a (Spike.Lib.HelloPreA.H1Gfp.inv1G W1 X K L0 ms1) :=
  h1TakeXH_of_x0WH fun l b n s c fs hi => hX l b n s c fs (Spike.Lib.HelloPreA.H1Gfp.x_of_inv1G hi)

/-- **`H1TakeXH` at a strengthened invariant** (`inv ∧ P`, as `RootL1U.inv1RU`). -/
theorem h1TakeXH_and {L : RuntimeLayout} {a : Int64} {inv inv' : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (h : H1TakeXH L a inv) (hi : ∀ l b n s c fs, inv' l b n s c fs → inv l b n s c fs) : H1TakeXH L a inv' :=
  fun l b n s c fs h' => h l b n s c fs (hi l b n s c fs h')

/-- **`HelloPreA.hsplitH` at `H1TakeXH`**: the same shape of `OPrem.hsplit` at `I3`, level 1 discharged as
level 0 (`HeldOk2`'s first case, the other two refuted by `¬ StackM r0Of`). -/
theorem hsplitHX {L : RuntimeLayout} {a : Int64} {ar : Arena} {L0 : Lbl} {ls0 : Lsize} {inv0 : FragS isaLSE2}
    {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (hr0 : (Spike.Lib.A64.Rt.Ti2.r0Of L.lab).lo % 8 = 0 ∧ 8 ≤ (Spike.Lib.A64.Rt.Ti2.r0Of L.lab).size)
    (h0t : H0TakeH L a inv0) (h0o : H0TakeOwnH L a inv0) (h1t : H1TakeXH L a inv1)
    (h2t : H2TakeH L a inv2) (h2o : H2TakeOwnH L a inv2) :
    ∀ lbl lsize s c fs hl, I3 ar L0 ls0 inv0 inv1 inv2 lbl lsize s c fs →
      HeldOk2 L.Λ (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) (Spike.Lib.A64.Rt.PreChild.r1Of L.lab) s hl →
      pcOf s = a.toBitVec.toNat →
      (hl = [] ∧ Scc.Sem.Kernel.siteRange Scc.Sem.A64.abi s = Spike.Lib.A64.Rt.Ti2.r0Of L.lab) ∨
        (hl = [(0, Spike.Lib.A64.Rt.Ti2.r0Of L.lab)] ∧
          Scc.Sem.Kernel.siteRange Scc.Sem.A64.abi s = Spike.Lib.A64.Rt.PreChild.r1Of L.lab) := by
  intro lbl lsize s c fs hl hI hH hpc
  rcases hI with ⟨-, -, hi⟩ | ⟨l, b, n, -, -, -, -, hi⟩ | ⟨l, b, n, l', b', n', -, -, -, -, -, -, hi⟩
  · have hr := h0t s c fs hi hpc
    have hu := h0o s c fs hi hpc
    rcases hH with ⟨rfl, -, -⟩ | ⟨-, ho, -⟩ | ⟨-, ho, -⟩
    · exact .inl ⟨rfl, hr⟩
    · exact (Spike.Lib.A64Consumer.owned_not_stackM ho hu).elim
    · exact (Spike.Lib.A64Consumer.owned_not_stackM ho hu).elim
  · obtain ⟨hr, hu⟩ := h1t l b n s c fs hi hpc
    rcases hH with ⟨rfl, -, -⟩ | ⟨-, ho, -⟩ | ⟨-, ho, -⟩
    · exact .inl ⟨rfl, hr⟩
    · exact (Spike.Lib.A64Consumer.owned_not_stackM ho hu).elim
    · exact (Spike.Lib.A64Consumer.owned_not_stackM ho hu).elim
  · have hr := h2t l b n l' b' n' s c fs hi hpc
    obtain ⟨ho0, hu1⟩ := h2o l b n l' b' n' s c fs hi hpc
    rcases hH with ⟨-, hu0, -⟩ | ⟨rfl, -, -⟩ | ⟨-, -, ho1⟩
    · exact (Spike.Lib.WakeOSplit.owned_not_unowned ho0 hu0 hr0.1 hr0.2).elim
    · exact .inr ⟨rfl, hr⟩
    · exact (Spike.Lib.A64Consumer.owned_not_stackM ho1 hu1).elim

/-- **`H1TakeXH` is not vacuous**: off the take pc every state meets it, and at the take pc a state whose site's
range is `r0Of` and `r0Of` not private (`X0WH`'s) does; so `H1TakeXH` asks strictly less than `H1TakeH`. -/
example (L : RuntimeLayout) (a : Int64) (P : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
    (h : Spike.Lib.HelloPreA.H1TakeH a P) : H1TakeXH L a P :=
  fun l b n s c fs hi hpc => absurd hpc (h l b n s c fs hi)

/-- **At level 1's `h1` invariant** (`Level1I.h1_level1`'s `inv1G … (XR hpw i0) …`, `XR` is `X0WH (AX)`): the take
fact holds with no premise. -/
example {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
    (W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (K : State → State → Prop) (L0 : Lbl)
    (ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2) :
    H1TakeXH (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0))
      ((RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0)).lab
        Spike.Lib.A64.Flow.Ret0.StackTake.siteL)
      (Spike.Lib.HelloPreA.H1Gfp.inv1G W1 (Spike.Lib.A64.HelloPh.Level1I.XR hpw i0) K L0 ms1) :=
  h1TakeXH_inv1G fun _ _ _ _ _ _ h => h

end Spike.Lib.HelloPreA.Take1X

/-- info: 'Spike.Lib.HelloPreA.Take1X.h1TakeXH_of_x0WH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.Take1X.h1TakeXH_of_x0WH

/-- info: 'Spike.Lib.HelloPreA.Take1X.h1TakeXH_inv1G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.Take1X.h1TakeXH_inv1G

/-- info: 'Spike.Lib.HelloPreA.Take1X.h1TakeXH_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.Take1X.h1TakeXH_and

/-- info: 'Spike.Lib.HelloPreA.Take1X.hsplitHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.Take1X.hsplitHX
