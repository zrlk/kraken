/-
**Level 1's take fact narrowed to its use** (hello.w, x86-64; the twin of `Spike/Lib/A64HelloTake1X.lean`): level
1's states at the take pc `a` only need the shape of `H0TakeH`/`H0TakeOwnH` (at `a`, the site's range main's stack
`r0Of`, and `r0Of` not in private memory) to discharge `OPrem.hsplit` at level-1 states at `a`: `HeldOk2`'s first
case is `hsplit`'s first disjunct, its other two own `r0Of`, refuted by `¬ StackM r0Of` (`owned_not_stackM`). That
shape is the start's per-state fact `StartGlue.X0WH`'s second conjunct, which level 1 carries, so level 1's
invariant gives it with no strengthening.

- `H1TakeXH`: level 1's take fact at `a` (`H0TakeH ∧ H0TakeOwnH`'s shape at every label).
- `h1TakeXH_of_x0WH`: from `X0WH L a` at the invariant's states.
- `h1TakeXH_inv1G`: at `H1Gfp.inv1G` inside `X0WH` facts (`x_of_inv1G`); `h1TakeXH_and`: at `inv ∧ U`-style
  strengthenings.
- `hsplitHX`: `OPrem.hsplit`'s shape at `I3`, level 1 discharged as level 0.

Unlike AArch64:
- A64's `H1TakeH` and `HelloPreA.hsplitH` are not twinned on x86-64 (`X64HelloWcInv3`), so `hsplitHX` stands on
  its own (A64: `hsplitH` with `h1t : H1TakeH` replaced), and the non-vacuity example is stated from states off
  the take pc (A64: from `H1TakeH`);
- the example at level 1's own invariant (A64's at `Level1I.h1_level1`'s `inv1G … (XR hpw i0) …`) is not stated
  here: x86-64's level-1 invariant module is not yet present; `h1TakeXH_inv1G` is the lemma it instantiates;
- the ISA is x86-64's (`isa`, `Scc.Sem.X64.abi`, `X64Consumer.Owned`/`HeldOk2`, `X64.WakeOSplit.owned_not_unowned`).
-/
import Spike.Lib.X64HelloH1Gfp
import Spike.Lib.X64HelloStartGlue
import Spike.Lib.X64OwnedStackM
import Spike.Lib.X64HelloWcInv3
import Spike.Lib.X64WakeOSplit

namespace Spike.Lib.X64HelloPreA.Take1X

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize Owned Unowned HeldOk2)
open Spike.Lib.X64ConsumerA (I3)
open Spike.Lib.X64HelloPreA (H0TakeH H0TakeOwnH H2TakeH H2TakeOwnH)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)

/-- **`h1`'s take fact at its use**: at the take pc `a`, level 1's states have the site's range main's stack and
main's stack not in private memory (`H0TakeH ∧ H0TakeOwnH`'s shape per label). Unlike AArch64, over x86-64's
states and `Scc.Sem.X64.abi`. -/
def H1TakeXH (L : RuntimeLayout) (a : Int64) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa) : Prop :=
  ∀ l b n s c fs, inv1 l b n s c fs → pcOf s = a.toBitVec.toNat →
    Scc.Sem.Kernel.siteRange Scc.Sem.X64.abi s = Spike.Lib.X64.Rt.Ti2.r0Of L.lab ∧
      ¬ Spike.Lib.X64.Flow.Ret0.StackM (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) s.st.1

/-- **`H1TakeXH` from the start's per-state fact** `X0WH L a` at the invariant's states. -/
theorem h1TakeXH_of_x0WH {L : RuntimeLayout} {a : Int64} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    (h : ∀ l b n s c fs, inv1 l b n s c fs → X0WH L a s) : H1TakeXH L a inv1 :=
  fun l b n s c fs hi hpc => (h l b n s c fs hi).2 hpc

/-- **`H1TakeXH` at `H1Gfp.inv1G`** whose per-state facts `X` give `X0WH L a`. -/
theorem h1TakeXH_inv1G {L : RuntimeLayout} {a : Int64} {W1 X : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {K : State → State → Prop} {L0 : Lbl}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    (hX : ∀ l b n s c fs, X l b n s c fs → X0WH L a s) :
    H1TakeXH L a (Spike.Lib.X64HelloPreA.H1Gfp.inv1G W1 X K L0 ms1) :=
  h1TakeXH_of_x0WH fun l b n s c fs hi => hX l b n s c fs (Spike.Lib.X64HelloPreA.H1Gfp.x_of_inv1G hi)

/-- **`H1TakeXH` at a strengthened invariant** (`inv ∧ P`). -/
theorem h1TakeXH_and {L : RuntimeLayout} {a : Int64} {inv inv' : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    (h : H1TakeXH L a inv) (hi : ∀ l b n s c fs, inv' l b n s c fs → inv l b n s c fs) : H1TakeXH L a inv' :=
  fun l b n s c fs h' => h l b n s c fs (hi l b n s c fs h')

/-- **`OPrem.hsplit`'s shape at `I3` from the three levels' take facts**, level 1 discharged as level 0
(`HeldOk2`'s first case, the other two refuted by `¬ StackM r0Of`). Unlike AArch64 (`HelloPreA.hsplitH` with
`H1TakeH` replaced), it is stated directly: x86-64 has no `hsplitH`. -/
theorem hsplitHX {L : RuntimeLayout} {a : Int64} {ar : Arena} {L0 : Lbl} {ls0 : Lsize} {inv0 : FragS isa}
    {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    (hr0 : (Spike.Lib.X64.Rt.Ti2.r0Of L.lab).lo % 8 = 0 ∧ 8 ≤ (Spike.Lib.X64.Rt.Ti2.r0Of L.lab).size)
    (h0t : H0TakeH L a inv0) (h0o : H0TakeOwnH L a inv0) (h1t : H1TakeXH L a inv1)
    (h2t : H2TakeH L a inv2) (h2o : H2TakeOwnH L a inv2) :
    ∀ lbl lsize s c fs hl, I3 ar L0 ls0 inv0 inv1 inv2 lbl lsize s c fs →
      HeldOk2 L.Λ (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) (Spike.Lib.X64.Rt.PreChild.r1Of L.lab) s hl →
      pcOf s = a.toBitVec.toNat →
      (hl = [] ∧ Scc.Sem.Kernel.siteRange Scc.Sem.X64.abi s = Spike.Lib.X64.Rt.Ti2.r0Of L.lab) ∨
        (hl = [(0, Spike.Lib.X64.Rt.Ti2.r0Of L.lab)] ∧
          Scc.Sem.Kernel.siteRange Scc.Sem.X64.abi s = Spike.Lib.X64.Rt.PreChild.r1Of L.lab) := by
  intro lbl lsize s c fs hl hI hH hpc
  rcases hI with ⟨-, -, hi⟩ | ⟨l, b, n, -, -, -, -, hi⟩ | ⟨l, b, n, l', b', n', -, -, -, -, -, -, hi⟩
  · have hr := h0t s c fs hi hpc
    have hu := h0o s c fs hi hpc
    rcases hH with ⟨rfl, -, -⟩ | ⟨-, ho, -⟩ | ⟨-, ho, -⟩
    · exact .inl ⟨rfl, hr⟩
    · exact (Spike.Lib.X64Consumer.owned_not_stackM ho hu).elim
    · exact (Spike.Lib.X64Consumer.owned_not_stackM ho hu).elim
  · obtain ⟨hr, hu⟩ := h1t l b n s c fs hi hpc
    rcases hH with ⟨rfl, -, -⟩ | ⟨-, ho, -⟩ | ⟨-, ho, -⟩
    · exact .inl ⟨rfl, hr⟩
    · exact (Spike.Lib.X64Consumer.owned_not_stackM ho hu).elim
    · exact (Spike.Lib.X64Consumer.owned_not_stackM ho hu).elim
  · have hr := h2t l b n l' b' n' s c fs hi hpc
    obtain ⟨ho0, hu1⟩ := h2o l b n l' b' n' s c fs hi hpc
    rcases hH with ⟨-, hu0, -⟩ | ⟨rfl, -, -⟩ | ⟨-, -, ho1⟩
    · exact (Spike.Lib.X64.WakeOSplit.owned_not_unowned ho0 hu0 hr0.1 hr0.2).elim
    · exact .inr ⟨rfl, hr⟩
    · exact (Spike.Lib.X64Consumer.owned_not_stackM ho1 hu1).elim

/-- **`H1TakeXH` is not vacuous**: an invariant whose states are all off the take pc meets it (A64 states this from
`H1TakeH`, which x86-64 does not twin). -/
example (L : RuntimeLayout) (a : Int64) (P : WeakMem.AllocLabel → Nat → Nat → FragS isa)
    (h : ∀ l b n s c fs, P l b n s c fs → pcOf s ≠ a.toBitVec.toNat) : H1TakeXH L a P :=
  fun l b n s c fs hi hpc => absurd hpc (h l b n s c fs hi)

end Spike.Lib.X64HelloPreA.Take1X

/-- info: 'Spike.Lib.X64HelloPreA.Take1X.h1TakeXH_of_x0WH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.Take1X.h1TakeXH_of_x0WH

/-- info: 'Spike.Lib.X64HelloPreA.Take1X.h1TakeXH_inv1G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.Take1X.h1TakeXH_inv1G

/-- info: 'Spike.Lib.X64HelloPreA.Take1X.h1TakeXH_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.Take1X.h1TakeXH_and

/-- info: 'Spike.Lib.X64HelloPreA.Take1X.hsplitHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.Take1X.hsplitHX
