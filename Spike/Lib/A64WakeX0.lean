/-
**`W0`'s per-state facts at wake** (`X0W`, AArch64): what `h0`'s maximal
invariant `inv0` owes at each of its states (`H0Stmt`'s "never at the
`clone`", `H0Take`, `H0TakeOwn`, `Spike/Lib/A64WakeWcInv.lean`), asked of
every state of `W0` (`WakeWf.W0`'s parameter `X0`) so that any invariant
inside `W0` has them.

- `X0W L a`: off the `clone`'s pc; at the take pc `a`, the site's range
  main's stack `r0Of`, not in private memory (`¬ StackM`).
- `x0W_inv`: `X0W` at the states of an invariant inside `W0 … (X0W L a)`
  (`SegInvS`'s first component);
- `noClone_of`, `h0Take_of`, `h0TakeOwn_of`: `H0Stmt`'s clone clause,
  `H0Take`, `H0TakeOwn` from it.
-/
import Spike.Lib.A64WakeWf
import Spike.Lib.A64WakeWcInv
import Spike.Lib.A64OwnedMono

namespace Spike.Lib.A64.WakeWf

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib (Arena FragS)
open Spike.Lib.A64Consumer (Lbl Lsize Own)
open Spike.Lib.A64ConsumerA (SegInvS)
open Spike.Lib.A64.Rt (RuntimeLayout)

/-- **`h0`'s per-state facts at `W0`**: off the `clone`, and at the take
pc `a` main's stack the site's range, not in private memory (`¬ StackM`:
not yet taken). -/
def X0W (L : RuntimeLayout) (a : Int64) (s : State) : Prop :=
  pcOf s ≠ Spike.Lib.A64.Flow.WakeWc.clonePc L ∧
    (pcOf s = a.toBitVec.toNat →
      Kernel.siteRange abi s = Spike.Lib.A64.Rt.Ti2.r0Of L.lab ∧
      ¬ Spike.Lib.A64.Flow.Ret0.StackM (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) s.st.1)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {ar : Arena} {p : Prog} {Dt Ab Cl Ac : State → Prop}
  {Ctx : FragS isaLSE2} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {K : State → State → Prop}
  {ms0 : List TermRun.Frame → Spike.Lib.MemSide isaLSE2} {inv0 : FragS isaLSE2} {L : RuntimeLayout}
  {a : Int64}

/-- **`X0W` at an invariant inside `W0`.** -/
theorem x0W_inv (h : SegInvS (W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM (X0W L a)) K p L0 ms0 inv0) :
    ∀ s c fs, inv0 s c fs → X0W L a s :=
  fun s c fs hi => (h s c fs hi).1.2.1

/-- **`H0Stmt`'s clone clause** at an invariant inside `W0 … (X0W L a)`. -/
theorem noClone_of (h : SegInvS (W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM (X0W L a)) K p L0 ms0 inv0) :
    ∀ s c fs, inv0 s c fs → pcOf s ≠ Spike.Lib.A64.Flow.WakeWc.clonePc L :=
  fun s c fs hi => (x0W_inv h s c fs hi).1

/-- **`H0Take`** at an invariant inside `W0 … (X0W L a)`. -/
theorem h0Take_of (h : SegInvS (W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM (X0W L a)) K p L0 ms0 inv0) :
    Spike.Lib.A64.Flow.WakeWc.H0Take L a inv0 :=
  fun s c fs hi hpc => ((x0W_inv h s c fs hi).2 hpc).1

/-- **`H0TakeOwn`** at an invariant inside `W0 … (X0W L a)`. -/
theorem h0TakeOwn_of (h : SegInvS (W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM (X0W L a)) K p L0 ms0 inv0) :
    Spike.Lib.A64.Flow.WakeWc.H0TakeOwn L a inv0 :=
  fun s c fs hi hpc => ((x0W_inv h s c fs hi).2 hpc).2

end Spike.Lib.A64.WakeWf

/-- info: 'Spike.Lib.A64.WakeWf.h0Take_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.h0Take_of

/-- info: 'Spike.Lib.A64.WakeWf.h0TakeOwn_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.h0TakeOwn_of
