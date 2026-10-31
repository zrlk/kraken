/-
**`WakeO.OPrem.hsplit` at `wakeD`** (x86-64): at the take site
`a := X64WakeOSide.aW hp i E`, a state of the fragment invariant
`I2 ar L0 ls0 inv0 inv1` with held list `hl` (`HeldOk2 Λ r0 r1`) takes
main's stack `r0` with nothing held (an `inv0` state) or the child's `r1`
with `r0` held (an `inv1` state), from the take facts:

- at the take pc, `inv0`'s states take `r0` (`WakeWc.H0Take`) and do not own
  it (`H0TakeOwn`); `inv1`'s take `r1` (`H1Take`), own `r0` and not `r1`
  (`H1TakeOwn`);
- `HeldOk2`'s held list is tied to the state by ownership, and a range
  owned (`Owned`: its aligned words load) is not unowned (`Unowned`: no
  byte mapped) once it holds an aligned word (`owned_not_unowned`; the two
  stacks are 8-aligned, `r0W_al`, `r1W_al`), nor not in private memory
  (`¬ StackM`, the take facts' form: `owned_not_stackM`).

The take facts are `WakeWc.H0Take`/`H0TakeOwn`/`H1Take`/`H1TakeOwn`
(`Spike/Lib/X64WakeWcInv.lean`) at `L := ofPlaceWX hp i`, `a := aW hp i E`.

x86-64 twin of `Spike/Lib/WakeOSplit.lean` (same names, namespace
`Spike.Lib.X64.WakeOSplit`).

**Unlike AArch64**: `hsplit_W` takes `{asm} (hpa : cellsOf asm = some o.prog)`
(`X64WakeOSide.ha_W`'s premise) in place of A64's `hpa`/`hwp` on
`SccCertificate.asm`; `owned_not_unowned` is proved from
`stackM_of_owned`/`unowned_not_stackM`.
-/
import Spike.Lib.X64WakeOD
import Spike.Lib.X64OwnedMono
import Spike.Lib.X64HeldOk2
import Spike.Lib.X64WakeWcInv
import Spike.Lib.X64OwnedStackM

namespace Spike.Lib.X64.WakeOSplit

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer (Owned Unowned)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib (PlaceWX)

/-- **An owned range holding an aligned word is not unowned.** -/
theorem owned_not_unowned {Λ : Scc.Sem.Layout} {r : Range} {s : State} (ho : Owned Λ r s) (hu : Unowned r s)
    (hal : r.lo % 8 = 0) (hsz : 8 ≤ r.size) : False :=
  Spike.Lib.X64Consumer.unowned_not_stackM hu hal hsz (Spike.Lib.X64Consumer.stackM_of_owned ho)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ0 o)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

include hp

/-- main's stack is 8-aligned, of a word at least. -/
theorem r0W_al : (X64WakeOSide.r0W hp i).lo % 8 = 0 ∧ 8 ≤ (X64WakeOSide.r0W hp i).size := by
  obtain ⟨hl, hs⟩ := Spike.Lib.X64.Rt.Ti2.r0Of_eq (Ly).lab
  have ha := (Ly).stacks_al
  rw [show (Ly).stacksA = Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab from (Ly).lab_stacks.symm] at ha
  simp only [X64WakeOSide.r0W, hl, hs]
  omega

/-- The child's stack is 8-aligned, of a word at least. -/
theorem r1W_al : (X64WakeOSide.r1W hp i).lo % 8 = 0 ∧ 8 ≤ (X64WakeOSide.r1W hp i).size := by
  have hlt := X64WakeOSide.stacks_lt hp i
  simp only at hlt
  obtain ⟨hl, hs⟩ := Spike.Lib.X64.Rt.Ti2.r1Of_eq (lab := (Ly).lab) (by omega)
  have ha := (Ly).stacks_al
  rw [show (Ly).stacksA = Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab from (Ly).lab_stacks.symm] at ha
  simp only [X64WakeOSide.r1W, hl, hs]
  omega

/-- **`OPrem.hsplit` at `wakeD`**, from the take facts at the take pc. -/
theorem hsplit_W {asm : Scc.Sem.X64.Asm} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (E : Scc.Sem.Entry) (cT : Loc) (Dt : State → Prop) (ls0 : Spike.Lib.X64Consumer.Lsize)
    (W0 inv0 : Spike.Lib.FragS isa)
    (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → Spike.Lib.FragS isa)
    (h0t : Spike.Lib.X64.Flow.WakeWc.H0Take (Ly) (X64WakeOSide.aW hp i E) inv0)
    (h0o : Spike.Lib.X64.Flow.WakeWc.H0TakeOwn (Ly) (X64WakeOSide.aW hp i E) inv0)
    (h1t : Spike.Lib.X64.Flow.WakeWc.H1Take (Ly) (X64WakeOSide.aW hp i E) inv1)
    (h1o : Spike.Lib.X64.Flow.WakeWc.H1TakeOwn (Ly) (X64WakeOSide.aW hp i E) inv1) :
    let D := WakeOD.wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1
    ∀ lbl lsize s c fs hl, Spike.Lib.X64ConsumerA.I2 D.ar D.L0 D.ls0 D.inv0 D.inv1 lbl lsize s c fs →
      Spike.Lib.X64Consumer.HeldOk2 (Ly).Λ D.r0 D.r1 s hl →
      ∀ a, ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ).site .take = some a →
        pcOf s = a →
        (hl = [] ∧ Scc.Sem.Kernel.siteRange Scc.Sem.X64.abi s = D.r0) ∨
          (hl = [(0, D.r0)] ∧ Scc.Sem.Kernel.siteRange Scc.Sem.X64.abi s = D.r1) := by
  intro D lbl lsize s c fs hl hI hH a ha hpc
  rw [X64WakeOSide.ha_W hp i hpa E] at ha
  cases ha
  obtain ⟨al0, sz0⟩ := r0W_al hp i
  obtain ⟨al1, sz1⟩ := r1W_al hp i
  rcases hI with ⟨-, -, hi⟩ | ⟨l, b, n, -, -, -, -, hi⟩
  · have hr := h0t s c fs hi hpc
    have hu := h0o s c fs hi hpc
    rcases hH with ⟨rfl, -, -⟩ | ⟨-, ho, -⟩ | ⟨-, ho, -⟩
    · exact .inl ⟨rfl, hr⟩
    · exact (Spike.Lib.X64Consumer.owned_not_stackM ho hu).elim
    · exact (Spike.Lib.X64Consumer.owned_not_stackM ho hu).elim
  · have hr := h1t l b n s c fs hi hpc
    obtain ⟨ho0, hu1⟩ := h1o l b n s c fs hi hpc
    rcases hH with ⟨-, hu0, -⟩ | ⟨rfl, -, -⟩ | ⟨-, -, ho1⟩
    · exact (owned_not_unowned ho0 hu0 al0 sz0).elim
    · exact .inr ⟨rfl, hr⟩
    · exact (Spike.Lib.X64Consumer.owned_not_stackM ho1 hu1).elim

end Place

end Spike.Lib.X64.WakeOSplit

/-- info: 'Spike.Lib.X64.WakeOSplit.owned_not_unowned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeOSplit.owned_not_unowned

/-- info: 'Spike.Lib.X64.WakeOSplit.r0W_al' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeOSplit.r0W_al

/-- info: 'Spike.Lib.X64.WakeOSplit.r1W_al' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeOSplit.r1W_al

/-- info: 'Spike.Lib.X64.WakeOSplit.hsplit_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeOSplit.hsplit_W
