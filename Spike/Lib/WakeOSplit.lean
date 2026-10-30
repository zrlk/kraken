/-
**`WakeO.OPrem.hsplit` at `wakeD`** (AArch64): at the take site
`a := WakeOSide.aW hp i E`, a state of the fragment invariant
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
(`Spike/Lib/A64WakeWcInv.lean`) at `L := ofPlaceW hp i`, `a := aW hp i E`.
-/
import Spike.Lib.WakeOD
import Spike.Lib.A64OwnedMono
import Spike.Lib.A64HeldOk2
import Spike.Lib.A64WakeWcInv
import Spike.Lib.A64OwnedStackM

namespace Spike.Lib.WakeOSplit

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer (Owned Unowned)
open Spike.Lib.A64.Rt (RuntimeLayout)

/-- **An owned range holding an aligned word is not unowned.** -/
theorem owned_not_unowned {Λ : Scc.Sem.Layout} {r : Range} {s : State} (ho : Owned Λ r s) (hu : Unowned r s)
    (hal : r.lo % 8 = 0) (hsz : 8 ≤ r.size) : False := by
  have h := ho.2 r.lo hal ⟨Nat.le_refl _, by omega⟩ ⟨by omega, by omega⟩
  have key : (Mem.loadInt s.st.1.dmem (BitVec.ofNat 64 r.lo) 8).isSome = true ↔
      ∀ i, i < 8 → BitVec.ofNat 64 r.lo + BitVec.ofNat 64 i ∈ s.st.1.dmem := by
    simp [Mem.loadInt, Option.isSome_map, Mem.loadBytes, List.allSome_isSome_iff]
  simp only [Scc.Sem.A64.privLoad, Option.isSome_map] at h
  have h0 := (key.mp h) 0 (by decide)
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at h0
  exact hu r.lo ⟨Nat.le_refl _, by omega⟩ h0

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

include hp

/-- main's stack is 8-aligned, of a word at least. -/
theorem r0W_al : (WakeOSide.r0W hp i).lo % 8 = 0 ∧ 8 ≤ (WakeOSide.r0W hp i).size := by
  obtain ⟨hl, hs⟩ := Spike.Lib.A64.Rt.Ti2.r0Of_eq (Ly).lab
  have ha := (Ly).stacks_al
  rw [show (Ly).stacksA = Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab from (Ly).lab_stacks.symm] at ha
  simp only [WakeOSide.r0W, hl, hs]
  omega

/-- The child's stack is 8-aligned, of a word at least. -/
theorem r1W_al : (WakeOSide.r1W hp i).lo % 8 = 0 ∧ 8 ≤ (WakeOSide.r1W hp i).size := by
  have hlt := WakeOSide.stacks_lt hp i
  simp only at hlt
  obtain ⟨hl, hs⟩ := Spike.Lib.A64.Rt.Ti2.r1Of_eq (lab := (Ly).lab) (by omega)
  have ha := (Ly).stacks_al
  rw [show (Ly).stacksA = Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab from (Ly).lab_stacks.symm] at ha
  simp only [WakeOSide.r1W, hl, hs]
  omega

/-- **`OPrem.hsplit` at `wakeD`**, from the take facts at the take pc. -/
theorem hsplit_W (hpa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok o.prog)
    (hwp : Scc.Sem.A64.textProgram SccCertificate.asm = .ok Spike.Lib.A64.WakeLabels.wakeProg)
    (E : Scc.Sem.Entry) (cT : Loc) (Dt : State → Prop) (ls0 : Spike.Lib.A64Consumer.Lsize)
    (W0 inv0 : Spike.Lib.FragS isaLSE2)
    (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → Spike.Lib.FragS isaLSE2)
    (h0t : Spike.Lib.A64.Flow.WakeWc.H0Take (Ly) (WakeOSide.aW hp i E) inv0) (h0o : Spike.Lib.A64.Flow.WakeWc.H0TakeOwn (Ly) (WakeOSide.aW hp i E) inv0)
    (h1t : Spike.Lib.A64.Flow.WakeWc.H1Take (Ly) (WakeOSide.aW hp i E) inv1) (h1o : Spike.Lib.A64.Flow.WakeWc.H1TakeOwn (Ly) (WakeOSide.aW hp i E) inv1) :
    let D := WakeOD.wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1
    ∀ lbl lsize s c fs hl, Spike.Lib.A64ConsumerA.I2 D.ar D.L0 D.ls0 D.inv0 D.inv1 lbl lsize s c fs →
      Spike.Lib.A64Consumer.HeldOk2 (Ly).Λ D.r0 D.r1 s hl →
      ∀ a, ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks SccCertificate.asm (Ly).Λ).site .take = some a →
        pcOf s = a →
        (hl = [] ∧ Scc.Sem.Kernel.siteRange Scc.Sem.A64.abi s = D.r0) ∨
          (hl = [(0, D.r0)] ∧ Scc.Sem.Kernel.siteRange Scc.Sem.A64.abi s = D.r1) := by
  intro D lbl lsize s c fs hl hI hH a ha hpc
  rw [WakeOSide.ha_W hp i hpa hwp E] at ha
  cases ha
  obtain ⟨al0, sz0⟩ := r0W_al hp i
  obtain ⟨al1, sz1⟩ := r1W_al hp i
  rcases hI with ⟨-, -, hi⟩ | ⟨l, b, n, -, -, -, -, hi⟩
  · have hr := h0t s c fs hi hpc
    have hu := h0o s c fs hi hpc
    rcases hH with ⟨rfl, -, -⟩ | ⟨-, ho, -⟩ | ⟨-, ho, -⟩
    · exact .inl ⟨rfl, hr⟩
    · exact (Spike.Lib.A64Consumer.owned_not_stackM ho hu).elim
    · exact (Spike.Lib.A64Consumer.owned_not_stackM ho hu).elim
  · have hr := h1t l b n s c fs hi hpc
    obtain ⟨ho0, hu1⟩ := h1o l b n s c fs hi hpc
    rcases hH with ⟨-, hu0, -⟩ | ⟨rfl, -, -⟩ | ⟨-, -, ho1⟩
    · exact (owned_not_unowned ho0 hu0 al0 sz0).elim
    · exact .inr ⟨rfl, hr⟩
    · exact (Spike.Lib.A64Consumer.owned_not_stackM ho1 hu1).elim

end Place

/-- info: 'Spike.Lib.WakeOSplit.hsplit_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hsplit_W

end Spike.Lib.WakeOSplit
