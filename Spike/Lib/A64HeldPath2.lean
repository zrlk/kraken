/-
**The take path of a thread taking two stack ranges** (AArch64, wake's
main): `HeldPathS` (`Spike/Lib/A64ConsumerS.lean`) at the held predicate
`HeldOk2 Λ r0 r1` (`Spike/Lib/A64HeldOk2.lean`).

- `heldPathS_ok2`: from the take site's facts (`TakeSiteS`), the two
  ranges in the pool, nonempty and disjoint (neither wrapping), the
  `.rodata` image off the pool, and the **take-site split** (`hsplit`): a
  fragment state at the take site holding `hl` takes `r0` with none held
  or `r1` with `r0` held. The split is a fact of the fragment `I` (which
  call of `scc_rt_stack_take` the state is in), discharged with it.
-/
import Spike.Lib.A64OwnedCopy
import Spike.Lib.A64ConsumerS

namespace Spike.Lib.A64ConsumerS

open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.A64Consumer

/-- **`HeldPathS` at `HeldOk2`**: the take site's facts, the ranges' facts
and the take-site split. -/
theorem heldPathS_ok2 {Λ : Scc.Sem.Layout} {p : CoreTerm.Prog} {μ : Marks} {I : InvS} {r0 r1 : Range}
    (hts : TakeSiteS p μ I)
    (hsplit : ∀ lbl lsize s c fs hl, I lbl lsize s c fs → HeldOk2 Λ r0 r1 s hl →
      ∀ a, μ.site .take = some a → pcOf s = a →
        (hl = [] ∧ Kernel.siteRange abi s = r0) ∨ (hl = [(0, r0)] ∧ Kernel.siteRange abi s = r1))
    (hs0 : r0.Sub Λ.stackPool) (hs1 : r1.Sub Λ.stackPool) (hz0 : 0 < r0.size) (hz1 : 0 < r1.size)
    (hro : Λ.rodata.Disjoint Λ.stackPool) (hd : r1.Disjoint r0)
    (hw0 : r0.lo + r0.size ≤ 2 ^ 64) (hw1 : r1.lo + r1.size ≤ 2 ^ 64) :
    HeldPathS Λ p μ I (HeldOk2 Λ r0 r1) where
  toTakeSiteS := hts
  own := fun _ _ h => h.own
  held := by
    intro lbl lsize s c fs hl hI hH a ha hpc
    rcases hsplit lbl lsize s c fs hl hI hH a ha hpc with ⟨rfl, hr⟩ | ⟨rfl, hr⟩
    · rw [hr]
      refine ⟨hs0, hz0, hro, fun _ h => absurd h List.not_mem_nil, fun pm _ _ _ => ?_⟩
      exact heldOk2_take0 hH hs0 hd hw1 hw0 pm
    · rw [hr]
      refine ⟨hs1, hz1, hro, fun h hm => ?_, fun pm _ _ _ => heldOk2_take1 hH hs1 pm⟩
      rw [List.mem_singleton] at hm
      subst hm
      exact hd
  instr := fun _ _ _ _ _ _ _ hH hs _ _ _ he =>
    (hH.instr hs he).mono fun _ h _ _ _ _ _ => h
  sys := fun _ _ _ _ _ _ _ hH _ _ _ _ hs' _ _ _ _ _ => hH.sys hs'

/-- info: 'Spike.Lib.A64ConsumerS.heldPathS_ok2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64ConsumerS.heldPathS_ok2

end Spike.Lib.A64ConsumerS
