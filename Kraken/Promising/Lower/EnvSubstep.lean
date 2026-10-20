/-
Environment judgments with fewer outcomes, AArch64. Generic (no
program-specific names).

* `Effects.AllEnv.substep`, `Safely.substep`: a judgment of `E` is also a
  judgment of `⟨E.State, E.ok, st⟩` for any `st ⊆ E.step` (the same
  permissions, fewer outcomes). `Pilot2.Effects.AllEnv.vals`/`Safely.vals`
  (`Lower/Pilot2Bridge.lean`) are the case `st := (valsEnv E G).step`.
* `PartialTripleEnv.countedVals`: a `counted E` partial triple is one of
  `counted (valsEnv E G)`.
* The two `valsEnv` definitions, `SLR.EnvG.Vals.valsEnv` (ISA-neutral) and
  `Pilot2.valsEnv` (the AArch64 pilots'), are the same environment
  (`Pilot2.valsEnv_eq`); both keep `Skips` (`valsEnv_skips`).

Machine: the executable machine's per-thread environment semantics
(`Executable.instrStepEnv`), partial correctness (`Safely`).
-/
import Kraken.Promising.Lower.Pilot2Bridge
import Kraken.Promising.SLR.EnvG.ValsLink
import Kraken.AArch64.EnvCfg

open Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP

namespace Kraken.Promising.Lower

open Kraken.Promising.SLR.EnvG.Vals (valsEnv)

/-! ## Fewer outcomes, same permissions -/

/-- **A judgment of `E` is one of every environment with `E`'s state and
permissions and fewer outcomes.** -/
theorem Effects.AllEnv.substep {E : SharedEnv} {st : (a : SharedAccess) → E.State → a.Ret → E.State → Prop}
    (hst : ∀ a g r g', st a g r g' → E.step a g r g') {post : MachineState → E.State → Prop}
    (ef : Effects) : ∀ g, ef.AllEnv E g post → ef.AllEnv ⟨E.State, E.ok, st⟩ g post := by
  induction ef with
  | done a => exact fun g h => h
  | unimplemented => exact fun _ h => h
  | unaligned_sp => exact fun _ h => h
  | nonmem_load dmem addr w ret ih => exact fun g h => ⟨h.1, fun v g' h' => ih _ _ g' (h.2 v g' (hst _ _ _ _ h'))⟩
  | nonmem_store dmem addr v ret ih => exact fun g h => ⟨h.1, fun b g' h' => ih _ g' (h.2 b g' (hst _ _ _ _ h'))⟩
  | undefined ret ih => exact fun g h v => ih v g (h v)
  | require_read_access _ _ ok ih => exact fun g h => ih () g h
  | require_write_access _ _ ok ih => exact fun g h => ih () g h
  | require_exec_access _ ok ih => exact fun g h => ih () g h
  | sync_load k xcl dmem addr w ret ih =>
    exact fun g h => ⟨h.1, fun v g' h' => ih _ _ g' (h.2 v g' (hst _ _ _ _ h'))⟩
  | sync_store k xcl dmem addr v ret ih =>
    exact fun g h => ⟨h.1, fun b g' h' => ih _ _ g' (h.2 b g' (hst _ _ _ _ h'))⟩
  | rmw k nr dmem addr w op ret ih => exact fun g h => ⟨h.1, fun v g' h' => ih _ _ g' (h.2 v g' (hst _ _ _ _ h'))⟩
  | fence k ok ih => exact fun g h => ⟨h.1, fun g' h' => ih () g' (h.2 g' (hst _ _ _ _ h'))⟩
  | rmw_pair k dmem addr cmp1 cmp2 new1 new2 ret ih =>
    intro g h succ rev
    have h' := h succ rev
    cases rev with
    | true =>
      exact ⟨h'.1, fun v₂ g₁ h₁ => ⟨(h'.2 v₂ g₁ (hst _ _ _ _ h₁)).1,
        fun v₁ g₂ h₂ he => ih _ _ _ g₂ ((h'.2 v₂ g₁ (hst _ _ _ _ h₁)).2 v₁ g₂ (hst _ _ _ _ h₂) he)⟩⟩
    | false =>
      exact ⟨h'.1, fun v₁ g₁ h₁ => ⟨(h'.2 v₁ g₁ (hst _ _ _ _ h₁)).1,
        fun v₂ g₂ h₂ he => ih _ _ _ g₂ ((h'.2 v₁ g₁ (hst _ _ _ _ h₁)).2 v₂ g₂ (hst _ _ _ _ h₂) he)⟩⟩
  | sync_load_pair => exact fun _ h => h
  | sync_store_pair => exact fun _ h => h

/-- **`Safely` with fewer outcomes** (`Effects.AllEnv.substep`). -/
theorem Safely.substep {E : SharedEnv} {st : (a : SharedAccess) → E.State → a.Ret → E.State → Prop}
    (hst : ∀ a g r g', st a g r g' → E.step a g r g') {e : Kraken.Executable Directive}
    {post : MachineState × E.State → Prop} {x : MachineState × E.State}
    (h : Safely (e.instrStepEnv E) post x) : Safely (e.instrStepEnv ⟨E.State, E.ok, st⟩) post x := by
  obtain ⟨Inv, hx, hInv⟩ := h
  refine ⟨Inv, hx, fun y hy => (hInv y hy).imp id fun ⟨R, hT, hR⟩ => ⟨R, ?_, hR⟩⟩
  obtain ⟨d, z, rest, hcode, hstep⟩ := hT
  exact ⟨d, z, rest, hcode, hstep.imp (Effects.AllEnv.substep hst _ _) (Effects.AllEnv.substep hst _ _)⟩

/-- **A counted partial triple of `E` is one of `valsEnv E G`.** -/
theorem PartialTripleEnv.countedVals [CodeEnv] {E : SharedEnv} {G : Loc → Val → Prop}
    {P : MachineData → (SharedEnv.counted E).State → Prop} {q : Program}
    {Q : MachineData → (SharedEnv.counted E).State → Prop}
    {Ex : Int64 → MachineData → (SharedEnv.counted E).State → Prop}
    (h : PartialTripleEnv (SharedEnv.counted E) P q Q Ex) :
    PartialTripleEnv (SharedEnv.counted (valsEnv E G)) P q Q Ex :=
  fun s g hp pc hpl => Safely.substep (E := SharedEnv.counted E) (st := (SharedEnv.counted (valsEnv E G)).step)
    (fun _ _ _ _ h => ⟨h.1.1, h.2⟩) (h s g hp pc hpl)

/-! ## The two `valsEnv`s -/

/-- The pilots' `valsEnv` is the ISA-neutral one. -/
theorem Pilot2.valsEnv_eq (E : SharedEnv) (G : Loc → Val → Prop) : Pilot2.valsEnv E G = valsEnv E G := rfl

end Kraken.Promising.Lower

namespace Kraken.Promising.SLR.EnvG.Vals

/-- Fences of `valsEnv E G` are `E`'s: they skip if `E`'s do. -/
instance valsEnv_skips (E : SharedEnv) [E.Skips] (G : Loc → Val → Prop) : (valsEnv E G).Skips :=
  ⟨fun k g => ⟨(SharedEnv.Skips.fencesSkip (env := E) k g).1,
    fun g' h => (SharedEnv.Skips.fencesSkip (env := E) k g).2 g' h.1⟩⟩

end Kraken.Promising.SLR.EnvG.Vals

namespace Kraken.Promising.Lower.Pilot2

/-- Fences of `valsEnv E G` are `E`'s: they skip if `E`'s do. -/
instance valsEnv_skips (E : SharedEnv) [E.Skips] (G : Loc → Val → Prop) : (valsEnv E G).Skips :=
  ⟨(Kraken.Promising.SLR.EnvG.Vals.valsEnv_skips E G).fencesSkip⟩

end Kraken.Promising.Lower.Pilot2
