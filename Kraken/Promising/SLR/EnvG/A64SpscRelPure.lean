/-
**Part 6: the SPSC threads are pure** (the
`EnvG/TakeMpRelPure.lean` pattern): each thread's non-release writes have
pure release predicates, by one `cfgEnv_partial` table and `vcgen`
(counted, for the spin loops' back edges).

- `spscProdA_relPure`: the producer's only non-release write is its plain
  `STR W3, [X7]`, and `X7` is `buf` or `buf ^^^ 8` at every round (it never
  depends on a loaded value), whose release predicates are pure
  (`relS_B0`, `relS_B1`: `emp`).
- `spscConsA_relPure`: the consumer's only writes are `STLR`s (releases), so
  the obligation is vacuous.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnvA64
import Kraken.Promising.SLR.EnvG.A64SpscVCGen

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.SLR.EnvG.SpscA

set_option mvcgen.warning false
set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

section ProdAt

variable [CodeEnv]

/-- The producer's purity table: the frame, and at `prod_loop` the slot
pointer is one of the two slots. -/
abbrev prodPureTable (P : SP) (rel : Loc → Pred) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)).State → Prop :=
  fun lb s _ => FrameP P s ∧ (lb = "prod_loop" → s.regs.X7.toBitVec = P.b ∨ s.regs.X7.toBitVec = P.b ^^^ 8)

/-- **`spscProdA_relPure` in any ambient code** in which `spscProdA` is `PlacedIn`, from `prod` to
the end address `endA` of its last block (its script; `EnvG/A64MaskRunAt.lean`). -/
theorem spscProdA_relPure_at (P : SP) (rel : Loc → Pred) (h0 : ∀ v, Pred.Pure (rel P.B0) v)
    (h1 : ∀ v, Pred.Pure (rel P.B1) v)
    (hpl : Program.PlacedIn spscProdA) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt spscProdA l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (prodPureTable P rel) "prod" s g → Safely (cenv.instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
      (fun x => (x.1.2 = endA ∧ True) ∨ False)
      ((s, (_root_.Executable.labels cenv).label "prod"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
    (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (prodPureTable P rel) ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env [spscProdA]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hx1, hx2, hdh, hdt, hdb, hdb1⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [forall_const, true_implies] at hT
  all_goals try simp at hdb1
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.relPureQ_step,
    SharedEnv.relPureQ_ok_load, SharedEnv.relPureQ_ok_store, and_true, true_and] at *
  all_goals try (simp [hx0, hx1, hx2, hdh, hdt, hdb, hdb1]; done)
  case vc1 =>
    refine ⟨?_, fun _ => .inl ?_⟩ <;> simp [FrameP, hx0, hx1, hx2, hdh, hdt, hdb, hdb1]
  case vc4 =>
    rename_i hcnt _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨?_, fun _ => ?_⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    · simp [FrameP, hx0, hx1, hx2, hdh, hdt, hdb, hdb1]
    · simpa using hT
    · have := congrArg Prod.snd hg; simp [SharedAccess.tick] at hcnt; omega
  case vc6 =>
    intro _
    rcases hT with h | h
    · simp [h]; exact h0 _
    · simp [h]; exact h1 _
  case vc8 =>
    rename_i hstr _
    rcases hT with h | h <;> simp [h, hx0, hx1, hx2, hdh, hdt, hdb, hdb1] at hstr <;> simp [hstr.1, hx2, hdt]
  case vc10 =>
    rename_i v σ1 r1 hc r2 dm σ2 r3 hc2 σ3 r4 r5 hc3 hcnt hstr hstl _
    rcases hT with h | h <;> simp [h, hx0, hx1, hx2, hdh, hdt, hdb, hdb1] at hstr hstl hc2 hc3 hcnt
    all_goals
      obtain ⟨rfl, hs2⟩ := hstr
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨?_, fun _ => ?_⟩, .inr fun ⟨_, hg⟩ => ?_⟩
      · simp [FrameP, hx0, hx1, hx2, hdh, hdt, hdb, hdb1]
      · simp [h, BitVec.xor_assoc]
      · have := congrArg Prod.snd hg; omega
  case vc11 =>
    rename_i v σ1 r1 hc r2 dm σ2 r3 hc2 σ3 r4 r5 hc3 hcnt hstr hstl _
    rcases hT with h | h <;> simp [h, hx0, hx1, hx2, hdh, hdt, hdb, hdb1] at hstr hstl hc2 hc3 hcnt
    all_goals
      obtain ⟨rfl, -⟩ := hstr
      refine Table.ofLabelsEnv_at ⟨by decide, ⟨?_, fun h => absurd h (by decide)⟩, .inl (by decide)⟩
      simp [FrameP, hx0, hx1, hx2, hdh, hdt, hdb, hdb1]

end ProdAt

section Prod

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscProdA)]

local instance spscProdA.relPureEnv : CodeEnv := ⟨layout spscProdA⟩

/-- **The SPSC producer is pure**: its only non-release write is to a slot;
counted, partial. -/
theorem spscProdA_relPure (P : SP) (rel : Loc → Pred) (h0 : ∀ v, Pred.Pure (rel P.B0) v)
    (h1 : ∀ v, Pred.Pure (rel P.B1) v) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)) (fun s _ => FrameP P s) spscProdA
      (fun _ _ => True) (fun _ _ _ => False) :=
  have hpl : Program.Placed spscProdA "prod" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAtT hpl (by funext s g; simp [prodPureTable]) fun _ hlast =>
    spscProdA_relPure_at P rel h0 h1 hpl.toPlacedIn hlast

end Prod

section ConsAt

variable [CodeEnv]

/-- **`spscConsA_relPure` in any ambient code** in which `spscConsA` is `PlacedIn`, from `cons` to
the end address `endA` of its last block (its script; `EnvG/A64MaskRunAt.lean`). -/
theorem spscConsA_relPure_at (P : SP) (rel : Loc → Pred)
    (hpl : Program.PlacedIn spscConsA) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt spscConsA l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (fun (_ : Label) s
      (_ : (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)).State) => FrameC P s) "cons" s g → Safely (cenv.instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
      (fun x => (x.1.2 = endA ∧ True) ∨ False)
      ((s, (_root_.Executable.labels cenv).label "cons"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
    (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun (_ : Label) s
      (_ : (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)).State) => FrameC P s) ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env [spscConsA]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hx2, hdh, hdt, hdb, hdb1⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals try simp at hdb1
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.relPureQ_step,
    SharedEnv.relPureQ_ok_load, SharedEnv.relPureQ_ok_store, and_true, true_and] at *
  all_goals try (simp [hx0, hx1, hx2, hdh, hdt, hdb, hdb1]; done)
  all_goals try (simp [FrameC, hx0, hx1, hx2, hdh, hdt, hdb, hdb1]; done)
  -- the spin loops' back edges: the counter moved
  case vc4 | vc4 | vc4 =>
    rename_i hcnt _
    refine Table.ofLabelsEnv_at ⟨by decide, by simp [FrameC, hx0, hx1, hx2, hdh, hdt, hdb, hdb1],
      .inr fun ⟨_, hg⟩ => ?_⟩
    have := congrArg Prod.snd hg; simp [SharedAccess.tick] at hcnt; omega
  -- `B cdone`
  case vc10 =>
    exact Table.ofLabelsEnv_at ⟨by decide, by simp [FrameC, hx0, hx1, hx2, hdh, hdt, hdb, hdb1], .inl (by decide)⟩

end ConsAt

section Cons

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscConsA)]

local instance spscConsA.relPureEnv : CodeEnv := ⟨layout spscConsA⟩

/-- **The SPSC consumer is pure**: it makes only release writes; counted,
partial. -/
theorem spscConsA_relPure (P : SP) (rel : Loc → Pred) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)) (fun s _ => FrameC P s) spscConsA
      (fun _ _ => True) (fun _ _ _ => False) :=
  have hpl : Program.Placed spscConsA "cons" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAtT hpl (by funext s g; simp) fun _ hlast => spscConsA_relPure_at P rel hpl.toPlacedIn hlast

end Cons

end Kraken.Promising.SLR.EnvG.SpscA

#print axioms Kraken.Promising.SLR.EnvG.SpscA.spscProdA_relPure
#print axioms Kraken.Promising.SLR.EnvG.SpscA.spscConsA_relPure
