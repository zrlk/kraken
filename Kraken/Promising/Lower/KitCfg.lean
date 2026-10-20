/-
**The function cfg rule with a general edge guard.**
ISA: AArch64 (`Kraken.AArch64.EnvCfg`); a statement about
the env-level `Safely` judgment of laid-out code, no machine.

The MS queue pilot's `cfgEnv_partial_fun_rank` (`Lower/MsqPilotSpecs.lean`, left where it
is) orders the zero-step exits of a function fragment by a label rank, then
by the text. Restated here in general:

- **`MachineWP.cfgEnv_partial_fun_guard`**: `cfgEnv_partial_fun`
  (`AArch64/EnvCallsPartial.lean`) for any guard `Gd` on the exits (the
  fall-through included) that some label measure `μ` makes well founded: a
  guarded exit lowers `μ` or leaves the entry state (`hGd`).
- **`MachineWP.cfgEnv_partial_fun_edgeRank`**: the MS queue pilot's
  `cfgEnv_partial_fun_rank`, verbatim statement, as the instance
  `Gd := EdgeRank p ρ`, `μ l := ρ l * (N + 1) + (N - blockIdx p l)`.

A lowering whose loops retry without a shared access picks `μ` (or a rank)
to fit its block order; one whose retry edges go forward uses
`cfgEnv_partial_fun` as is.
-/
import Kraken.AArch64.EnvCallsPartial
import Kraken.Promising.SLR.EnvG.MsQueueCfg

open Kraken
open Std.WP

namespace MachineWP

variable [CodeEnv] {env : SharedEnv}

/-- **The function cfg rule with an edge guard `Gd` and a label measure `μ`**:
from the table entry at the fragment's entry `l₀`, every run reaches `E` or
runs forever, when each block's triple guards its exits (to labels of the
fragment, and its fall-through) by `Gd`, and every guarded exit from a block
lowers `μ` or changes the state (`hGd`). -/
theorem cfgEnv_partial_fun_guard {p p' : Program} {E : Int64 → MachineData → env.State → Prop} {l₀ : Label}
    (T : Label → MachineData → env.State → Prop) (μ : Label → Nat)
    (Gd : Label → MachineData → env.State → Label → MachineData → env.State → Prop)
    (hGd : ∀ l blk, Program.blockAt p l = some blk → ∀ s₀ g₀ l' s g, Gd l s₀ g₀ l' s g →
      μ l' < μ l ∨ ¬ (s = s₀ ∧ g = g₀))
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ (s₀ : MachineData) (g₀ : env.State),
      ⦃ fun s g => T l s g ∧ s = s₀ ∧ g = g₀ ⦄ (⟨blk.body⟩ : EnvProgram env)
      ⦃ (match blk.next with
         | some l' => fun _ s g => T l' s g ∧ Gd l s₀ g₀ l' s g
         | none => fun _ _ _ => False);
        fun a s g => Table.ofLabelsEnv (fun l' s g => (Program.blockAt p l').isSome ∧ T l' s g
          ∧ Gd l s₀ g₀ l' s g) a s g ∨ E a s g ⦄)
    (hp : p = Directive.label l₀ :: p') (hwf : Program.WF p) (hpl : Program.PlacedIn p) :
    ∀ s g, T l₀ s g → Safely (cenv.instrStepEnv env) (fun x => E x.1.2 x.1.1 x.2)
      ((s, (_root_.Executable.labels cenv).label l₀), g) := by
  have hnd := hwf.nodup
  intro s g hT
  have key := Program.linkEnv_partial (env := env)
    (post := fun x => E x.1.2 x.1.1 x.2)
    (fun l => (Program.blockAt p l).elim [] (·.body))
    (fun l => (_root_.Executable.labels cenv).label l)
    (fun l s g => (Program.blockAt p l).isSome ∧ T l s g)
    (fun j i => μ j < μ i) (measure μ).wf ?_ ?_
  · exact key l₀ s g ⟨Program.blockAt_entry' hp, hT⟩
  · intro l
    cases hb : Program.blockAt p l with
    | none => exact trivial
    | some blk => simpa using hpl.block l blk hb
  · intro l s₀ g₀
    cases hb : Program.blockAt p l with
    | none => exact fun s g hpre => absurd hpre.1.1 (by simp)
    | some blk =>
      simp only [Option.elim]
      rintro s g ⟨⟨-, hTl⟩, rfl, rfl⟩
      have hw := (hblocks l blk hb s g).le_wp s g ⟨hTl, rfl, rfl⟩
      rw [wpEnv_eq] at hw
      refine Executable.wpEnv_mono ?_ ?_ hw
      · intro s' g' hq
        cases hnx : blk.next with
        | some l' =>
          rw [hnx] at hq
          obtain ⟨hsome', -⟩ := Program.blockAt_next hnd hb hnx
          obtain ⟨hq, he⟩ := hq
          refine Or.inr ⟨l', (hpl.next l blk l' hb hnx).symm, ⟨hsome', hq⟩, ?_⟩
          rcases hGd l blk hb s g l' s' g' he with h | hne
          · exact .inl h
          · exact .inr fun ⟨_, h1, h2⟩ => hne ⟨h1, h2⟩
        | none =>
          rw [hnx] at hq
          exact hq.elim
      · rintro a s' g' (⟨l', hlab, hsome', hTl', he⟩ | he)
        · refine Or.inr ⟨l', hlab, ⟨hsome', hTl'⟩, ?_⟩
          rcases hGd l blk hb s g l' s' g' he with h | hne
          · exact .inl h
          · exact .inr fun ⟨_, h1, h2⟩ => hne ⟨h1, h2⟩
        · exact Or.inl he

open Kraken.Promising.SLR.EnvG.MsQueue (EdgeRank) in
/-- **`cfgEnv_partial_fun` with a label rank** `ρ` (the MS queue pilot's
`cfgEnv_partial_fun_rank`, same statement): every exit is guarded by
`EdgeRank` (smaller rank, or the same rank and later in the text, or a
changed state). The instance of `cfgEnv_partial_fun_guard` at the
lexicographic measure. -/
theorem cfgEnv_partial_fun_edgeRank {p p' : Program} {E : Int64 → MachineData → env.State → Prop} {l₀ : Label}
    (T : Label → MachineData → env.State → Prop) (ρ : Label → Nat)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ (s₀ : MachineData) (g₀ : env.State),
      ⦃ fun s g => T l s g ∧ s = s₀ ∧ g = g₀ ⦄ (⟨blk.body⟩ : EnvProgram env)
      ⦃ (match blk.next with
         | some l' => fun _ s g => T l' s g ∧ EdgeRank p ρ l s₀ g₀ l' s g
         | none => fun _ _ _ => False);
        fun a s g => Table.ofLabelsEnv (fun l' s g => (Program.blockAt p l').isSome ∧ T l' s g
          ∧ EdgeRank p ρ l s₀ g₀ l' s g) a s g ∨ E a s g ⦄)
    (hp : p = Directive.label l₀ :: p') (hwf : Program.WF p) (hpl : Program.PlacedIn p) :
    ∀ s g, T l₀ s g → Safely (cenv.instrStepEnv env) (fun x => E x.1.2 x.1.1 x.2)
      ((s, (_root_.Executable.labels cenv).label l₀), g) := by
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length := Program.blockIdx_le p
  refine cfgEnv_partial_fun_guard T
    (fun l => ρ l * ((Program.view p).2.length + 1) + ((Program.view p).2.length - Program.blockIdx p l))
    (EdgeRank p ρ) ?_ hblocks hp hwf hpl
  rintro l blk hb s₀ g₀ l' s g (h | ⟨h, h'⟩ | hne)
  · have hidx := Program.blockIdx_lt hwf.nodup hb
    have h1 := hK l'
    have h2 : (ρ l' + 1) * ((Program.view p).2.length + 1) ≤ ρ l * ((Program.view p).2.length + 1) :=
      Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at h2
    exact .inl (by omega)
  · have hidx := Program.blockIdx_lt hwf.nodup hb
    rw [h]
    exact .inl (by omega)
  · exact .inr hne

end MachineWP
