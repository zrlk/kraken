/-
**One run script for the per-thread, whole-image
and masked theorems.**

A thread's `vcgen` run is stated once, over any ambient code (`[CodeEnv]`) in
which its text is `Program.PlacedIn`, from its entry label to a named end
address `endA` (the address behind its last block, `hlast`). Such a run
serves

- the per-thread theorem, in the text's own layout: `PartialTripleEnv.of_runAt`
  turns the run into the `PartialTripleEnv` that `MachineWP.cfgEnv_partial`
  (or `cfgEnv_partial_rank`) used to give, from `Program.Placed`;
- the whole-image theorem and every mask of the image: the run at the image
  (or mask) layout, with `hlast` from `Program.last_of_check`
  (`EnvG/A64MaskCfg.lean`).

The rank rule at an entry label, `MsQueue.cfgEnv_partial_rank_at`, is
`MsQueue.cfgEnv_partial_rank` (`EnvG/MsQueueCfg.lean`) for a fragment that is
only `PlacedIn` the ambient code, as `MachineWP.cfgEnv_partial_at` is
`cfgEnv_partial`'s.
-/
import Kraken.Promising.SLR.EnvG.A64MaskCfg
import Kraken.Promising.SLR.EnvG.MsQueueCfg

open Kraken
open Std.WP

open MachineWP in
/-- **A run at the entry label gives the partial triple** of a placed text:
`Program.Placed` names the entry label's address as every placement's start
and the end of the last block as the text's end. -/
theorem MachineWP.PartialTripleEnv.of_runAt [CodeEnv] {env : SharedEnv} {p : Program} {l₀ : Label}
    {P : MachineData → env.State → Prop} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop}
    (hpl : Program.Placed p l₀)
    (h : ∀ endA : Int64, (∀ l blk, Program.blockAt p l = some blk → blk.next = none →
        cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) →
      ∀ s g, P s g → Safely (cenv.instrStepEnv env)
        (fun x => (x.1.2 = endA ∧ Q x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2)
        ((s, (_root_.Executable.labels cenv).label l₀), g)) :
    PartialTripleEnv env P p Q E := by
  intro s g hP pc hplace
  have hrun := h (cenv.after pc p) (fun l blk hb hn => by rw [hpl.last l blk hb hn, hpl.entry pc hplace])
    s g hP
  rwa [hpl.entry pc hplace] at hrun

open MachineWP in
/-- `PartialTripleEnv.of_runAt` with the precondition named as a table
entry `T` (`hP`, as `MachineWP.cfgEnv_partial`'s). -/
theorem MachineWP.PartialTripleEnv.of_runAtT [CodeEnv] {env : SharedEnv} {p : Program} {l₀ : Label}
    {P T : MachineData → env.State → Prop} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop}
    (hpl : Program.Placed p l₀) (hP : P = T)
    (h : ∀ endA : Int64, (∀ l blk, Program.blockAt p l = some blk → blk.next = none →
        cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) →
      ∀ s g, T s g → Safely (cenv.instrStepEnv env)
        (fun x => (x.1.2 = endA ∧ Q x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2)
        ((s, (_root_.Executable.labels cenv).label l₀), g)) :
    PartialTripleEnv env P p Q E := by
  subst hP
  exact PartialTripleEnv.of_runAt hpl h

namespace Kraken.Promising.SLR.EnvG.MsQueue

open MachineWP in
/-- **The partial control-flow rule with a label rank, at the entry label of
a placed fragment** (`cfgEnv_partial_rank` for a fragment only `PlacedIn` the
ambient code; the end address of its last block is named by `hlast`). -/
theorem cfgEnv_partial_rank_at [CodeEnv] {env : SharedEnv} {p p' : Program}
    {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} {l₀ : Label} {endA : Int64}
    (T : Label → MachineData → env.State → Prop) (ρ : Label → Nat)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ (s₀ : MachineData) (g₀ : env.State),
      ⦃ fun s g => T l s g ∧ s = s₀ ∧ g = g₀ ⦄ (⟨blk.body⟩ : EnvProgram env)
      ⦃ (match blk.next with
         | some l' => fun _ s g => T l' s g ∧ EdgeRank p ρ l s₀ g₀ l' s g
         | none => fun _ => Q);
        Table.ofLabelsEnv (fun l' s g => (Program.blockAt p l').isSome ∧ T l' s g
          ∧ EdgeRank p ρ l s₀ g₀ l' s g) ⦄)
    (hp : p = Directive.label l₀ :: p') (hwf : Program.WF p) (hpl : Program.PlacedIn p)
    (hlast : ∀ l blk, Program.blockAt p l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, T l₀ s g → Safely (cenv.instrStepEnv env)
      (fun x => (x.1.2 = endA ∧ Q x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2)
      ((s, (_root_.Executable.labels cenv).label l₀), g) := by
  have hnd := hwf.nodup
  intro s g hT
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length := Program.blockIdx_le p
  let N := (Program.view p).2.length
  let ν : Label → Nat := fun l => ρ l * (N + 1) + (N - Program.blockIdx p l)
  have hdec : ∀ l l', Program.blockIdx p l < N →
      (ρ l' < ρ l ∨ (ρ l' = ρ l ∧ Program.blockIdx p l < Program.blockIdx p l')) → ν l' < ν l := by
    intro l l' hl h
    have h1 := hK l'
    rcases h with h | ⟨h, h'⟩
    · have h2 : (ρ l' + 1) * (N + 1) ≤ ρ l * (N + 1) := Nat.mul_le_mul_right _ h
      rw [Nat.succ_mul] at h2
      simp only [ν]
      omega
    · simp only [ν, h]
      omega
  have key := Program.linkEnv_partial (env := env)
    (post := fun x => x.1.2 = endA ∧ Q x.1.1 x.2)
    (fun l => (Program.blockAt p l).elim [] (·.body))
    (fun l => (_root_.Executable.labels cenv).label l)
    (fun l s g => (Program.blockAt p l).isSome ∧ T l s g)
    (fun j i => ν j < ν i) (measure ν).wf ?_ ?_
  · exact (key l₀ s g ⟨blockAt_entry' hp, hT⟩).mono fun st hst => Or.inl hst
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
      have hidx : Program.blockIdx p l < (Program.view p).2.length := Program.blockIdx_lt hnd hb
      have hw := (hblocks l blk hb s g).le_wp s g ⟨hTl, rfl, rfl⟩
      rw [wpEnv_eq] at hw
      refine Executable.wpEnv_mono ?_ ?_ hw
      · intro s' g' hq
        cases hnx : blk.next with
        | some l' =>
          rw [hnx] at hq
          obtain ⟨hsome', -⟩ := Program.blockAt_next hnd hb hnx
          obtain ⟨hq, hedge⟩ := hq
          refine Or.inr ⟨l', (hpl.next l blk l' hb hnx).symm, ⟨hsome', hq⟩, ?_⟩
          rcases hedge with h | h | hne
          · exact .inl (hdec l l' hidx (.inl h))
          · exact .inl (hdec l l' hidx (.inr h))
          · exact .inr fun ⟨_, h1, h2⟩ => hne ⟨h1, h2⟩
        | none =>
          rw [hnx] at hq
          exact Or.inl ⟨hlast l blk hb hnx, hq⟩
      · rintro a s' g' ⟨l', hlab, hsome', hTl', hedge⟩
        refine Or.inr ⟨l', hlab, ⟨hsome', hTl'⟩, ?_⟩
        rcases hedge with h | h | hne
        · exact .inl (hdec l l' hidx (.inl h))
        · exact .inl (hdec l l' hidx (.inr h))
        · exact .inr fun ⟨_, h1, h2⟩ => hne ⟨h1, h2⟩

end Kraken.Promising.SLR.EnvG.MsQueue

#print axioms MachineWP.PartialTripleEnv.of_runAt
#print axioms MachineWP.PartialTripleEnv.of_runAtT
#print axioms Kraken.Promising.SLR.EnvG.MsQueue.cfgEnv_partial_rank_at
