/-
Part 5: **the partial control-flow rule with a label
rank** (`cfgEnv_partial_rank`), for `msqueue1.kl`'s dequeuer.

`MachineWP.cfgEnv_partial`'s zero-step guard (`Program.EdgeSafe`) lets a jump
that does not change the state go only forward in the text. The dequeuer's
block `deq1a_ne` starts with `cbz x5, deq1a`: a backward jump taken in zero
steps (when `x5 = 0`, which is reachable). `cfgEnv_partial_rank` orders the
labels lexicographically by a rank `ρ` first, then by the text: such a jump
is guarded by a smaller rank (`ρ deq1a < ρ deq1a_ne`). Every exit, the
fall-through included, carries the guard `EdgeRank`. Same proof as
`cfgEnv_partial` (`Program.linkEnv_partial` with the lex measure).
`cfg_cases_env_rank` is `cfg_cases_env` that also evaluates `EdgeRank`'s
text indices.

A hoist candidate: `cfgEnv_partial` is the instance `ρ = 0` (up to the
fall-through guard, which `ρ = 0` discharges by the text order).
-/
import Kraken.AArch64.EnvCfg

open Kraken
open Std.WP

namespace Kraken.Promising.SLR.EnvG.MsQueue

/-- **The rank guard** from a block entered at `l` in `(s₀, g₀)` to `l'`
reached in `(s, g)`: a smaller rank, or the same rank and later in the text,
or the state is not the entry state. -/
abbrev EdgeRank {env : SharedEnv} (p : Program) (ρ : Label → Nat) (l : Label) (s₀ : MachineData)
    (g₀ : env.State) (l' : Label) (s : MachineData) (g : env.State) : Prop :=
  ρ l' < ρ l ∨ (ρ l' = ρ l ∧ Program.blockIdx p l < Program.blockIdx p l') ∨ ¬ (s = s₀ ∧ g = g₀)

theorem blockAt_entry' {p p' : Program} {l₀ : Label} (hp : p = Directive.label l₀ :: p') :
    (Program.blockAt p l₀).isSome := by
  rw [hp]
  show (Program.blockAtAux (Program.view (Directive.label l₀ :: p')).2 l₀).isSome = true
  simp [Program.view, Program.blockAtAux]

open MachineWP in
/-- **The partial control-flow rule with a label rank** (`ρ`): as
`MachineWP.cfgEnv_partial`, with every exit (fall-through and jumps) guarded
by `EdgeRank`. -/
theorem cfgEnv_partial_rank [CodeEnv] {env : SharedEnv} {p p' : Program}
    {P : MachineData → env.State → Prop} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} {l₀ : Label}
    (T : Label → MachineData → env.State → Prop) (ρ : Label → Nat)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ (s₀ : MachineData) (g₀ : env.State),
      ⦃ fun s g => T l s g ∧ s = s₀ ∧ g = g₀ ⦄ (⟨blk.body⟩ : EnvProgram env)
      ⦃ (match blk.next with
         | some l' => fun _ s g => T l' s g ∧ EdgeRank p ρ l s₀ g₀ l' s g
         | none => fun _ => Q);
        Table.ofLabelsEnv (fun l' s g => (Program.blockAt p l').isSome ∧ T l' s g
          ∧ EdgeRank p ρ l s₀ g₀ l' s g) ⦄)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.Placed p l₀ := by
      first
        | assumption
        | exact Program.placed_of_layout (by decide) (by rfl) (by decide))
    (hP : P = T l₀ := by rfl) :
    PartialTripleEnv env P p Q E := by
  subst hP
  have hnd := hwf.nodup
  intro s g hT pc hplace
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
    (post := fun x => x.1.2 = cenv.after pc p ∧ Q x.1.1 x.2)
    (fun l => (Program.blockAt p l).elim [] (·.body))
    (fun l => (_root_.Executable.labels cenv).label l)
    (fun l s g => (Program.blockAt p l).isSome ∧ T l s g)
    (fun j i => ν j < ν i) (measure ν).wf ?_ ?_
  · have hrun := key l₀ s g ⟨blockAt_entry' hp, hT⟩
    rw [hpl.entry pc hplace] at hrun
    exact hrun.mono fun st hst => Or.inl hst
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
          have hend : cenv.after ((_root_.Executable.labels cenv).label l) blk.body = cenv.after pc p := by
            rw [hpl.last l blk hb hnx, hpl.entry pc hplace]
          exact Or.inl ⟨hend, hq⟩
      · rintro a s' g' ⟨l', hlab, hsome', hTl', hedge⟩
        refine Or.inr ⟨l', hlab, ⟨hsome', hTl'⟩, ?_⟩
        rcases hedge with h | h | hne
        · exact .inl (hdec l l' hidx (.inl h))
        · exact .inl (hdec l l' hidx (.inr h))
        · exact .inr fun ⟨_, h1, h2⟩ => hne ⟨h1, h2⟩

/-- `cfg_cases_env` for `cfgEnv_partial_rank`: one goal per block, the text
indices of `EdgeRank` evaluated. -/
macro "cfg_cases_env_rank" "[" ids:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    (intro l blk hblk
     cfg_view hblk as hview
     have hlabels := congrArg (List.map (·.1)) hview
     simp only [List.map_cons, List.map_nil] at hlabels
     rw [Program.blockAt, hview] at hblk
     clear hview
     simp only [$ids,*, Program.blockAtAux, List.head?_cons, List.head?_nil, Option.map_some,
       Option.map_none] at hblk
     repeat' split at hblk
     all_goals subst_vars
     all_goals simp only [Option.some.injEq, reduceCtorEq] at hblk
     all_goals subst hblk
     all_goals simp only [EdgeRank, Program.isSome_blockAt, Program.blockIdx_eq_view, hlabels]
     all_goals clear hlabels))

end Kraken.Promising.SLR.EnvG.MsQueue
