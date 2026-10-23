/-
Control flow over the environment-aware wp, AArch64 (design note
`Kraken/Promising/EnvWP.md` §8). Copied from x64's
`Kraken/EnvCfg.lean`, over AArch64's `Program`, `cfg` placement facts
(`Kraken.AArch64.WP.Cfg`) and `EnvProgram` (`Kraken.AArch64.EnvVCGen`).

`MachineWP.cfg` (in `Kraken.AArch64.WP.Cfg`) proves a triple on a labeled program
from one triple per block, by `Program.link`. Here is the same over `wpEnv`,
where every predicate also reads the environment state `g`:

- **Total correctness**, `MachineWP.cfgEnv`: the table `T` and the variant
  `var` read `(s, g)`; each block is a `vcgen` triple on
  `⟨blk.body⟩ : EnvProgram env`; a back edge must decrease the variant
  (`Program.EdgeLtEnv`). Built on `Program.linkEnv`. The conclusion is a
  `TripleEnv`, so `Program.instrStepEnv_of_tripleEnv` and `env_link_halt`
  apply. This serves loops whose exit the thread controls, and retry loops in
  an environment where the retry cannot fail forever (x64 `lock cmpxchg` in
  `lastWrite`: the compare after a load of an unchanged location succeeds).
- **Partial correctness**, `MachineWP.cfgEnv_partial`: no variant. The
  conclusion is a `PartialTripleEnv` (`Safely` in place of `Eventually`):
  every run either reaches the postcondition or the exit, or runs forever.
  Built on `Program.linkEnv_partial`. This serves retry loops in every
  environment (a CAS that keeps losing, an AArch64 store-exclusive that keeps
  failing, which even `lastWrite` allows).
  `Program.instrStepEnv_of_partialTripleEnv` reads it at the machine, and
  `env_link_halt_safe` (`Kraken.Promising.EnvLinkSafeX64`/`…AArch64`) carries
  it to the Promising machine for the runs that halt.

**The zero-step guard.** A block's triple may hold by an exit taken in zero
steps (`Eventually.done` with the exit predicate at the block's own entry).
Without a variant, blocks exiting into each other that way would prove
anything (`Program.unguardedLinkEnvPartial_false`). So a jump exit of the partial
rule must go forward in the text or leave the block's entry state
(`Program.EdgeSafe`). A zero-step exit lands exactly on the entry state, so it
must go forward, and forward chains are finite. A retry loop discharges the
guard because its environment state changed. `SharedEnv.counted` adds a
ghost access counter to any environment for the case where nothing else
changes (a failed store-exclusive); `Safely` judgments in `counted env` project
back to `env` (`MachineWP.PartialTripleEnv.uncount`).

`cfg_cases_env [p]` splits either rule's block obligation into one goal per
block, as `cfg_cases` does for `cfg`.
-/
import Kraken.AArch64.EnvVCGen
import Kraken.AArch64.WP.Cfg
import Kraken.AArch64.WP.RulesCF
import Kraken.SharedEnvCounted
import Kraken.Safely

open Kraken
open Std.WP
open Lean.Order

/-! ## Linking fragments -/

/-- Where a step out of fragment `i`, entered in `(s₀, g₀)`, may land: the
global postcondition, or another fragment's entry with its invariant and a
smaller measure. `Program.Cont` with the environment state. -/
def Program.ContEnv {ι : Type} {env : SharedEnv} (post : MachineState × env.State → Prop)
    (entry : ι → Int64) (T : ι → MachineData → env.State → Prop)
    (r : ι × MachineData × env.State → ι × MachineData × env.State → Prop)
    (i : ι) (s₀ : MachineData) (g₀ : env.State) (a : Int64) (s : MachineData) (g : env.State) : Prop :=
  post ((s, a), g) ∨ ∃ j, entry j = a ∧ T j s g ∧ r (j, s, g) (i, s₀, g₀)

open MachineWP in
/-- `Program.link` with the environment: total correctness of finitely or
infinitely many fragments tied by a well-founded order on index and state. -/
theorem Program.linkEnv [CodeEnv] {env : SharedEnv} {ι : Type} {post : MachineState × env.State → Prop}
    (frag : ι → Program) (entry : ι → Int64) (T : ι → MachineData → env.State → Prop)
    (r : ι × MachineData × env.State → ι × MachineData × env.State → Prop) (hwf : WellFounded r)
    (hplace : ∀ i, cenv.sits (entry i) (frag i))
    (hfrag : ∀ i s₀ g₀,
      TripleEnv env (fun s g => T i s g ∧ s = s₀ ∧ g = g₀) (frag i)
        (fun s g => Program.ContEnv post entry T r i s₀ g₀ (cenv.after (entry i) (frag i)) s g)
        (fun a s g => Program.ContEnv post entry T r i s₀ g₀ a s g)) :
    ∀ i s g, T i s g → Eventually (cenv.instrStepEnv env) post ((s, entry i), g) := by
  suffices h : ∀ x : ι × MachineData × env.State, T x.1 x.2.1 x.2.2 →
      Eventually (cenv.instrStepEnv env) post ((x.2.1, entry x.1), x.2.2) from
    fun i s g hT => h (i, s, g) hT
  intro x
  induction x using hwf.induction with
  | _ x ih =>
    intro hT
    have hev := hfrag x.1 x.2.1 x.2.2 x.2.1 x.2.2 ⟨hT, rfl, rfl⟩ (entry x.1) (hplace x.1)
    refine eventually_trans _ _ _ _ hev ?_
    rintro ⟨⟨s', a⟩, g'⟩ hc
    have hc' : Program.ContEnv post entry T r x.1 x.2.1 x.2.2 a s' g' := by
      rcases hc with ⟨ha, hc⟩ | hc
      · dsimp only at ha hc
        rw [ha]
        exact hc
      · exact hc
    rcases hc' with hp | ⟨j, hj, hTj, hr⟩
    · exact .done _ hp
    · rw [← hj]
      exact ih (j, s', g') hr hTj

/-- Where a step out of fragment `i`, entered in `(s₀, g₀)`, may land, for
partial correctness: the global postcondition, or another fragment's entry
with its invariant, along a smaller index **or** away from the entry state
`(entry i, s₀, g₀)` (the zero-step guard). -/
def Program.ContSafe {ι : Type} {env : SharedEnv} (post : MachineState × env.State → Prop)
    (entry : ι → Int64) (T : ι → MachineData → env.State → Prop) (r : ι → ι → Prop)
    (i : ι) (s₀ : MachineData) (g₀ : env.State) (a : Int64) (s : MachineData) (g : env.State) : Prop :=
  post ((s, a), g) ∨ ∃ j, entry j = a ∧ T j s g ∧ (r j i ∨ ¬ (a = entry i ∧ s = s₀ ∧ g = g₀))

open MachineWP in
/-- **Partial-correctness link.** Fragments tied by any jumps: each run either
reaches `post` or runs forever. The well-founded order `r` on indices is
needed only for exits that do not leave the entry state, which is where a
zero-step exit lands. -/
theorem Program.linkEnv_partial [CodeEnv] {env : SharedEnv} {ι : Type}
    {post : MachineState × env.State → Prop}
    (frag : ι → Program) (entry : ι → Int64) (T : ι → MachineData → env.State → Prop)
    (r : ι → ι → Prop) (hwf : WellFounded r)
    (hplace : ∀ i, cenv.sits (entry i) (frag i))
    (hfrag : ∀ i s₀ g₀,
      TripleEnv env (fun s g => T i s g ∧ s = s₀ ∧ g = g₀) (frag i)
        (fun s g => Program.ContSafe post entry T r i s₀ g₀ (cenv.after (entry i) (frag i)) s g)
        (fun a s g => Program.ContSafe post entry T r i s₀ g₀ a s g)) :
    ∀ i s g, T i s g → Safely (cenv.instrStepEnv env) post ((s, entry i), g) := by
  -- the invariant: on the way (in finitely many steps) to `post` or to a
  -- fragment's entry with its table entry
  let C : MachineState × env.State → Prop := fun x => post x ∨ ∃ j, x.1.2 = entry j ∧ T j x.1.1 x.2
  have hA : ∀ j s g, T j s g → post ((s, entry j), g) ∨
      ∃ R, cenv.instrStepEnv env ((s, entry j), g) R ∧
        ∀ z, R z → Eventually (cenv.instrStepEnv env) C z := by
    intro j
    induction j using hwf.induction with
    | _ j ih =>
      intro s g hT
      have hev := hfrag j s g s g ⟨hT, rfl, rfl⟩ (entry j) (hplace j)
      have hwk : ∀ x : MachineState × env.State,
          ((x.1.2 = cenv.after (entry j) (frag j) ∧
              Program.ContSafe post entry T r j s g (cenv.after (entry j) (frag j)) x.1.1 x.2) ∨
            Program.ContSafe post entry T r j s g x.1.2 x.1.1 x.2) → C x := by
        rintro ⟨⟨s', a⟩, g'⟩ hc
        have hc' : Program.ContSafe post entry T r j s g a s' g' := by
          rcases hc with ⟨ha, hc⟩ | hc
          · dsimp only at ha hc
            rw [ha]
            exact hc
          · exact hc
        rcases hc' with hp | ⟨k, hk, hTk, -⟩
        · exact .inl hp
        · exact .inr ⟨k, hk.symm, hTk⟩
      cases hev with
      | done _ hc =>
        have hc' : Program.ContSafe post entry T r j s g (entry j) s g := by
          rcases hc with ⟨ha, hc⟩ | hc
          · dsimp only at ha hc
            rw [ha]
            exact hc
          · exact hc
        rcases hc' with hp | ⟨k, hk, hTk, hr | hne⟩
        · exact .inl hp
        · rw [← hk]
          exact ih k hr s g hTk
        · exact absurd ⟨rfl, rfl, rfl⟩ hne
      | step _ mid hT hmid =>
        exact .inr ⟨mid, hT, fun z hz => eventually_weaken _ _ _ _ hwk (hmid z hz)⟩
  intro i s g hT
  refine ⟨Eventually (cenv.instrStepEnv env) C, .done _ (.inr ⟨i, rfl, hT⟩), ?_⟩
  intro y hy
  cases hy with
  | done _ hc =>
    rcases hc with hp | ⟨j, hj, hTj⟩
    · exact .inl hp
    · obtain ⟨⟨s', pc⟩, g'⟩ := y
      dsimp only at hj hTj
      subst hj
      exact hA j s' g' hTj
  | step _ mid hT hmid => exact .inr ⟨mid, hT, hmid⟩

/-! ## The zero-step guard is needed

`Program.linkEnv_partial` without the guard (any exit to a fragment's entry
with its table entry) is unsound: one empty fragment falls through, in zero
steps, to its own entry, so its triple holds for any table, and the rule would
then give `Safely` of `False` where the machine cannot step. -/

open MachineWP in
/-- `Program.linkEnv_partial` with the zero-step guard dropped. -/
def Program.UnguardedLinkEnvPartial [CodeEnv] (env : SharedEnv) : Prop :=
  ∀ {ι : Type} {post : MachineState × env.State → Prop}
    (frag : ι → Program) (entry : ι → Int64) (T : ι → MachineData → env.State → Prop),
    (∀ i, cenv.sits (entry i) (frag i)) →
    (∀ i s₀ g₀,
      TripleEnv env (fun s g => T i s g ∧ s = s₀ ∧ g = g₀) (frag i)
        (fun s g => post ((s, cenv.after (entry i) (frag i)), g) ∨
          ∃ j, entry j = cenv.after (entry i) (frag i) ∧ T j s g)
        (fun a s g => post ((s, a), g) ∨ ∃ j, entry j = a ∧ T j s g)) →
    ∀ i s g, T i s g → Safely (cenv.instrStepEnv env) post ((s, entry i), g)

/-- **The unguarded rule is false** in any code where some address `a` has no
instruction: the empty fragment at `a`, with the table `True` and the
postcondition `False`. -/
theorem Program.unguardedLinkEnvPartial_false [CodeEnv] (env : SharedEnv) (a : Int64)
    (s : MachineData) (g : env.State) (hstuck : ∀ x R, x.1.2 = a → ¬ cenv.instrStepEnv env x R) :
    ¬ Program.UnguardedLinkEnvPartial env := by
  intro h
  have hs := h (ι := Unit) (post := fun _ => False) (fun _ => []) (fun _ => a) (fun _ _ _ => True)
    (fun _ => trivial)
    (fun _ _ _ s' g' _ pc _ => .done _ (.inl ⟨rfl, .inr ⟨(), rfl, trivial⟩⟩)) () s g trivial
  exact hs.post_of_stuck fun R => hstuck _ R rfl

/-! ## The control-flow rules -/

/-- A label-keyed table with the environment state, read at an address. -/
def Table.ofLabelsEnv [CodeEnv] {env : SharedEnv} (tl : Label → MachineData → env.State → Prop) :
    Int64 → MachineData → env.State → Prop :=
  fun a s g => ∃ l, (_root_.Executable.labels cenv).label l = a ∧ tl l s g

@[grind ←] theorem Table.ofLabelsEnv_at [CodeEnv] {env : SharedEnv}
    {tl : Label → MachineData → env.State → Prop} {l : Label} {s : MachineData} {g : env.State}
    (h : tl l s g) : Table.ofLabelsEnv tl ((_root_.Executable.labels cenv).label l) s g :=
  ⟨l, rfl, h⟩

/-- `Program.EdgeLt` with the environment state: the variant decreased, or it
is unchanged and the target sits later in the text. -/
abbrev Program.EdgeLtEnv {env : SharedEnv} (p : Program) (var : Label → MachineData → env.State → Nat)
    (l : Label) (n : Nat) (l' : Label) (s : MachineData) (g : env.State) : Prop :=
  var l' s g < n ∨ (var l' s g = n ∧ Program.blockIdx p l < Program.blockIdx p l')

/-- The zero-step guard of the partial rule, from a block entered at `l` in
`(s₀, g₀)` to a jump target `l'` reached in `(s, g)`: the target sits later in
the text, or the state is not the entry state. -/
abbrev Program.EdgeSafe {env : SharedEnv} (p : Program) (l : Label) (s₀ : MachineData) (g₀ : env.State)
    (l' : Label) (s : MachineData) (g : env.State) : Prop :=
  Program.blockIdx p l < Program.blockIdx p l' ∨ ¬ (s = s₀ ∧ g = g₀)

/-- The lex order of `cfgEnv`, in one number. -/
private def cfgMeasureEnv {env : SharedEnv} (p : Program) (var : Label → MachineData → env.State → Nat)
    (x : Label × MachineData × env.State) : Nat :=
  var x.1 x.2.1 x.2.2 * ((Program.view p).2.length + 1)
    + ((Program.view p).2.length - Program.blockIdx p x.1)

/-- The entry label has a block. -/
private theorem blockAt_entry {p p' : Program} {l₀ : Label} (hp : p = Directive.label l₀ :: p') :
    (Program.blockAt p l₀).isSome := by
  rw [hp]
  show (Program.blockAtAux (Program.view (Directive.label l₀ :: p')).2 l₀).isSome = true
  simp [Program.view, Program.blockAtAux]

open MachineWP in
/-- **The control-flow rule with the environment**, total correctness. One
table `T`, one variant `var`, both reading the environment state; one
`EnvProgram` triple per block of `Program.blockAt`, entered with its table
entry and the variant snapshotted. It falls into the next block with the entry
there and the variant not increased; a jump exit lands on a mapped table entry
along `Program.EdgeLtEnv`. -/
theorem MachineWP.cfgEnv [CodeEnv] {env : SharedEnv} {p p' : Program}
    {P : MachineData → env.State → Prop} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} {l₀ : Label}
    (T : Label → MachineData → env.State → Prop)
    (var : Label → MachineData → env.State → Nat := fun _ _ _ => 0)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s g => T l s g ∧ var l s g = n ⦄ (⟨blk.body⟩ : EnvProgram env)
      ⦃ (match blk.next with
         | some l' => fun _ s g => T l' s g ∧ var l' s g ≤ n
         | none => fun _ => Q);
        Table.ofLabelsEnv (fun l' s g => (Program.blockAt p l').isSome ∧ T l' s g
          ∧ Program.EdgeLtEnv p var l n l' s g) ⦄)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.Placed p l₀ := by
      first
        | assumption
        | exact Program.placed_of_layout (by decide) (by rfl) (by decide))
    (hP : P = T l₀ := by rfl) :
    TripleEnv env P p Q E := by
  subst hP
  have hnd := hwf.nodup
  intro s g hT pc hplace
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length := Program.blockIdx_le p
  have key := Program.linkEnv (env := env) (post := fun x => x.1.2 = cenv.after pc p ∧ Q x.1.1 x.2)
    (fun l => (Program.blockAt p l).elim [] (·.body))
    (fun l => (_root_.Executable.labels cenv).label l)
    (fun l s g => (Program.blockAt p l).isSome ∧ T l s g)
    (fun x y => cfgMeasureEnv p var x < cfgMeasureEnv p var y)
    (measure (cfgMeasureEnv p var)).wf ?_ ?_
  · have hrun := key l₀ s g ⟨blockAt_entry hp, hT⟩
    rw [hpl.entry pc hplace] at hrun
    exact eventually_weaken _ _ _ _ (fun st hst => Or.inl hst) hrun
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
      have hw := (hblocks l blk hb (var l s g)).le_wp s g ⟨hTl, rfl⟩
      rw [wpEnv_eq] at hw
      refine Executable.wpEnv_mono ?_ ?_ hw
      · intro s' g' hq
        cases hnx : blk.next with
        | some l' =>
          rw [hnx] at hq
          obtain ⟨hTl', hvar⟩ := hq
          obtain ⟨hsome', hidx'⟩ := Program.blockAt_next hnd hb hnx
          refine Or.inr ⟨l', (hpl.next l blk l' hb hnx).symm, ⟨hsome', hTl'⟩, ?_⟩
          have hmul : var l' s' g' * ((Program.view p).2.length + 1)
              ≤ var l s g * ((Program.view p).2.length + 1) := Nat.mul_le_mul_right _ hvar
          simp only [cfgMeasureEnv]
          omega
        | none =>
          rw [hnx] at hq
          have hend : cenv.after ((_root_.Executable.labels cenv).label l) blk.body = cenv.after pc p := by
            rw [hpl.last l blk hb hnx, hpl.entry pc hplace]
          exact Or.inl ⟨hend, hq⟩
      · rintro a s' g' ⟨l', hlab, hsome', hTl', hedge⟩
        refine Or.inr ⟨l', hlab, ⟨hsome', hTl'⟩, ?_⟩
        have hle' : Program.blockIdx p l' ≤ (Program.view p).2.length := hK l'
        simp only [cfgMeasureEnv]
        rcases hedge with hlt | ⟨heq, hij⟩
        · have hmul : (var l' s' g' + 1) * ((Program.view p).2.length + 1)
              ≤ var l s g * ((Program.view p).2.length + 1) := Nat.mul_le_mul_right _ hlt
          have hsucc : (var l' s' g' + 1) * ((Program.view p).2.length + 1)
              = var l' s' g' * ((Program.view p).2.length + 1)
                + ((Program.view p).2.length + 1) := Nat.succ_mul _ _
          omega
        · rw [heq]
          omega

namespace MachineWP

/-- A partial-correctness triple with the environment, on the ambient code:
from every state and environment state satisfying `P`, every run of `q`
falls through with `Q`, exits with `E`, or runs forever (`Safely`). -/
def PartialTripleEnv [CodeEnv] (env : SharedEnv) (P : MachineData → env.State → Prop) (q : Program)
    (Q : MachineData → env.State → Prop) (E : Int64 → MachineData → env.State → Prop) : Prop :=
  ∀ s g, P s g → ∀ pc, cenv.sits pc q →
    Safely (cenv.instrStepEnv env)
      (fun x => (x.1.2 = cenv.after pc q ∧ Q x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2) ((s, pc), g)

/-- Total correctness implies partial correctness. -/
theorem TripleEnv.partial [CodeEnv] {env : SharedEnv} {P : MachineData → env.State → Prop}
    {q : Program} {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    (h : TripleEnv env P q Q E) : PartialTripleEnv env P q Q E :=
  fun s g hp pc hpl => Safely.of_eventually (h s g hp pc hpl)

end MachineWP

open MachineWP in
/-- **The control-flow rule with the environment**, partial correctness. One
table `T` reading the environment state, no variant; one `EnvProgram` triple
per block, entered with its table entry in the snapshotted state `(s₀, g₀)`.
It falls into the next block with the entry there; a jump exit lands on a
mapped table entry, forward in the text or away from the entry state
(`Program.EdgeSafe`, the zero-step guard). -/
theorem MachineWP.cfgEnv_partial [CodeEnv] {env : SharedEnv} {p p' : Program}
    {P : MachineData → env.State → Prop} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} {l₀ : Label}
    (T : Label → MachineData → env.State → Prop)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ (s₀ : MachineData) (g₀ : env.State),
      ⦃ fun s g => T l s g ∧ s = s₀ ∧ g = g₀ ⦄ (⟨blk.body⟩ : EnvProgram env)
      ⦃ (match blk.next with
         | some l' => fun _ s g => T l' s g
         | none => fun _ => Q);
        Table.ofLabelsEnv (fun l' s g => (Program.blockAt p l').isSome ∧ T l' s g
          ∧ Program.EdgeSafe p l s₀ g₀ l' s g) ⦄)
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
  let μ : Label → Nat := fun l => (Program.view p).2.length - Program.blockIdx p l
  have key := Program.linkEnv_partial (env := env)
    (post := fun x => x.1.2 = cenv.after pc p ∧ Q x.1.1 x.2)
    (fun l => (Program.blockAt p l).elim [] (·.body))
    (fun l => (_root_.Executable.labels cenv).label l)
    (fun l s g => (Program.blockAt p l).isSome ∧ T l s g)
    (fun j i => μ j < μ i) (measure μ).wf ?_ ?_
  · have hrun := key l₀ s g ⟨blockAt_entry hp, hT⟩
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
          obtain ⟨hsome', hidx'⟩ := Program.blockAt_next hnd hb hnx
          refine Or.inr ⟨l', (hpl.next l blk l' hb hnx).symm, ⟨hsome', hq⟩, .inl ?_⟩
          simp only [μ]
          omega
        | none =>
          rw [hnx] at hq
          have hend : cenv.after ((_root_.Executable.labels cenv).label l) blk.body = cenv.after pc p := by
            rw [hpl.last l blk hb hnx, hpl.entry pc hplace]
          exact Or.inl ⟨hend, hq⟩
      · rintro a s' g' ⟨l', hlab, hsome', hTl', hedge⟩
        refine Or.inr ⟨l', hlab, ⟨hsome', hTl'⟩, ?_⟩
        rcases hedge with hlt | hne
        · have hle' : Program.blockIdx p l' ≤ (Program.view p).2.length := hK l'
          refine .inl ?_
          simp only [μ]
          omega
        · exact .inr fun ⟨_, h1, h2⟩ => hne ⟨h1, h2⟩

/-! ## A partial triple at the machine -/

/-- A partial triple with the environment on a laid-out program, read at the
machine: from the start address every run, its environment state threaded
through, reaches the end of the text with `Q`, stops at an address satisfying
`E`, or runs forever. The partial twin of `Program.instrStepEnv_of_tripleEnv`. -/
theorem Program.instrStepEnv_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {env : SharedEnv} {P : MachineData → env.State → Prop}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    {s : MachineData} {g : env.State}
    (ht : MachineWP.PartialTripleEnv env P p Q E) (hs : P s g)
    (henv : cenv = layout p := by rfl) :
    Safely ((layout p).instrStepEnv env)
      (fun x => (x.1.2 = (layout p).addrOf p.length ∧ Q x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2)
      ((s, Kraken.Layout.start Directive), g) := by
  have h : ∀ pc, (layout p).sits pc p → Safely ((layout p).instrStepEnv env)
      (fun x => (x.1.2 = (layout p).after pc p ∧ Q x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2) ((s, pc), g) :=
    henv ▸ ht s g hs
  obtain ⟨hsits, hafter⟩ := Executable.walk_addrOf (p := p) p [] 0 (by simp)
  rw [Nat.zero_add] at hafter
  have hev := h ((layout p).addrOf 0) hsits
  rwa [hafter, Executable.addrOf_zero, Layout.apply_fst] at hev

/-! ## Projecting the ghost counter away -/

/-- A `CASP` reading in `SharedEnv.counted env` is one in `env`, the counter
forgotten (each half's `rmw` ticks it once). -/
theorem Kraken.SharedEnv.CaspEnv.uncount {env : SharedEnv} {k : RmwKind} {addr : BitVec 64}
    {w : MemWidth} {cmp1 cmp2 new1 new2 : w.type} {g : (SharedEnv.counted env).State}
    {K : w.type → w.type → (SharedEnv.counted env).State → Prop}
    (h : (SharedEnv.counted env).CaspEnv k addr w cmp1 cmp2 new1 new2 g K) :
    env.CaspEnv k addr w cmp1 cmp2 new1 new2 g.1 (fun o₁ o₂ g' => ∃ n, K o₁ o₂ (g', n)) := by
  intro succ rev
  have h := h succ rev
  cases rev <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h ⊢ <;>
    exact ⟨h.1, fun v g₁ hs => ⟨(h.2 v (g₁, g.2 + 1) ⟨hs, rfl⟩).1, fun v' g₂ hs' hc =>
      ⟨_, (h.2 v (g₁, g.2 + 1) ⟨hs, rfl⟩).2 v' (g₂, g.2 + 1 + 1) ⟨hs', rfl⟩ hc⟩⟩⟩

/-- An `AllEnv` judgment in `SharedEnv.counted env` is one in `env`, the
counter forgotten. -/
theorem Effects.AllEnv.uncount {env : SharedEnv}
    {post : MachineState → (SharedEnv.counted env).State → Prop} (e : Effects) :
    ∀ g : (SharedEnv.counted env).State, e.AllEnv (SharedEnv.counted env) g post →
      e.AllEnv env g.1 (fun s g' => ∃ n, post s (g', n)) := by
  induction e with
  | done a => exact fun g h => ⟨g.2, h⟩
  | unimplemented => exact fun _ h => h
  | syscall => exact fun _ h => h
  | unaligned_sp => exact fun _ h => h
  | nonmem_load dmem addr w ret ih =>
    exact fun g h => ⟨h.1, fun v g' hs => ih _ _ (g', g.2 + 1) (h.2 v (g', g.2 + 1) ⟨hs, rfl⟩)⟩
  | nonmem_store dmem addr v ret ih =>
    exact fun g h => ⟨h.1, fun b g' hs => ih _ (g', g.2 + 1) (h.2 b (g', g.2 + 1) ⟨hs, rfl⟩)⟩
  | undefined ret ih => exact fun g h v => ih v g (h v)
  | require_read_access _ _ ok ih => exact fun g h => ih () g h
  | require_write_access _ _ ok ih => exact fun g h => ih () g h
  | require_exec_access _ ok ih => exact fun g h => ih () g h
  | sync_load k xcl dmem addr w ret ih =>
    exact fun g h => ⟨h.1, fun v g' hs => ih _ _ (g', g.2 + 1) (h.2 v (g', g.2 + 1) ⟨hs, rfl⟩)⟩
  | sync_store k xcl dmem addr v ret ih =>
    exact fun g h => ⟨h.1, fun b g' hs => ih _ _ (g', g.2 + 1) (h.2 b (g', g.2 + 1) ⟨hs, rfl⟩)⟩
  | rmw k nr dmem addr w op ret ih =>
    exact fun g h => ⟨h.1, fun v g' hs => ih _ _ (g', g.2 + 1) (h.2 v (g', g.2 + 1) ⟨hs, rfl⟩)⟩
  -- no environment rule for an exclusive pair with both halves shared: `AllEnv` is `False`
  | sync_load_pair => exact fun _ h => h.elim
  | sync_store_pair => exact fun _ h => h.elim
  | rmw_pair k dmem addr cmp1 cmp2 new1 new2 ret ih =>
    exact fun g h => SharedEnv.CaspEnv.mono (fun o₁ o₂ g' ⟨n, hn⟩ => ih o₁ o₂ dmem (g', n) hn)
      (SharedEnv.CaspEnv.uncount h)
  | fence k ok ih => exact fun g h => ⟨h.1, fun g' hs => ih () (g', g.2) (h.2 (g', g.2) ⟨hs, rfl⟩)⟩

/-- One instruction in `SharedEnv.counted env` is one in `env`, the counter
forgotten. -/
theorem Kraken.Executable.instrStepEnv_uncount {e : Kraken.Executable Directive} {env : SharedEnv}
    {x : MachineState × (SharedEnv.counted env).State}
    {R : MachineState × (SharedEnv.counted env).State → Prop}
    (h : e.instrStepEnv (SharedEnv.counted env) x R) :
    e.instrStepEnv env (x.1, x.2.1) (fun y => ∃ x', y = (x'.1, x'.2.1) ∧ R x') := by
  obtain ⟨d, z, rest, hcode, hstep⟩ := h
  refine ⟨d, z, rest, hcode, ?_⟩
  rcases hstep with h | h
  · exact .inl (Effects.AllEnv.mono (fun _ _ ⟨n, hn⟩ => ⟨(_, (_, n)), rfl, hn⟩) _ _
      (Effects.AllEnv.uncount _ _ h))
  · exact .inr (Effects.AllEnv.mono (fun _ _ ⟨n, hn⟩ => ⟨(_, (_, n)), rfl, hn⟩) _ _
      (Effects.AllEnv.uncount _ _ h))

/-- A partial triple in `SharedEnv.counted env` is one in `env`: the ghost
counter is existentially forgotten in the pre- and postconditions. -/
theorem MachineWP.PartialTripleEnv.uncount [CodeEnv] {env : SharedEnv}
    {P : MachineData → (SharedEnv.counted env).State → Prop} {q : Program}
    {Q : MachineData → (SharedEnv.counted env).State → Prop}
    {E : Int64 → MachineData → (SharedEnv.counted env).State → Prop}
    (h : MachineWP.PartialTripleEnv (SharedEnv.counted env) P q Q E) :
    MachineWP.PartialTripleEnv env (fun s g => ∃ n, P s (g, n)) q (fun s g => ∃ n, Q s (g, n))
      (fun a s g => ∃ n, E a s (g, n)) := by
  rintro s g ⟨n, hp⟩ pc hpl
  have hs := (h s (g, n) hp pc hpl).sim
    (fun (x : MachineState × (SharedEnv.counted env).State) (y : MachineState × env.State) =>
      y = (x.1, x.2.1))
    (fun x y R hxy hT => hxy ▸ Executable.instrStepEnv_uncount hT) rfl
  refine hs.mono ?_
  rintro y ⟨x', rfl, hx⟩
  rcases hx with ⟨ha, hq⟩ | he
  · exact .inl ⟨ha, x'.2.2, hq⟩
  · exact .inr ⟨x'.2.2, he⟩

/-! ## Splitting the block obligations -/

/-- Split the block obligation of `cfgEnv` or `cfgEnv_partial` into one goal
per block, as `cfg_cases` does for `cfg`. It stops before the snapshot
binders (`∀ n` or `∀ s₀ g₀`): introduce them in each goal. -/
macro "cfg_cases_env" "[" ids:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
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
     all_goals simp only [Program.EdgeLtEnv, Program.EdgeSafe, Program.isSome_blockAt,
       Program.blockIdx_eq_view, hlabels]
     all_goals clear hlabels))
