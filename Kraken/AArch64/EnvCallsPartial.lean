/-
**Calls under partial correctness, AArch64**. Generic (no pilot-specific
names), a candidate for hoisting next to `AArch64/EnvCalls.lean`.

`MachineWP.call_specEnv` and `fun_specEnv_from_label` (`AArch64/EnvCalls.lean`)
take the callee's run as a `TripleEnv`, i.e. *total* correctness
(`Eventually`). A lock-free `push`/`pop` has a CAS retry loop that another
thread may make fail forever, so its only specification is partial
(`Safely`, as `PartialTripleEnv`/`cfgEnv_partial`). This file supplies the
partial counterparts that the lowered Treiber callers need:

- `Safely.bind`: sequencing of two `Safely` runs.
- `Executable.sits_append`: placement of `q ++ p`.
- `PartialWpEnv`: the partial wp of a fragment at a state (`PartialTripleEnv` at a
  point); `PartialWpEnv.nil`, `PartialWpEnv.of_wpEnv` (a total prefix, e.g. by `vcgen`, then a
  partial rest).
- `FunSpecPartialEnv`: a function's partial specification at its entry address,
  `ProcSpecEnv` with `Safely` in place of `Eventually`: from every return
  address `ra` and entry state satisfying `Pre`, every run returns to `ra`
  with `Post` or runs forever.
- `PartialWpEnv.call`: **the partial call rule** (`bl l` through a `FunSpecPartialEnv` at the
  label's address).
- `cfgEnv_partial_fun`: `cfgEnv_partial_at` for a *function* fragment whose
  blocks may also leave by an arbitrary exit `E` (the `ret`), and never fall
  through its last block. `cfgEnv_partial(_at)` only admit jumps to the
  fragment's own labels, so a `ret` cannot be expressed there.
-/
import Kraken.AArch64.EnvCalls
import Kraken.Promising.SLR.EnvG.A64MaskCfg

open Kraken
open Std.WP
open MachineWP


/-- **Sequencing of `Safely`**: a partial run into states from which the
rest is partially correct. -/
theorem Safely.bind {State : Type} {trans : State → (State → Prop) → Prop} {P Q : State → Prop} {x : State}
    (h : Safely trans P x) (hk : ∀ y, P y → Safely trans Q y) : Safely trans Q x := by
  obtain ⟨Inv, hx, hInv⟩ := h
  refine ⟨fun z => Inv z ∨ Safely trans Q z, .inl hx, ?_⟩
  rintro z (hz | hz)
  · rcases hInv z hz with hp | ⟨R, hT, hR⟩
    · rcases (hk z hp).unfold with hq | ⟨R, hT, hR⟩
      · exact .inl hq
      · exact .inr ⟨R, hT, fun w hw => .inr (hR w hw)⟩
    · exact .inr ⟨R, hT, fun w hw => .inl (hR w hw)⟩
  · rcases hz.unfold with hq | ⟨R, hT, hR⟩
    · exact .inl hq
    · exact .inr ⟨R, hT, fun w hw => .inr (hR w hw)⟩

/-- **Placement of a concatenation**: `q ++ p` at `pc` is `q` at `pc` and `p`
behind it. -/
theorem _root_.Kraken.Executable.sits_append (e : Kraken.Executable Directive) :
    ∀ (q p : Program) (pc : Int64), e.sits pc (q ++ p) →
      e.sits pc q ∧ e.sits (e.after pc q) p ∧ e.after pc (q ++ p) = e.after (e.after pc q) p
  | [], _, _, h => ⟨trivial, h, rfl⟩
  | .label _ :: q, p, pc, h => Executable.sits_append e q p pc h
  | .instr i :: q, p, pc, h => by
    obtain ⟨z, rest, hc, hs⟩ := h
    obtain ⟨h1, h2, h3⟩ := Executable.sits_append e q p _ hs
    refine ⟨⟨z, rest, hc, h1⟩, ?_, ?_⟩ <;> simp only [Executable.after, hc, List.cons_append, h2, h3]
  | .byteArray b :: q, p, pc, h => by
    obtain ⟨z, rest, hc, hs⟩ := h
    obtain ⟨h1, h2, h3⟩ := Executable.sits_append e q p _ hs
    refine ⟨⟨z, rest, hc, h1⟩, ?_, ?_⟩ <;> simp only [Executable.after, hc, List.cons_append, h2, h3]

namespace MachineWP

variable [CodeEnv] {env : SharedEnv}

/-- **The partial wp** of the fragment `q` at `(s, g)`: placed anywhere, every
run falls through with `Q`, exits with `E`, or runs forever. -/
def PartialWpEnv (env : SharedEnv) (q : Program) (Q : MachineData → env.State → Prop)
    (E : Int64 → MachineData → env.State → Prop) (s : MachineData) (g : env.State) : Prop :=
  ∀ pc, cenv.sits pc q →
    Safely (cenv.instrStepEnv env) (fun x => (x.1.2 = cenv.after pc q ∧ Q x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2)
      ((s, pc), g)

theorem PartialWpEnv.nil {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    {s : MachineData} {g : env.State} (h : Q s g) : PartialWpEnv env [] Q E s g :=
  fun _ _ => Safely.fold (.inl (.inl ⟨rfl, h⟩))

/-- **A total prefix, then a partial rest**: the prefix's `wpEnv` with the
rest's `PartialWpEnv` as its fall-through postcondition. -/
theorem PartialWpEnv.of_wpEnv {q p : Program} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} {s : MachineData} {g : env.State}
    (h : cenv.wpEnv env q (PartialWpEnv env p Q E) E s g) : PartialWpEnv env (q ++ p) Q E s g := by
  intro pc hpl
  obtain ⟨h1, h2, h3⟩ := Executable.sits_append cenv q p pc hpl
  refine Safely.of_eventually_safely (h pc h1) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨ha, hk⟩ | he)
  · dsimp only at ha hk
    subst ha
    rw [h3]
    exact hk _ h2
  · exact Safely.fold (.inl (.inr he))

/-- **A function's partial specification** at its entry address: `Pre`
reads the return address `ra` and the entry state (`X30 = ra` set by the
caller's `bl`); every run returns to `ra` with `Post` or runs forever. -/
def FunSpecPartialEnv (env : SharedEnv) (entry : Int64) (Pre : Int64 → MachineData → env.State → Prop)
    (Post : Int64 → MachineData → env.State → MachineData → env.State → Prop) : Prop :=
  ∀ ra t g, Pre ra t g →
    Safely (cenv.instrStepEnv env) (fun x => x.1.2 = ra ∧ Post ra t g x.1.1 x.2) ((t, entry), g)

/-- **The partial call rule**: `bl l` through the callee's `FunSpecPartialEnv` at the
label's address; the callee's return continues with the rest of the caller. -/
theorem PartialWpEnv.call {l : Label} {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (hf : FunSpecPartialEnv env ((_root_.Executable.labels cenv).label l) Pre Post) {p : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop}
    {s : MachineData} {g : env.State}
    (h : ∀ ra, Pre ra (s.setLr ra) g ∧ ∀ s' g', Post ra (s.setLr ra) g s' g' → PartialWpEnv env p Q E s' g') :
    PartialWpEnv env (Directive.instr ⟨.W64, .BL (.label l)⟩ :: p) Q E s g := by
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  have hafter : cenv.after pc (Directive.instr ⟨.W64, .BL (.label l)⟩ :: p) = cenv.after (pc + .ofNat z) p := by
    simp only [Executable.after, hseg]
  refine Safely.fold (.inr ⟨_, ⟨_, _, _, hseg, Or.inr ?_⟩, fun _ h => h⟩)
  rw [bl_cellEnv]
  obtain ⟨hpre, hk⟩ := h (pc + .ofNat z)
  refine Safely.bind (hf _ _ _ hpre) ?_
  rintro ⟨⟨s', a⟩, g'⟩ ⟨rfl, hpost⟩
  rw [hafter]
  exact hk s' g' hpost _ hpl'

/-- **The control-flow rule for a function fragment**, partial correctness:
`cfgEnv_partial_at` where each block may also exit by `E` (a `ret`, whose
target is a register), and the last block never falls through. The
conclusion is the run from the entry label's address into `E`. -/
theorem cfgEnv_partial_fun {p p' : Program} {E : Int64 → MachineData → env.State → Prop} {l₀ : Label}
    (T : Label → MachineData → env.State → Prop)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ (s₀ : MachineData) (g₀ : env.State),
      ⦃ fun s g => T l s g ∧ s = s₀ ∧ g = g₀ ⦄ (⟨blk.body⟩ : EnvProgram env)
      ⦃ (match blk.next with
         | some l' => fun _ s g => T l' s g
         | none => fun _ _ _ => False);
        fun a s g => Table.ofLabelsEnv (fun l' s g => (Program.blockAt p l').isSome ∧ T l' s g
          ∧ Program.EdgeSafe p l s₀ g₀ l' s g) a s g ∨ E a s g ⦄)
    (hp : p = Directive.label l₀ :: p') (hwf : Program.WF p) (hpl : Program.PlacedIn p) :
    ∀ s g, T l₀ s g → Safely (cenv.instrStepEnv env) (fun x => E x.1.2 x.1.1 x.2)
      ((s, (_root_.Executable.labels cenv).label l₀), g) := by
  have hnd := hwf.nodup
  intro s g hT
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length := Program.blockIdx_le p
  let μ : Label → Nat := fun l => (Program.view p).2.length - Program.blockIdx p l
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
          exact hq.elim
      · rintro a s' g' (⟨l', hlab, hsome', hTl', hedge⟩ | he)
        · refine Or.inr ⟨l', hlab, ⟨hsome', hTl'⟩, ?_⟩
          rcases hedge with hlt | hne
          · have hle' : Program.blockIdx p l' ≤ (Program.view p).2.length := hK l'
            refine .inl ?_
            simp only [μ]
            omega
          · exact .inr fun ⟨_, h1, h2⟩ => hne ⟨h1, h2⟩
        · exact Or.inl he

end MachineWP
