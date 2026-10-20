/-
**A program inside a larger image: placement, the control-flow rule, the
halt**. Additive companion of `Kraken/EnvCfg.lean` and
`Kraken/MachineWP.lean`'s placement section.

A `.kl` program's thread runs in the runner's executable: the code, then one
`.label sym` cell per data symbol, each behind a padding `.byteArray`
(`Kraken.Litmus.X64.prepareProgram`). The data labels are what absolute
operands `(sym)` resolve through (`Kraken/EnvVCGenAbs.lean`). The thread starts
at its entry label and halts at its exit label. So the code `p` is proved in
the ambient code `layout (p ++ t)` (the *image*, `t` the data trailer), not in
`layout p`:

- `Program.subBlocksOfE`, `Program.PlacedIn.of_placedE`: the blocks of `p`
  are placed in the image (as `Program.PlacedIn.of_placed`, also allowing an
  empty last block, such as the exit label `done:`, whose image block runs on
  into the trailer);
- `MachineWP.cfgEnv_partial_at`: `cfgEnv_partial` from a `PlacedIn` fragment,
  read at its entry label, with the end address of its last block named
  (`hlast`) instead of `Program.Placed`'s `entry`/`last`;
- `not_instrStepEnv_of_byteArray`: at the address of a `.byteArray` cell no
  instruction steps (the cell is data: `Directive.interp` is `unimplemented`),
  the `hstuck` of a thread halting at a label in front of the trailer.
-/
import Kraken.EnvCfg

open Kraken
open Std.WP

/-! ## Placement of a fragment in an image -/

/-- The blocks of `p` are among those of `q` (`Program.subBlocksOf`), or empty
and last. Decidable. -/
def Program.subBlocksOfE (p q : Program) : Bool :=
  (Program.view p).2.all fun lb =>
    match Program.blockAt p lb.1 with
    | none => false
    | some blk => (blk.body.isEmpty && blk.next.isNone) ||
      match Program.blockAt q lb.1 with
      | some blk' => decide (blk'.body = blk.body) && (blk.next.isNone || decide (blk'.next = blk.next))
      | none => false

/-- A fragment whose blocks are among a placed text's, up to empty last
blocks, is placed (`Program.PlacedIn.of_placed`). -/
theorem Program.PlacedIn.of_placedE [CodeEnv] {p q : Program} {m₀ : Label}
    (hq : Program.Placed q m₀) (h : Program.subBlocksOfE p q = true) : Program.PlacedIn p := by
  have key : ∀ l blk, Program.blockAt p l = some blk →
      (blk.body = [] ∧ blk.next = none) ∨
      ∃ blk', Program.blockAt q l = some blk' ∧ blk'.body = blk.body
        ∧ (blk.next.isNone = true ∨ blk'.next = blk.next) := by
    intro l blk hb
    have hmem : l ∈ (Program.view p).2.map (·.1) := by
      rw [← Program.labels_view]
      exact Program.blockAt_mem_labels hb
    obtain ⟨lb, hlb, rfl⟩ := List.mem_map.mp hmem
    have hall := List.all_eq_true.mp h lb hlb
    simp only [hb] at hall
    rcases Bool.or_eq_true_iff.mp hall with he | hall
    · left
      simp only [Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at he
      exact he
    · right
      cases hb' : Program.blockAt q lb.1 with
      | none => rw [hb'] at hall; cases hall
      | some blk' =>
        rw [hb'] at hall
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hall
        exact ⟨blk', rfl, hall.1, hall.2⟩
  refine ⟨?_, ?_⟩
  · intro l blk hb
    rcases key l blk hb with ⟨he, -⟩ | ⟨blk', hb', hbody, -⟩
    · rw [he]; trivial
    · rw [← hbody]
      exact hq.block l blk' hb'
  · intro l blk l' hb hn
    rcases key l blk hb with ⟨-, he⟩ | ⟨blk', hb', hbody, hnext⟩
    · rw [hn] at he; cases he
    · rw [hn] at hnext
      simp only [Option.isNone_some, Bool.false_eq_true, false_or] at hnext
      rw [← hbody]
      exact hq.next l blk' l' hb' hnext

/-! ## The control-flow rule at the entry label of a placed fragment -/

/-- The entry label has a block (a copy of `EnvCfg.lean`'s private
`blockAt_entry`). -/
theorem Program.blockAt_entry' {p p' : Program} {l₀ : Label} (hp : p = Directive.label l₀ :: p') :
    (Program.blockAt p l₀).isSome := by
  rw [hp]
  show (Program.blockAtAux (Program.view (Directive.label l₀ :: p')).2 l₀).isSome = true
  simp [Program.view, Program.blockAtAux]

open MachineWP in
/-- **The control-flow rule with the environment, partial correctness, at the
entry label of a placed fragment** (`cfgEnv_partial` for a fragment that is
only `PlacedIn` the ambient code). The block obligations are those of
`cfgEnv_partial`; the conclusion is the run from the entry label's address,
which ends at `endA`, the address behind the last block (`hlast`). -/
theorem MachineWP.cfgEnv_partial_at [CodeEnv] {env : SharedEnv} {p p' : Program}
    {Q : MachineData → env.State → Prop} {E : Int64 → MachineData → env.State → Prop} {l₀ : Label}
    {endA : Int64}
    (T : Label → MachineData → env.State → Prop)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ (s₀ : MachineData) (g₀ : env.State),
      ⦃ fun s g => T l s g ∧ s = s₀ ∧ g = g₀ ⦄ (⟨blk.body⟩ : EnvProgram env)
      ⦃ (match blk.next with
         | some l' => fun _ s g => T l' s g
         | none => fun _ => Q);
        Table.ofLabelsEnv (fun l' s g => (Program.blockAt p l').isSome ∧ T l' s g
          ∧ Program.EdgeSafe p l s₀ g₀ l' s g) ⦄)
    (hp : p = Directive.label l₀ :: p') (hwf : Program.WF p) (hpl : Program.PlacedIn p)
    (hlast : ∀ l blk, Program.blockAt p l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, T l₀ s g → Safely (cenv.instrStepEnv env)
      (fun x => (x.1.2 = endA ∧ Q x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2)
      ((s, (_root_.Executable.labels cenv).label l₀), g) := by
  have hnd := hwf.nodup
  intro s g hT
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length := Program.blockIdx_le p
  let μ : Label → Nat := fun l => (Program.view p).2.length - Program.blockIdx p l
  have key := Program.linkEnv_partial (env := env)
    (post := fun x => x.1.2 = endA ∧ Q x.1.1 x.2)
    (fun l => (Program.blockAt p l).elim [] (·.body))
    (fun l => (_root_.Executable.labels cenv).label l)
    (fun l s g => (Program.blockAt p l).isSome ∧ T l s g)
    (fun j i => μ j < μ i) (measure μ).wf ?_ ?_
  · exact (key l₀ s g ⟨Program.blockAt_entry' hp, hT⟩).mono fun st hst => Or.inl hst
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
          exact Or.inl ⟨hlast l blk hb hnx, hq⟩
      · rintro a s' g' ⟨l', hlab, hsome', hTl', hedge⟩
        refine Or.inr ⟨l', hlab, ⟨hsome', hTl'⟩, ?_⟩
        rcases hedge with hlt | hne
        · have hle' : Program.blockIdx p l' ≤ (Program.view p).2.length := hK l'
          refine .inl ?_
          simp only [μ]
          omega
        · exact .inr fun ⟨_, h1, h2⟩ => hne ⟨h1, h2⟩

/-- **The end of a fragment's last block is its exit label `x`** (the
`hlast` of `MachineWP.cfgEnv_partial_at`), in any code environment, from a
decidable check on `p` alone (`by decide`): every block of `p` without a
successor is the empty block `x:`. (The per-fragment `*_last`
lemmas are its instances.) -/
theorem Program.after_last_of [CodeEnv] {p : Program} {x : Label}
    (h : ∀ l ∈ Program.labels p, (Program.blockAt p l).map (·.next) = some none →
      l = x ∧ (Program.blockAt p l).map (·.body) = some []) :
    ∀ l blk, Program.blockAt p l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body =
        (_root_.Executable.labels cenv).label x := by
  intro l blk hb hn
  obtain ⟨rfl, hd⟩ := h l (Program.blockAt_mem_labels hb) (by rw [hb]; simp [hn])
  rw [hb] at hd
  simp only [Option.map_some, Option.some.injEq] at hd
  rw [hd]; rfl

/-- **A run in `SharedEnv.counted env` is a run in `env`**, the counter
existentially forgotten in the postcondition (the `Safely` form of
`MachineWP.PartialTripleEnv.uncount`). (The x64 absolute-operand
proofs' `Safely.uncountV`/`T`/`M`/`S`/`R` are its instances.) -/
theorem Safely.uncountEnv {e : Kraken.Executable Directive} {env : SharedEnv}
    {post : MachineState × (SharedEnv.counted env).State → Prop} {x : MachineState}
    {g : (SharedEnv.counted env).State} (h : Safely (e.instrStepEnv (SharedEnv.counted env)) post (x, g)) :
    Safely (e.instrStepEnv env) (fun y => ∃ n : Nat, post (y.1, (y.2, n))) (x, g.1) := by
  have hs := h.sim
    (fun (x : MachineState × (SharedEnv.counted env).State) (y : MachineState × env.State) =>
      y = (x.1, x.2.1))
    (fun x y R hxy hT => hxy ▸ Executable.instrStepEnv_uncount hT) rfl
  refine hs.mono ?_
  rintro y ⟨x', rfl, hx⟩
  exact ⟨x'.2.2, hx⟩

/-! ## The halt in front of a data cell -/

/-- **No instruction steps at a `.byteArray` cell**: its interpretation is
`unimplemented`, which no environment judgment admits. -/
theorem not_instrStepEnv_of_byteArray [layout : _root_.Layout] {q : Program}
    [Executable.ValidLayout (layout q)] {i : Nat} {b : ByteArray} (env : SharedEnv)
    (hq : q[i]? = some (.byteArray b)) :
    ∀ x R, x.1.2 = (layout q).addrOf i → ¬ (layout q).instrStepEnv env x R := by
  rintro x R hx ⟨d, z, rest, hcode, hstep⟩
  rw [hx, Executable.codeAt_addrOf (by rfl) hq] at hcode
  simp only [List.cons.injEq, Prod.mk.injEq] at hcode
  obtain ⟨⟨rfl, -⟩, -⟩ := hcode
  rcases hstep with h | h <;> simp [Directive.interp, Effects.AllEnv] at h
