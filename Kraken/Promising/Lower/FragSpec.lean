/-
**Placement-independent fragment specifications,
AArch64.** Generic (no pilot-specific names).

A lowered function body is one fragment, the same instructions wherever it is
placed, so one spec per fragment suffices.
The pilots proved their `FunSpecPartialEnv` facts (`AArch64/EnvCallsPartial.lean`)
at a fixed program's layout (`<prog>_placed`), so a second program containing
the same fragment re-proved the spec. Here the spec is proved once, for every
ambient code that places the fragment, and transported:

- `FragSpecEnv env frag l Pre Post`: for every `CodeEnv` in which `frag` is
  `Program.PlacedIn`, the `FunSpecPartialEnv` holds at `l`'s address. `Pre` and
  `Post` read the return address `ra` (and, through the state, the entry), so
  they are relative to the label and do not mention the placement.
- `FragSpecEnv.at` (from a `PlacedIn`), `FragSpecEnv.of_placed` (from an
  image's `Program.Placed` and the decidable `Program.subBlocksOfE`), and
  `FragSpecEnv.of_layout` (from a laid-out program `layout q`; the client cost
  is one line per function per program).
- `FragSpecEnv.of_cfg`: the constructor; it runs `cfgEnv_partial_fun` once with
  the placement abstract. The block obligations quantify over the `CodeEnv`;
  `cfg_cases_env` and `vcgen` never inspect the ambient code (only the
  fragment's own blocks, by `decide`), so a pilot's proof goes through verbatim.
- `FragSpecEnv.mono`: weakening of the pre/post.

Machine: the executable machine's per-thread environment semantics
(`Executable.instrStepEnv`), partial correctness (`Safely`), as
`FunSpecPartialEnv`. Purity twins (`relPure` environments) are the same notion
at a different `env`: nothing extra is needed.
-/
import Kraken.AArch64.EnvCallsPartial

open Kraken
open Std.WP

namespace MachineWP

variable {env : SharedEnv}

/-- **A placement-independent function specification**: in every ambient code
that places the blocks of `frag`, the function entered at `l`'s address
satisfies `FunSpecPartialEnv env _ Pre Post` (every run from a `Pre` state
returns to `ra` with `Post`, or runs forever). -/
structure FragSpecEnv (env : SharedEnv) (frag : Program) (l : Label) (Pre : Int64 → MachineData → env.State → Prop)
    (Post : Int64 → MachineData → env.State → MachineData → env.State → Prop) : Prop where
  /-- The specification in an ambient code that places `frag`. (A structure,
  not a `def`: the elaborator would otherwise unfold the `∀ [CodeEnv]` and
  consume the binder, breaking dot notation.) -/
  spec : ∀ [CodeEnv], Program.PlacedIn frag → FunSpecPartialEnv env ((_root_.Executable.labels cenv).label l) Pre Post

/-- **Transport** to an ambient code that places the fragment. -/
theorem FragSpecEnv.at [CodeEnv] {frag : Program} {l : Label} {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnv env frag l Pre Post) (hpl : Program.PlacedIn frag) :
    FunSpecPartialEnv env ((_root_.Executable.labels cenv).label l) Pre Post :=
  h.spec hpl

/-- **Transport into an image**: `frag`'s blocks among a placed text's
(`Program.subBlocksOfE`, decidable: `by decide` for closed texts). -/
theorem FragSpecEnv.of_placed [CodeEnv] {frag q : Program} {l m₀ : Label}
    {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnv env frag l Pre Post) (hq : Program.Placed q m₀) (hs : Program.subBlocksOfE frag q = true) :
    FunSpecPartialEnv env ((_root_.Executable.labels cenv).label l) Pre Post :=
  h.spec (Program.PlacedIn.of_placedE hq hs)

/-- **Transport into a laid-out program** `layout q` (the code of the pilots'
`local instance … : CodeEnv := ⟨layout q⟩`): `q` well formed, starting with
its entry label, not only labels, and holding `frag`'s blocks. All four side
conditions are `by decide` / `rfl` for closed texts. -/
theorem FragSpecEnv.of_layout [layout : _root_.Layout] {frag q q' : Program} [Executable.ValidLayout (layout q)]
    {l m₀ : Label} {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnv env frag l Pre Post) (hwf : Program.WF q) (hq : q = Directive.label m₀ :: q')
    (hne : q.any (fun d => !d.isLabel) = true) (hs : Program.subBlocksOfE frag q = true) :
    @FunSpecPartialEnv ⟨layout q⟩ env ((_root_.Executable.labels (layout q)).label l) Pre Post :=
  @FragSpecEnv.of_placed env ⟨layout q⟩ frag q l m₀ Pre Post h (Program.placed_of_layout hwf hq hne) hs

/-- **Weakening**: a stronger precondition, a weaker postcondition. -/
theorem FragSpecEnv.mono {frag : Program} {l : Label} {Pre Pre' : Int64 → MachineData → env.State → Prop}
    {Post Post' : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (h : FragSpecEnv env frag l Pre Post) (hpre : ∀ ra t g, Pre' ra t g → Pre ra t g)
    (hpost : ∀ ra t g t' g', Pre' ra t g → Post ra t g t' g' → Post' ra t g t' g') :
    FragSpecEnv env frag l Pre' Post' := by
  refine ⟨fun hpl ra t g hp => ?_⟩
  exact (h.spec hpl ra t g (hpre ra t g hp)).mono fun x ⟨hra, hq⟩ => ⟨hra, hpost ra t g _ _ hp hq⟩

/-- **The constructor**: `cfgEnv_partial_fun` once, with the placement
abstract. `T ra t g` is the loop table of the run entered with return address
`ra` from `(t, g)`; it holds at the entry label; every block, in every ambient
code, keeps the table, or exits to `ra` with `Post` (the `ret`). -/
theorem FragSpecEnv.of_cfg {frag p' : Program} {l₀ : Label} {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (T : Int64 → MachineData → env.State → Label → MachineData → env.State → Prop)
    (hp : frag = Directive.label l₀ :: p') (hwf : Program.WF frag)
    (hinit : ∀ ra t g, Pre ra t g → T ra t g l₀ t g)
    (hblocks : ∀ [CodeEnv] (ra : Int64) (t : MachineData) (g : env.State), Pre ra t g →
      ∀ l blk, Program.blockAt frag l = some blk → ∀ (s₀ : MachineData) (g₀ : env.State),
      ⦃ fun s g' => T ra t g l s g' ∧ s = s₀ ∧ g' = g₀ ⦄ (⟨blk.body⟩ : EnvProgram env)
      ⦃ (match blk.next with
         | some l' => fun _ s g' => T ra t g l' s g'
         | none => fun _ _ _ => False);
        fun a s g' => Table.ofLabelsEnv (fun l' s g' => (Program.blockAt frag l').isSome ∧ T ra t g l' s g'
          ∧ Program.EdgeSafe frag l s₀ g₀ l' s g') a s g' ∨ (a = ra ∧ Post ra t g s g') ⦄) :
    FragSpecEnv env frag l₀ Pre Post := by
  refine ⟨fun hpl ra t g hpre => ?_⟩
  exact cfgEnv_partial_fun (T ra t g) (E := fun a s g' => a = ra ∧ Post ra t g s g')
    (hblocks ra t g hpre) hp hwf hpl t g (hinit ra t g hpre)

end MachineWP
